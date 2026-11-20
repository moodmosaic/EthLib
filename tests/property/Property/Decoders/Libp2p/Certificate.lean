import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Networking.Libp2p.Tls

/-!
# The certificate of libp2p TLS

A description of a certificate is generated here, and the oracle builds its DER and signs it.

The oracle then reads the bytes back, as RFC 5280 and the libp2p TLS text say, and gives the facts.

EthLib must read what the facts say is a certificate, and authenticate what they say is a peer.

The dates come from every class: both time forms, the pivot of 1950, leap years, month ends.
-/

open Hedgehog Support EthLib EthLib.Networking EthLib.Networking.Libp2p

namespace DecodersProperty.Libp2p.Certificate

open DecodersProperty

/-- The name of the constructor of an error, from its `Repr`. -/
def constructor {ε : Type} [Repr ε] (e : ε) : String :=
  let text := (toString (repr e)).takeWhile fun c => !c.isWhitespace && c != '('
  (text.toString.splitOn ".").getLastD ""

/-! ## Times -/

/-- A date and a time of day, which need not exist. -/
structure Moment where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  deriving Repr

/-- A number in decimal digits, at a width, with leading zeros. -/
def digits (width n : Nat) : String :=
  let text := toString (n % 10 ^ width)
  String.ofList (List.replicate (width - text.length) '0') ++ text

/-- The years where a calendar rule or a time form changes. -/
def edgeYears : List Nat :=
  [1, 4, 100, 400, 1582, 1600, 1700, 1899, 1900, 1901, 1904, 1949, 1950, 1951, 1968, 1969, 1970,
    1971, 1972, 1999, 2000, 2001, 2004, 2037, 2038, 2049, 2050, 2051, 2099, 2100, 2101, 2200,
    2400, 9996, 9999]

/-- The years whose February decides the leap rule: every fourth, a century, a fourth century. -/
def februaryYears : List Nat :=
  [4, 100, 400, 1600, 1700, 1900, 1904, 1952, 1972, 1996, 2000, 2024, 2048, 2052, 2100, 2400,
    9996, 1951, 2023, 2049]

/-- A moment: any year from 1 to 9999, the last days of a month, and a few values past a field. -/
def genMoment : Gen Moment := do
  let year ← Gen.frequency [(4, Gen.element edgeYears), (3, Gen.nat (.constant 1950 2049)),
    (2, Gen.nat (.constant 1 9999)), (1, Gen.nat (.constant 1 1949))]
  let month ← Gen.frequency [(30, Gen.nat (.constant 1 12)), (1, Gen.element [0, 13])]
  let day ← Gen.frequency [(14, Gen.nat (.constant 1 28)), (14, Gen.element [28, 29, 30, 31]),
    (1, Gen.element [0, 32])]
  let hour ← Gen.frequency [(20, Gen.nat (.constant 0 23)), (9, Gen.element [0, 23]),
    (1, pure 24)]
  let minute ← Gen.frequency [(20, Gen.nat (.constant 0 59)), (9, Gen.element [0, 59]),
    (1, pure 60)]
  let second ← Gen.frequency [(20, Gen.nat (.constant 0 59)), (9, Gen.element [0, 59]),
    (1, pure 60)]
  -- The end of February, in the years that decide the leap rule.
  let february ← Gen.frequency [(5, pure none),
    (1, some <$> Gen.zip (Gen.element februaryYears) (Gen.element [28, 29, 29, 30]))]
  pure (match february with
    | some (year, day) => ⟨year, 2, day, hour, minute, second⟩
    | none => ⟨year, month, day, hour, minute, second⟩)

/-- A time as a certificate holds it: the tag of its form, and its text. -/
structure TimeField where
  tag : Nat
  text : String
  moment : Moment
  /-- Whether the text has the form of its tag. -/
  wellFormed : Bool
  deriving Repr

/-- The text of a moment, with a year of two digits or of four. -/
def Moment.text (m : Moment) (generalized : Bool) : String :=
  (if generalized then digits 4 m.year else digits 2 m.year) ++ digits 2 m.month ++
    digits 2 m.day ++ digits 2 m.hour ++ digits 2 m.minute ++ digits 2 m.second ++ "Z"

/-- A time field: the form that RFC 5280 asks for its year, the other one, and broken texts. -/
def genTime : Gen TimeField := do
  let moment ← genMoment
  let usual := moment.year < 1950 || 2049 < moment.year
  let generalized ← Gen.frequency [(8, pure usual), (2, pure true), (1, pure false)]
  let text := moment.text generalized
  let broken ← Gen.frequency [(16, pure none), (1, some <$> Gen.element [
    text.dropEnd 1 |>.toString, (text.dropEnd 1).toString ++ "z",
    (text.dropEnd 3).toString ++ "Z", (text.dropEnd 1).toString ++ "+0000",
    (text.dropEnd 1).toString ++ ".5Z", "x" ++ (text.drop 1).toString, "0" ++ text, "",
    (text.dropEnd 1).toString ++ "-0100", (text.take 4).toString ++ " " ++
      (text.drop 5).toString])]
  let tag ← Gen.frequency [(30, pure (if generalized then 0x18 else 0x17)),
    (1, pure (if generalized then 0x17 else 0x18)), (1, Gen.element [0x16, 0x13, 0x0c])]
  let proper := if generalized then 0x18 else 0x17
  pure ⟨tag, broken.getD text, moment, broken.isNone && tag = proper⟩

/-- A time field in the word of the oracle: the tag, then the text. -/
def TimeField.word (t : TimeField) : String :=
  s!"{String.ofList (Nat.toDigits 16 t.tag)}:{hex t.text.toUTF8}"

/-- The days of a month, by the Gregorian rule, for the labels only. -/
def daysIn (year month : Nat) : Nat :=
  if month = 2 then
    if year % 4 = 0 ∧ (year % 100 ≠ 0 ∨ year % 400 = 0) then 29 else 28
  else if month ∈ [4, 6, 9, 11] then 30 else 31

/-- The class of a time field, for the labels. -/
def TimeField.classes (t : TimeField) : List String :=
  let m := t.moment
  let year := if t.tag = 0x17 then (if m.year % 100 < 50 then 2000 else 1900) + m.year % 100
    else m.year
  (if !t.wellFormed then ["a text of another form"] else
    (if t.tag = 0x17 then
      [if year < 2000 then "UTCTime, 1950 to 1999" else "UTCTime, 2000 to 2049"]
    else [if year < 1950 then "GeneralizedTime, before 1950"
      else if year < 2050 then "GeneralizedTime, 1950 to 2049"
      else "GeneralizedTime, from 2050"]) ++
    (if year < 1970 then ["before 1970"] else []) ++
    (if m.month = 2 ∧ m.day = 29 then
      [if daysIn year 2 = 29 then "29 February of a leap year"
        else "29 February of another year"] else []) ++
    (if 1 ≤ m.month ∧ m.month ≤ 12 ∧ m.day = daysIn year m.month then
      ["the last day of a month"] else []) ++
    (if 1 ≤ m.month ∧ m.month ≤ 12 ∧ daysIn year m.month < m.day ∧ m.day ≤ 31 then
      ["a day past the end of its month"] else []) ++
    (if year % 100 = 0 then ["a year of a century"] else []))

/-- A time field is read as the calendar gives it, in seconds from 1970, or refused.

The reference is Python's `datetime` under the two forms of RFC 5280 section 4.1.2.5. -/
def time (oracle : Oracle) : Property IO := propertyM do
  let field ← forAll genTime
  pure do
    let reference ← oracle.ask ["x509_time", String.ofList (Nat.toDigits 16 field.tag),
      hex field.text.toUTF8]
    let value : Serialization.Der.Value := ⟨UInt8.ofNat field.tag, field.text.toUTF8, .empty⟩
    match Tls.readTime value with
    | .ok seconds => toString seconds === reference
    | .error e => ensure (refused reference) s!"EthLib refuses ({repr e}), the reference reads"
    cover 40 "read" !(refused reference)
    cover 10 "refused" (refused reference)
    for name in field.classes do
      label name
    let has (name : String) := field.classes.contains name
    cover 5 "UTCTime, 1950 to 1999, read" (has "UTCTime, 1950 to 1999" && !refused reference)
    cover 5 "UTCTime, 2000 to 2049, read" (has "UTCTime, 2000 to 2049" && !refused reference)
    cover 5 "GeneralizedTime, before 1950, read"
      (has "GeneralizedTime, before 1950" && !refused reference)
    cover 5 "GeneralizedTime, from 2050, read"
      (has "GeneralizedTime, from 2050" && !refused reference)
    cover 1 "29 February of a leap year, read"
      (has "29 February of a leap year" && !refused reference)
    cover 1 "29 February of another year, refused"
      (has "29 February of another year" && refused reference)
    cover 5 "the last day of a month, read" (has "the last day of a month" && !refused reference)
    cover 2 "a day past the end of its month, refused"
      (has "a day past the end of its month" && refused reference)
    cover 3 "a year of a century, read" (has "a year of a century" && !refused reference)

/-! ## Certificates -/

/-- The description of a certificate, in the words of the oracle. -/
structure Spec where
  certKey : String
  sigalg : String
  sig : String
  version : String
  serial : String
  issuer : String
  subject : String
  notBefore : TimeField
  notAfter : TimeField
  spki : String
  uids : String
  exts : String
  hostKey : String
  hostVariant : String
  tbsFlip : String
  deriving Repr

/-- The words of a description, in the order of `cert_build`. -/
def Spec.words (s : Spec) : List String :=
  [s.certKey, s.sigalg, s.sig, s.version, s.serial, s.issuer, s.subject, s.notBefore.word,
    s.notAfter.word, s.spki, s.uids, s.exts, s.hostKey, s.hostVariant, s.tbsFlip]

/-- A moment as a number that orders it. -/
def Moment.order (m : Moment) : Nat :=
  ((((m.year * 100 + m.month) * 100 + m.day) * 100 + m.hour) * 100 + m.minute) * 100 + m.second

/-- A moment that exists, so that a certificate is not refused for its dates. -/
def genSoundTime : Gen TimeField := do
  let year ← Gen.frequency [(2, Gen.element edgeYears), (4, Gen.nat (.constant 1970 2049)),
    (2, Gen.nat (.constant 2050 9999)), (1, Gen.nat (.constant 1 9999))]
  let month ← Gen.nat (.constant 1 12)
  let day ← Gen.frequency [(3, Gen.nat (.constant 1 28)), (1, pure (daysIn year month))]
  let hour ← Gen.element [0, 11, 23]
  let minute ← Gen.element [0, 30, 59]
  let second ← Gen.element [0, 1, 59]
  let moment : Moment := ⟨year, month, day, hour, minute, second⟩
  let generalized ← if year < 1950 || 2049 < year then pure true
    else Gen.frequency [(4, pure false), (1, pure true)]
  pure ⟨if generalized then 0x18 else 0x17, moment.text generalized, moment, true⟩

/-- The validity of a certificate: two moments in order, or reversed, or one that is broken. -/
def genValidity : Gen (TimeField × TimeField) := do
  let (a, b) ← Gen.zip genSoundTime genSoundTime
  let (first, last) := if a.moment.order ≤ b.moment.order then (a, b) else (b, a)
  let shape ← Gen.frequency [(16, pure 0), (1, pure 1), (1, pure 2), (1, pure 3)]
  let other ← genTime
  pure (match shape with
    | 0 => (first, last)
    | 1 => (last, first)
    | 2 => (other, last)
    | _ => (first, other))

/-- The names that a reader of RFC 5280 takes, and those it does not. -/
def soundNames : List String :=
  ["empty", "cn", "printable", "ia5", "bmp", "universal", "two", "multi", "lengths"]

/-- The names that break a rule, or use a string type outside EthLib's documented subset. -/
def brokenNames : List String :=
  ["unsorted", "unsortedlengths", "emptyset", "teletex", "numeric", "badprintable", "badutf8",
    "badbmp", "surrogate"]

/-- A description: a certificate that a peer must accept, with a fault or two in half of them.

`faults` lists the fields that take a value outside what the libp2p TLS text accepts. -/
def genSpec : Gen Spec := do
  -- The fields with many faulty values are picked more often.
  let field := Gen.frequency [(2, pure 0), (2, pure 1), (2, pure 2), (2, pure 3), (1, pure 4),
    (1, pure 5), (1, pure 6), (1, pure 7), (1, pure 8), (8, pure 9), (3, pure 10), (8, pure 11),
    (4, pure 12)]
  let faults ← Gen.frequency [(4, pure []), (6, Gen.list (.singleton 1) field),
    (1, Gen.list (.singleton 2) field)]
  let pick (index : Nat) (sound broken : List String) : Gen String :=
    Gen.element (if faults.contains index then broken else sound)
  let secret ← genBytesN 32
  let hostSecret ← genBytesN 32
  let certKind ← pick 0 ["p256"] ["k256", "p384", "ed25519"]
  let sigalg ← pick 1 ["sha256"] ["sha384", "null", "mismatch"]
  let sig ← pick 2 ["good", "good", "highs"] ["flip", "pad"]
  let version ← pick 3 ["2"] ["none", "0", "1", "3"]
  let serial ← pick 4 ["01", "00", "7f", "ff", "0080", "ff7f", "00ff", "8000",
    "7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f"] ["0001", "", "ffff", "ff80", "0000"]
  let issuer ← pick 5 soundNames brokenNames
  let subject ← pick 6 soundNames brokenNames
  let spki ← pick 7 ["good"] ["compressed"]
  let uids ← pick 8 ["-:-", "-:-", "-:-", "-:-", "-:-", "-:-", "-:-", "-:-", "-:-", "-:-",
    "00ab:-", "-:00cd", "00ab:00cd", "01fe:0780", "00:-"]
    ["03ff:-", ":-", "-:08ff", "01:-", "-:0101"]
  let exts ← pick 9 ["L", "L", "Lc", "L,O1", "O2,L", "KU,L", "L,O1,O2", "Lc,O3", "L,B127",
    "B128,L", "L,B255", "L,B256", "B65535,L", "L,B65536"]
    ["none", "none", "O1", "O1,O2", "KU", "empty", "L,O1c", "O1c,L", "L,KUc", "Lc,O1c", "L,L",
      "LF", "L,F", "L,X", "L,O1,O1"]
  -- A certificate without extensions may be of any version.
  let version ← if exts = "none" then Gen.element ["none", "1", "2"] else pure version
  let uids := if version = "none" then "-:-" else uids
  let hostKind ← pick 10 ["k256", "p256"] ["ed25519", "rsa", "p384"]
  let hostVariant ← pick 11 ["good"] ["badsig", "highs", "pad", "prefix", "otherspki",
    "swapped", "extrafield", "longvarint", "nodata", "seqextra", "bitstring", "trail",
    "compressed"]
  let flip ← Gen.zip (Gen.nat (.constant 0 999)) (Gen.element [1, 2, 4, 8, 16, 32, 64, 128])
  let tbsFlip := if faults.contains 12 then s!"{flip.1}:{flip.2}" else "-"
  let (notBefore, notAfter) ← genValidity
  pure { certKey := s!"{certKind}:{hex secret}", sigalg, sig, version, serial, issuer, subject,
         notBefore, notAfter, spki, uids, exts, hostKey := s!"{hostKind}:{hex hostSecret}",
         hostVariant, tbsFlip }

/-- When the certificate is checked, against its validity. -/
inductive Clock where
  | between
  | atStart
  | atEnd
  | beforeStart
  | afterEnd
  | zero
  | far
  deriving Repr, DecidableEq

/-- How many certificates the peer sends. -/
inductive Chain where
  | one
  | none
  | two
  deriving Repr, DecidableEq

/-- Which peer the dialer expects. -/
inductive Expected where
  | anyone
  | thisPeer
  | another
  deriving Repr, DecidableEq

/-- What the receiver of a certificate decides for itself. -/
structure Trial where
  hosts : List Tls.HostAlgorithm
  certificates : List Tls.CertificateAlgorithm
  rejectUniqueIds : Bool
  clock : Clock
  chain : Chain
  expected : Expected
  deriving Repr

/-- A receiver: most accept both host keys, and most look at a moment within the validity. -/
def genTrial : Gen Trial := do
  let hosts ← Gen.frequency [(20, pure [Tls.HostAlgorithm.secp256k1, .p256]),
    (1, pure [.secp256k1]), (1, pure [.p256]), (1, pure [])]
  let certificates ← Gen.frequency [(30, pure [Tls.CertificateAlgorithm.p256Sha256]),
    (1, pure [])]
  let rejectUniqueIds ← Gen.frequency [(1, pure true), (2, pure false)]
  let clock ← Gen.frequency [(18, pure Clock.between), (6, pure .atStart), (6, pure .atEnd),
    (2, pure .beforeStart), (2, pure .afterEnd), (1, pure .zero), (1, pure .far)]
  let chain ← Gen.frequency [(40, pure Chain.one), (1, pure .none), (1, pure .two)]
  let expected ← Gen.frequency [(5, pure Expected.anyone), (5, pure .thisPeer),
    (2, pure .another)]
  pure ⟨hosts, certificates, rejectUniqueIds, clock, chain, expected⟩

/-- The facts of the oracle: the value of a name, or the empty string. -/
def factOf (facts : List String) (name : String) : String :=
  (facts.findSome? fun word =>
    match word.splitOn "=" with
    | [key, value] => if key = name then some value else none
    | _ => none).getD ""

/-- Whether the references agree on the bytes; a disagreement is an answer that starts so. -/
def disagree (answer : String) : Bool := answer.startsWith "error the references disagree"

/-- EthLib reads and authenticates the bytes exactly as the facts of the reference say.

A certificate is read when RFC 5280 reads it and it is within EthLib's documented subset.

A peer is authenticated when every rule of "Peer Authentication" holds at the given moment.

A refusal must name a rule that the facts say is broken. -/
def check (der : ByteArray) (facts : List String) (t : Trial) (shares : Bool := true)
    (long : Bool := true) : TestT IO Unit := do
  -- A property that fixes the receiver asks for no share of what a receiver varies.
  --
  -- A share of one percent is asked of a long run only: a hundred cases may hold none.
  let cover (minimum : Nat) (name : String) (reached : Bool) : TestT IO Unit :=
    if !shares then pure ()
    else if minimum ≤ 1 then coverLong long minimum name reached
    else Hedgehog.cover minimum name reached
  let fact := factOf facts
  let subset := fact "subset"
  let parses := fact "rfc" == "ok" && subset != "value-tag" && subset != "validity-inverted"
  let notBefore := (fact "nb").toInt?.getD 0
  let notAfter := (fact "na").toInt?.getD 0
  annotate s!"the certificate: {hex der}"
  annotate s!"the facts: {" ".intercalate facts}"
  match Tls.readCertificate der with
  | .error e =>
    ensure (!parses) s!"EthLib refuses to read ({repr e}), the reference reads"
    label s!"not read: {if fact "rfc" == "ok" then subset else fact "rfc"}"
  | .ok certificate =>
    ensure parses "EthLib reads, the reference does not"
    certificate.notBefore === notBefore
    certificate.notAfter === notAfter
    (if certificate.issuerUniqueId then "1" else "0") ++
      (if certificate.subjectUniqueId then "1" else "0") === fact "uid"
  let now : Nat := match t.clock with
    | .between => ((notBefore + notAfter) / 2).toNat
    | .atStart => notBefore.toNat
    | .atEnd => notAfter.toNat
    | .beforeStart => (notBefore - 1).toNat
    | .afterEnd => (notAfter + 1).toNat
    | .zero => 0
    | .far => 2 ^ 40
  let inValidity := notBefore ≤ (now : Int) && (now : Int) ≤ notAfter
  let host := fact "host"
  let hostAllowed := (host == "k256" && t.hosts.contains .secp256k1) ||
    (host == "p256" && t.hosts.contains .p256)
  let uniqueIds := t.rejectUniqueIds && fact "uid" != "00"
  let authentic := t.chain == .one && parses && inValidity && !uniqueIds &&
    !t.certificates.isEmpty && fact "alg" == "1" && fact "selfsig" == "1" && subset == "-" &&
    fact "ext" == "ok" && hostAllowed && fact "canon" == "1" && fact "hostsig" == "1"
  let peer := (unhex? (fact "peer")).getD .empty
  let other := peer.push 1
  let accept := authentic && t.expected != .another
  let policy : Tls.Policy := ⟨t.hosts, t.certificates, t.rejectUniqueIds⟩
  let chain := match t.chain with
    | .one => [der]
    | .none => []
    | .two => [der, der]
  let result := match t.expected with
    | .anyone => Tls.authenticate policy now chain
    | .thisPeer => Tls.authenticatePeer policy now peer chain
    | .another => Tls.authenticatePeer policy now other chain
  annotate s!"now {now}"
  match result with
  | .ok found =>
    ensure accept "EthLib authenticates, the reference does not"
    hex found.peerId === fact "peer"
    label s!"authenticated: a host key of {host}"
  | .error e =>
    ensure (!accept) s!"EthLib refuses ({repr e}), the reference authenticates"
    -- The refusal names a rule that the facts say is broken.
    let explained := match e with
      | .chain _ => t.chain != .one
      | .der _ | .certificate => !parses || fact "ext" == "malformed" || host == "badkey"
      | .duplicateExtension _ => fact "rfc" == "extension-twice"
      | .validity .. => !inValidity
      | .uniqueId => uniqueIds
      | .algorithm => t.certificates.isEmpty || fact "alg" == "0" || !hostAllowed ||
          fact "rfc" == "algorithm-mismatch" || fact "canon" == "0"
      | .selfSignature => fact "selfsig" == "0" || fact "alg" == "0" ||
          subset == "compressed-point"
      | .missingExtension => fact "ext" == "missing"
      | .criticalExtension _ => fact "ext" == "critical"
      | .publicKey => host == "badkey" || fact "canon" == "0"
      | .hostSignature => fact "hostsig" == "0"
      | .peerId => t.expected == .another
    ensure explained s!"EthLib refuses with {repr e}, which the facts do not explain"
    label s!"refused: {constructor e}"
    for name in ["validity", "uniqueId", "algorithm", "selfSignature", "missingExtension",
        "criticalExtension", "publicKey", "hostSignature", "peerId", "chain"] do
      cover 1 s!"refused, and every rule before it holds: {name}" (constructor e == name)
  cover 6 "authenticated" result.isOk
  cover 10 "read and refused" (parses && !result.isOk)
  cover 10 "not read" !parses
  cover 1 "authenticated at the first second of the validity"
    (result.isOk && t.clock == .atStart)
  cover 1 "authenticated at the last second of the validity" (result.isOk && t.clock == .atEnd)
  cover 1 "refused one second before the validity"
    (!result.isOk && parses && t.clock == .beforeStart && !inValidity)
  cover 1 "refused one second after the validity"
    (!result.isOk && parses && t.clock == .afterEnd && !inValidity)

/-- A generated certificate is read and authenticated as RFC 5280 and libp2p TLS say. -/
def certificate (oracle : Oracle) (long : Bool := true) : Property IO := propertyM do
  let spec ← forAll genSpec
  let trial ← forAll genTrial
  pure do
    let answer ← oracle.ask ("cert_build" :: spec.words)
    let derWord :: facts := words answer | failWith "the oracle gave no certificate"
    let some der := unhex? derWord | failWith s!"the oracle failed: {answer}"
    if facts.head? == some "error" then
      -- The two references read the bytes differently, so neither is taken.
      annotate answer
      label "the references disagree"
      collect (" ".intercalate facts)
    else
      check der facts trial (long := long)

/-- A way to change the bytes of a signed certificate. -/
inductive Damage where
  | flip (position : Nat) (mask : UInt8)
  | drop (position : Nat)
  | insert (position : Nat) (byte : UInt8)
  | cut (position : Nat)
  | append (byte : UInt8)
  deriving Repr

/-- The bytes after a change; a position is in thousandths of the length. -/
def Damage.apply (d : Damage) (bytes : ByteArray) : ByteArray :=
  let list := bytes.data.toList
  let index (position : Nat) := position * (list.length - 1) / 1000
  packed (match d with
    | .flip position mask => list.set (index position) (list.getD (index position) 0 ^^^ mask)
    | .drop position => list.eraseIdx (index position)
    | .insert position byte => list.take (index position) ++ [byte] ++ list.drop (index position)
    | .cut position => list.take (index position)
    | .append byte => list ++ [byte])

/-- A certificate with no fault at all. -/
def genSoundSpec : Gen Spec := do
  let secret ← genBytesN 32
  let hostSecret ← genBytesN 32
  let hostKind ← Gen.element ["k256", "p256"]
  let (a, b) ← Gen.zip genSoundTime genSoundTime
  let (notBefore, notAfter) := if a.moment.order ≤ b.moment.order then (a, b) else (b, a)
  let issuer ← Gen.element soundNames
  let exts ← Gen.element ["L", "Lc", "L,O1", "KU,L"]
  pure { certKey := s!"p256:{hex secret}", sigalg := "sha256", sig := "good", version := "2",
         serial := "01", issuer, subject := "cn", notBefore, notAfter, spki := "good",
         uids := "-:-", exts, hostKey := s!"{hostKind}:{hex hostSecret}",
         hostVariant := "good", tbsFlip := "-" }

/-- A signed certificate with one byte changed is refused, unless the reference still takes it.

The signature covers every byte but its own, so a change must end in a refusal. -/
def damaged (oracle : Oracle) : Property IO := propertyM do
  let spec ← forAll genSoundSpec
  let damage ← forAll (Gen.frequency [
    (8, Damage.flip <$> Gen.nat (.constant 0 1000) <*>
      (UInt8.ofNat <$> Gen.element [1, 2, 4, 8, 16, 32, 64, 128, 255])),
    (1, Damage.drop <$> Gen.nat (.constant 0 1000)),
    (1, Damage.insert <$> Gen.nat (.constant 0 1000) <*> genByte),
    (1, Damage.cut <$> Gen.nat (.constant 0 1000)),
    (1, Damage.append <$> genByte)])
  let untouched ← forAll (Gen.frequency [(1, pure true), (6, pure false)])
  pure do
    let answer ← oracle.ask ("cert_build" :: spec.words)
    let derWord :: _ := words answer | failWith "the oracle gave no certificate"
    let some sound := unhex? derWord | failWith s!"the oracle failed: {answer}"
    let der := if untouched then sound else damage.apply sound
    let reply ← oracle.ask ["cert_facts", hex der]
    let trial : Trial := ⟨[.secp256k1, .p256], [.p256Sha256], false, .between, .one, .anyone⟩
    if disagree reply then
      -- Neither reference is taken, but the signature is broken, so EthLib must refuse.
      annotate reply
      label "the references disagree"
      collect (reply, hex der)
      ensure (!(Tls.authenticate ⟨trial.hosts, trial.certificates, false⟩ 0 [der]).isOk)
        "EthLib authenticates bytes that the references read differently"
    else
      check der (words reply) trial (shares := false)
    classify "untouched" untouched
    let policy : Tls.Policy := ⟨trial.hosts, trial.certificates, false⟩
    classify "changed and authenticated by EthLib"
      (!untouched && (Tls.authenticate policy 2147483648 [der]).isOk)
    classify "changed and still read by the reference"
      (!untouched && (words reply).head? == some "rfc=ok")
    classify "changed and not read by the reference"
      (!untouched && !disagree reply && (words reply).head? != some "rfc=ok")

/-- The properties of the certificate. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("libp2p-tls: a time is read as the calendar gives it", (time oracle).withTests (4 * cases)),
  ("libp2p-tls: a certificate is read and authenticated as the texts say",
    (certificate oracle (cases ≥ 1000)).withTests cases),
  ("libp2p-tls: a certificate with one byte changed", (damaged oracle).withTests cases)]

end DecodersProperty.Libp2p.Certificate

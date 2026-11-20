import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Networking.Quic.Tls
import EthLib.Networking.Quic.Tls.Crypto
import EthLib.Networking.Quic.Tls.Extensions
import EthLib.Networking.Quic.Tls.Handshake
import EthLib.Networking.Quic.Tls.Messages
import EthLib.Networking.Quic.Tls.Transcript

/-!
# The TLS 1.3 handshake as QUIC carries it, on generated inputs

A handshake message is built here field by field, with the text that a reader must give for it.

EthLib reads the bytes, and so does a reader written from RFC 8446 in the oracle.

The key schedule is compared with HMAC and the HKDF of `cryptography`.

The whole handshake runs against aioquic's TLS context, as dialer and as listener.
-/

open Hedgehog Support EthLib
open EthLib.Networking.Quic
open EthLib.Networking.Quic.Tls

namespace DecodersProperty.Tls

open DecodersProperty

/-! ## Bytes of the presentation language, built apart from EthLib -/

/-- A number in `n` bytes, big-endian. -/
def be (n v : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (v / 256 ^ (n - 1 - i))

/-- A vector: its length in `width` bytes, then its bytes. -/
def vec (width : Nat) (data : List UInt8) : List UInt8 := be width data.length ++ data

/-- Bytes behind a mark, so that no bytes differ from no value. -/
def x (bytes : List UInt8) : String :=
  "x" ++ (if bytes.isEmpty then "" else hex (packed bytes))

/-- A list of items between brackets. -/
def bracket (items : List String) : String := "[" ++ ",".intercalate items ++ "]"

/-- An extension block: the bytes, and the text of its extensions. -/
def block (extensions : List (Nat × List UInt8)) : List UInt8 × String :=
  (vec 2 (extensions.map fun (kind, data) => be 2 kind ++ vec 2 data).flatten,
    bracket (extensions.map fun (kind, data) => s!"{kind}={x data}"))

/-- A handshake message: its type, a length of three bytes, its body. -/
def envelope (kind : Nat) (body : List UInt8) : List UInt8 :=
  [UInt8.ofNat kind] ++ vec 3 body

/-- Extensions of distinct types, in any order, whose block has `minimum` bytes at least. -/
def genExtensions (minimum : Nat) : Gen (List (Nat × List UInt8)) := do
  let kinds ← Gen.subsequence [0, 5, 10, 13, 16, 41, 42, 43, 44, 45, 51, 57, 65281, 65535]
  let kinds ← Gen.shuffle kinds
  let extensions ← kinds.mapM fun kind => do pure (kind, ← genByteList (.linear 0 6))
  let size := (extensions.map fun (_, data) => 4 + data.length).sum
  -- The padding extension, RFC 7685, brings a short block to its least length.
  if size < minimum then pure (extensions ++ [(21, List.replicate (minimum - size - 4) 0)])
  else pure extensions

/-- A message as bytes, with what a reader must say of it: its text, or `error`. -/
structure Made where
  name : String
  text : String
  bytes : List UInt8
  deriving Repr, BEq

/-- A code point: a known one or any. -/
def genCode : Gen Nat :=
  Gen.frequency [(2, Gen.element [0x1301, 0x1302, 0x1303, 0x0403, 0x0304, 0x001d, 0x0017]),
    (1, genNatBits 16)]

/-- A session ID: none, 32 bytes, or between. -/
def genSession : Gen (List UInt8) :=
  Gen.frequency [(2, pure []), (1, genByteList (.singleton 32)), (2, genByteList (.linear 0 32))]

/-- A ClientHello, RFC 8446 section 4.1.2. -/
def genClientHello : Gen Made := do
  let random ← genByteList (.singleton 32)
  let session ← genSession
  let suites ← Gen.list (.linear 1 4) genCode
  let (extensions, shown) := block (← genExtensions 8)
  pure { name := "ClientHello",
         text := s!"ch:{x random}:{x session}:{bracket (suites.map toString)}:{shown}",
         bytes := envelope 1 ([3, 3] ++ random ++ vec 1 session ++
           vec 2 (suites.map (be 2)).flatten ++ [1, 0] ++ extensions) }

/-- A ServerHello, RFC 8446 section 4.1.3. -/
def genServerHello : Gen Made := do
  let random ← genByteList (.singleton 32)
  let session ← genSession
  let suite ← genCode
  let (extensions, shown) := block (← genExtensions 6)
  pure { name := "ServerHello", text := s!"sh:{x random}:{x session}:{suite}:{shown}",
         bytes := envelope 2 ([3, 3] ++ random ++ vec 1 session ++ be 2 suite ++ [0] ++
           extensions) }

/-- An EncryptedExtensions message, RFC 8446 section 4.3.1. -/
def genEncryptedExtensions : Gen Made := do
  let (extensions, shown) := block (← genExtensions 0)
  pure { name := "EncryptedExtensions", text := s!"ee:{shown}", bytes := envelope 8 extensions }

/-- A request context: none, a few bytes, or 255. -/
def genContext : Gen (List UInt8) :=
  Gen.frequency [(3, pure []), (2, genByteList (.linear 1 5)), (1, genByteList (.singleton 255))]

/-- A CertificateRequest, RFC 8446 section 4.3.2. -/
def genCertificateRequest : Gen Made := do
  let context ← genContext
  let (extensions, shown) := block (← genExtensions 2)
  pure { name := "CertificateRequest", text := s!"cr:{x context}:{shown}",
         bytes := envelope 13 (vec 1 context ++ extensions) }

/-- A Certificate message, RFC 8446 section 4.4.2: any number of entries, none included. -/
def genCertificate : Gen Made := do
  let context ← genContext
  let entries ← Gen.list (.linear 0 3) do
    let data ← genByteList (.linear 1 10)
    let (extensions, shown) := block (← genExtensions 0)
    pure (vec 3 data ++ extensions, s!"{x data}/{shown}")
  pure { name := "Certificate", text := s!"ct:{x context}:{bracket (entries.map (·.2))}",
         bytes := envelope 11 (vec 1 context ++ vec 3 (entries.map (·.1)).flatten) }

/-- A CertificateVerify, RFC 8446 section 4.4.3. -/
def genCertificateVerify : Gen Made := do
  let algorithm ← genCode
  let signature ← genByteList (.linear 0 72)
  pure { name := "CertificateVerify", text := s!"cv:{algorithm}:{x signature}",
         bytes := envelope 15 (be 2 algorithm ++ vec 2 signature) }

/-- A Finished of the length of the hash, RFC 8446 section 4.4.4. -/
def genFinished (hashLength : Nat) : Gen Made := do
  let data ← genByteList (.singleton hashLength)
  pure { name := "Finished", text := s!"fin:{x data}", bytes := envelope 20 data }

/-- Each of the seven messages, valid. -/
def genValid (hashLength : Nat) : Gen Made :=
  Gen.choice [genClientHello, genServerHello, genEncryptedExtensions, genCertificateRequest,
    genCertificate, genCertificateVerify, genFinished hashLength]

/-- The names of the messages, for the coverage of a property. -/
def messageNames : List String :=
  ["ClientHello", "ServerHello", "EncryptedExtensions", "CertificateRequest", "Certificate",
    "CertificateVerify", "Finished"]

/-- A message that breaks one bound or one fixed field, each by the least amount. -/
def genBroken (hashLength : Nat) : Gen Made := do
  let broken (name : String) (bytes : List UInt8) : Made := { name, text := "error", bytes }
  let random ← genByteList (.singleton 32)
  let (extensions, _) := block (← genExtensions 8)
  let hello (version : List UInt8) (session suites compression : List UInt8)
      (extensions : List UInt8) :=
    envelope 1 (version ++ random ++ vec 1 session ++ vec 2 suites ++ compression ++ extensions)
  let server (version : List UInt8) (session : List UInt8) (compression : List UInt8)
      (extensions : List UInt8) :=
    envelope 2 (version ++ random ++ vec 1 session ++ [0x13, 1] ++ compression ++ extensions)
  let long ← Gen.frequency [(2, genByteList (.singleton 33)), (1, genByteList (.constant 34 40))]
  let version ← Gen.element [[3, 4], [3, 2], [3, 1], [0, 0], [0xff, 0xff]]
  let short := (block [(0, [])]).1
  let twice ← Gen.element [0, 43, 51, 65535]
  let repeated := (block [(twice, [1]), (10, [0, 0, 0]), (twice, [])]).1
  Gen.element [
    broken "a legacy version that is not 0x0303" (hello version [] [0x13, 1] [1, 0] extensions),
    broken "a legacy version that is not 0x0303" (server version [] [0] extensions),
    broken "a session ID of more than 32 bytes" (hello [3, 3] long [0x13, 1] [1, 0] extensions),
    broken "a session ID of more than 32 bytes" (server [3, 3] long [0] extensions),
    broken "no cipher suite" (hello [3, 3] [] [] [1, 0] extensions),
    broken "half a cipher suite" (hello [3, 3] [] [0x13, 1, 0x13] [1, 0] extensions),
    broken "another compression" (hello [3, 3] [] [0x13, 1] [1, 1] extensions),
    broken "another compression" (hello [3, 3] [] [0x13, 1] [2, 0, 0] extensions),
    broken "another compression" (hello [3, 3] [] [0x13, 1] [0] extensions),
    broken "another compression" (server [3, 3] [] [1] extensions),
    broken "an extension block below its least length" (hello [3, 3] [] [0x13, 1] [1, 0] short),
    broken "an extension block below its least length" (hello [3, 3] [] [0x13, 1] [1, 0] [0, 0]),
    broken "an extension block below its least length" (server [3, 3] [] [0] short),
    broken "an extension block below its least length" (envelope 13 [0, 0, 0]),
    broken "an extension type twice" (hello [3, 3] [] [0x13, 1] [1, 0] repeated),
    broken "an extension type twice" (server [3, 3] [] [0] repeated),
    broken "an extension type twice" (envelope 8 repeated),
    broken "an extension type twice" (envelope 13 ([0] ++ repeated)),
    broken "an extension type twice" (envelope 11 ([0] ++ vec 3 (vec 3 [1] ++ repeated))),
    broken "a byte after the last field" (envelope 8 (extensions ++ [0])),
    broken "a byte after the last field" (envelope 15 ([4, 3] ++ vec 2 [1, 2] ++ [0])),
    broken "a byte after the last field" (hello [3, 3] [] [0x13, 1] [1, 0] (extensions ++ [0])),
    broken "a field that passes its message" (envelope 8 (extensions.dropLast)),
    broken "a field that passes its message" (envelope 15 [4, 3, 0, 9, 1]),
    broken "a field that passes its message" (envelope 11 ([0] ++ vec 3 [0, 0, 9, 1])),
    broken "a certificate of no bytes" (envelope 11 ([0] ++ vec 3 (vec 3 [] ++ [0, 0]))),
    broken "a context that passes its message" (envelope 11 [9, 0, 0, 0]),
    broken "a Finished of another length" (envelope 20 (List.replicate (hashLength + 1) 7)),
    broken "a Finished of another length" (envelope 20 (List.replicate (hashLength - 1) 7 ++
      (if hashLength = 0 then [7, 7] else []))),
    broken "a handshake type that is not read" (envelope twice extensions),
    broken "a handshake type that is not read" (envelope 4 extensions),
    broken "a handshake type that is not read" (envelope 24 [0]),
    broken "a handshake type that is not read" (envelope 254 (List.replicate 32 0))]

/-- A message as text: the name of what was built, and its bytes. -/
def showMade (made : Made) : String := s!"{made.name} {hex (packed made.bytes)}"

/-- An extension block as the oracle writes one. -/
def showExtensions (extensions : List Extension) : String :=
  bracket (extensions.map fun e => s!"{e.kind.val}={x e.data.toList}")

/-- A message as the oracle writes one. -/
def showMessage : Message → String
  | .clientHello h =>
    s!"ch:{x h.random.toList}:{x h.legacySessionId.toList}:" ++
      s!"{bracket (h.cipherSuites.map (toString ·.val))}:{showExtensions h.extensions}"
  | .serverHello h =>
    s!"sh:{x h.random.toList}:{x h.legacySessionIdEcho.toList}:{h.cipherSuite.val}:" ++
      showExtensions h.extensions
  | .encryptedExtensions extensions => s!"ee:{showExtensions extensions}"
  | .certificateRequest r => s!"cr:{x r.context.toList}:{showExtensions r.extensions}"
  | .certificate c =>
    let entries := c.entries.map fun e => s!"{x e.data.toList}/{showExtensions e.extensions}"
    s!"ct:{x c.context.toList}:{bracket entries}"
  | .certificateVerify algorithm signature => s!"cv:{algorithm.val}:{x signature.toList}"
  | .finished data => s!"fin:{x data.toList}"

/-- What EthLib reads at the start of the input: the message and the bytes after it.

A message whose envelope is not complete is told apart, since more input could complete it. -/
def readMessage (hashLength : Nat) (bytes : List UInt8) : String :=
  match EthLib.Networking.Quic.Tls.decode hashLength (packed bytes) with
  | .ok (message, rest) => s!"{showMessage message} {hex rest}"
  | .error (.truncated ..) => "error:truncated"
  | .error _ => "error"

/-- A handshake message reads as RFC 8446 section 4 says, at every length of hash.

What was built, what EthLib reads and what the reference reads are the same.

A message that EthLib reads, it writes back as the same bytes, since the encoding is canonical. -/
def messageDecode (oracle : Oracle) (long : Bool) : Property IO := propertyM do
  let hashLength ← forAll (Gen.element [32, 32, 48, 0, 20, 64])
  let shape ← forAll (Gen.frequency [(5, pure "valid"), (3, pure "broken"), (2, pure "mutated")])
  let made ← forAllWith showMade (if shape == "broken" then genBroken hashLength
    else genValid hashLength)
  let rest ← forAllWith (fun b => hex (packed b))
    (Gen.frequency [(2, pure []), (1, genByteList (.linear 1 4))])
  let bytes ← forAllWith (fun b => hex (packed b))
    (if shape == "mutated" then genMutation made.bytes else pure made.bytes)
  pure do
    let input := bytes ++ rest
    let reference ← oracle.ask ["tls_message", toString hashLength, hex (packed input)]
    let got := readMessage hashLength input
    messageNames.forM fun name => cover 3 name (made.name == name)
    cover 20 "valid as generated" (shape == "valid" && !refused reference)
    coverLong long 2 "mutated and still accepted by the reference"
      (shape == "mutated" && !refused reference)
    cover 10 "refused by the reference" (reference == "error")
    coverLong long 1 "an envelope that is not complete" (reference == "error:truncated")
    if shape == "broken" then label made.name
    classify "a hash of 48 bytes" (hashLength == 48)
    classify "a hash of another length than 32 and 48" (hashLength != 32 && hashLength != 48)
    got === reference
    if shape == "valid" then reference === s!"{made.text} {hex (packed rest)}"
    if shape == "broken" then reference === "error"
    if let .ok (message, after) := EthLib.Networking.Quic.Tls.decode hashLength (packed input) then
      match EthLib.Networking.Quic.Tls.encode hashLength message with
      | .error e => failWith s!"EthLib does not write the message it read: {repr e}"
      | .ok written => (written ++ after).toList === input

/-! ## The payloads of the extensions -/

/-- The forms of a payload, with the name of each and its extension type. -/
def forms : List (PayloadForm × String × Nat) :=
  [(.supportedVersions, "supportedVersions", 43), (.selectedVersion, "selectedVersion", 43),
    (.supportedGroups, "supportedGroups", 10), (.signatureAlgorithms, "signatureAlgorithms", 13),
    (.clientKeyShare, "clientKeyShare", 51), (.serverKeyShare, "serverKeyShare", 51),
    (.retryKeyShare, "retryKeyShare", 51), (.alpn, "alpn", 16),
    (.quicTransportParameters, "quicTransportParameters", 57)]

/-- A key share entry: the bytes, and its text. -/
def genShare : Gen (List UInt8 × String) := do
  let group ← genCode
  let key ← Gen.frequency [(1, genByteList (.singleton 32)), (1, genByteList (.singleton 65)),
    (2, genByteList (.linear 1 8))]
  pure (be 2 group ++ vec 2 key, s!"{group}={x key}")

/-- A list of code points behind a length of `width` bytes: the bytes, and its text. -/
def genCodes (width least most : Nat) : Gen (List UInt8 × String) := do
  let count ← Gen.frequency [(1, pure least), (1, pure most), (4, Gen.nat (.linear least 6))]
  let codes ← Gen.list (.singleton count) genCode
  pure (vec width (codes.map (be 2)).flatten, bracket (codes.map toString))

/-- A valid payload of a form: the bytes, and its text. -/
def genPayload : PayloadForm → Gen (List UInt8 × String)
  | .supportedVersions => do
    let (bytes, shown) ← genCodes 1 1 127
    pure (bytes, s!"sv:{shown}")
  | .selectedVersion => do
    let code ← genCode
    pure (be 2 code, s!"chosen:{code}")
  | .supportedGroups => do
    let (bytes, shown) ← genCodes 2 1 6
    pure (bytes, s!"sg:{shown}")
  | .signatureAlgorithms => do
    let (bytes, shown) ← genCodes 2 1 6
    pure (bytes, s!"sa:{shown}")
  | .clientKeyShare => do
    let shares ← Gen.list (.linear 0 3) genShare
    pure (vec 2 (shares.map (·.1)).flatten, s!"cks:{bracket (shares.map (·.2))}")
  | .serverKeyShare => do
    let (bytes, shown) ← genShare
    pure (bytes, s!"sks:{shown}")
  | .retryKeyShare => do
    let code ← genCode
    pure (be 2 code, s!"rks:{code}")
  | .alpn => do
    let names ← Gen.list (.linear 1 3) (Gen.frequency [(1, pure "libp2p".toUTF8.toList),
      (1, genByteList (.linear 1 6)), (1, genByteList (.singleton 255))])
    pure (vec 2 (names.map (vec 1)).flatten, s!"alpn:{bracket (names.map x)}")
  | .quicTransportParameters => do
    let data ← genByteList (.linear 0 12)
    pure (data, s!"qtp:{x data}")

/-- A payload that breaks a bound of its form: the name of the form, and the bytes. -/
def genBrokenPayload : Gen (String × List UInt8) :=
  Gen.element [
    ("supportedVersions", [0]), ("supportedVersions", [1, 3]), ("supportedVersions", [3, 3, 4, 3]),
    ("supportedVersions", [2, 3, 4, 0]), ("supportedVersions", vec 1 (List.replicate 255 3)),
    ("supportedVersions", []), ("selectedVersion", [3]), ("selectedVersion", [3, 4, 0]),
    ("selectedVersion", []), ("supportedGroups", [0, 0]), ("supportedGroups", [0, 1, 0]),
    ("supportedGroups", [0, 3, 0, 29, 0]), ("supportedGroups", [0, 2, 0, 29, 0]),
    ("signatureAlgorithms", [0, 0]), ("signatureAlgorithms", [0, 3, 4, 3, 8]),
    ("signatureAlgorithms", [0, 4, 4, 3]), ("clientKeyShare", [0, 4, 0, 29, 0, 0]),
    ("clientKeyShare", [0, 5, 0, 29, 0, 2, 1]), ("clientKeyShare", [0]),
    ("clientKeyShare", [0, 0, 0]), ("serverKeyShare", [0, 29, 0, 0]),
    ("serverKeyShare", [0, 29, 0, 1, 1, 0]), ("serverKeyShare", [0, 29, 0, 2, 1]),
    ("retryKeyShare", [0]), ("retryKeyShare", [0, 29, 0]), ("alpn", [0, 0]), ("alpn", [0, 1, 0]),
    ("alpn", [0, 3, 2, 0x68, 0x33, 0]), ("alpn", [0, 4, 4, 0x68, 0x33]), ("alpn", [])]

/-- The payload of an extension as the oracle writes one. -/
def showPayload : Payload → String
  | .supportedVersions versions => s!"sv:{bracket (versions.map (toString ·.val))}"
  | .selectedVersion version => s!"chosen:{version.val}"
  | .supportedGroups groups => s!"sg:{bracket (groups.map (toString ·.val))}"
  | .signatureAlgorithms algorithms => s!"sa:{bracket (algorithms.map (toString ·.val))}"
  | .clientKeyShare shares =>
    s!"cks:{bracket (shares.map fun s => s!"{s.group.val}={x s.keyExchange.toList}")}"
  | .serverKeyShare share => s!"sks:{share.group.val}={x share.keyExchange.toList}"
  | .retryKeyShare group => s!"rks:{group.val}"
  | .alpn protocols => s!"alpn:{bracket (protocols.map (x ·.toList))}"
  | .quicTransportParameters data => s!"qtp:{x data.toList}"

/-- The payload of an extension reads as its form says, in each of the nine forms.

An extension of another type than the form's is refused.

A payload that EthLib reads, it writes back as the same bytes. -/
def payloadDecode (oracle : Oracle) (long : Bool) : Property IO := propertyM do
  let shape ← forAll (Gen.frequency [(5, pure "valid"), (3, pure "broken"), (2, pure "mutated"),
    (1, pure "another type")])
  let (form, name, kind) ← forAllWith (·.2.1) (Gen.element forms)
  let (valid, text) ← forAllWith (fun (b, t) => s!"{t} {hex (packed b)}") (genPayload form)
  let (brokenName, brokenBytes) ← forAllWith (fun (n, b) => s!"{n} {hex (packed b)}")
    genBrokenPayload
  let mutated ← forAllWith (fun b => hex (packed b))
    (if valid.isEmpty then pure valid else genMutation valid)
  let other ← forAll (Gen.element [0, 10, 13, 16, 43, 51, 57])
  pure do
    let (form, name, kind) := if shape == "broken" then
        (forms.find? (·.2.1 == brokenName)).getD (form, name, kind)
      else (form, name, kind)
    let data := if shape == "broken" then brokenBytes else if shape == "mutated" then mutated
      else valid
    let kind := if shape == "another type" then other else kind
    let reference ← oracle.ask ["tls_payload", name, toString kind, hex (packed data)]
    let extension : Extension := ⟨Fin.ofNat _ kind, packed data⟩
    let got := match decodePayload form extension with
      | .ok payload => showPayload payload
      | .error _ => "error"
    forms.forM fun (_, formName, _) => cover 3 formName (name == formName)
    cover 20 "valid as generated" (shape == "valid")
    coverLong long 2 "mutated and still accepted by the reference"
      (shape == "mutated" && !refused reference)
    cover 15 "refused by the reference" (refused reference)
    got === reference
    if shape == "valid" then reference === text
    if shape == "broken" then reference === "error"
    if let .ok payload := decodePayload form extension then
      match encodePayload payload with
      | .error e => failWith s!"EthLib does not write the payload it read: {repr e}"
      | .ok written => do
        written.kind.val === kind
        written.data.toList === data

/-! ## The key schedule, the transcript and the groups -/

/-- A secret as text. -/
def secretsOf (s : KeySchedule) : List String :=
  [hexv s.early, hexv s.handshake, hexv s.master, hexv s.clientHandshake, hexv s.serverHandshake,
    hexv s.clientApplication, hexv s.serverApplication]

/-- The seven secrets of RFC 8446 section 7.1 and the Finished value are the reference's.

The shared secret may have any length, as the module says. -/
def scheduleSecrets (oracle : Oracle) : Property IO := propertyM do
  let shared ← forAllWith hex (Gen.frequency [(3, genBytes (.singleton 32)),
    (1, genBytes (.linear 0 80))])
  let hello ← forAllWith hex (genBytes (.linear 0 200))
  let server ← forAllWith hex (genBytes (.linear 0 200))
  pure do
    classify "a shared secret of another length than 32" (shared.size != 32)
    match EthLib.Networking.Quic.Tls.keySchedule shared hello server with
    | .error _ => failWith "EthLib gives no key schedule"
    | .ok schedule =>
      let want ← oracle.ask ["tls_schedule", hex shared, hex hello, hex server]
      " ".intercalate (secretsOf schedule) === want
      match EthLib.Networking.Quic.Tls.finished schedule.serverHandshake server with
      | .error _ => failWith "EthLib gives no Finished value"
      | .ok value =>
        hexv value === (← oracle.ask ["tls_finished", hexv schedule.serverHandshake, hex server])
      let digest := Cryptography.Hash.Sha256.hash32 hello
      for flag in [true, false] do
        hex (certificateVerifyInput flag digest) ===
          (← oracle.ask ["tls_verify_input", if flag then "1" else "0", hexv digest])

/-- A ClientHello or a ServerHello, with the random of a retry or another. -/
def genHello (client retry : Bool) : Gen (List UInt8) := do
  let made ← if client then genClientHello else genServerHello
  if client || !retry then pure made.bytes
  else
    -- The random is at bytes 6 to 37 of a ServerHello, after its envelope and its version.
    pure (made.bytes.take 6 ++ retryRandom.toList ++ made.bytes.drop 38)

/-- The transcript hash is the reference's, with the hello of a retry replaced by its hash.

A retry anywhere but after one ClientHello, or a second one, is refused. -/
def transcriptHash (oracle : Oracle) : Property IO := propertyM do
  let kinds ← forAll (Gen.frequency [
    (3, Gen.element [["ch"], ["ch", "sh"], ["ch", "hrr", "ch", "sh"], ["ch", "hrr"],
      ["ch", "hrr", "ch", "hrr"], ["hrr"], ["ch", "ch", "hrr"], ["sh", "hrr"], ["ch", "sh", "hrr"],
      ["ch", "hrr", "ch", "sh", "ee"], []]),
    (1, Gen.list (.linear 0 5) (Gen.element ["ch", "sh", "hrr", "ee"]))])
  let messages ← forAllWith (fun ms => " ".intercalate (ms.map fun m => hex (packed m)))
    (kinds.mapM fun kind => match kind with
      | "ch" => genHello true false
      | "sh" => genHello false false
      | "hrr" => genHello false true
      | _ => (·.bytes) <$> genEncryptedExtensions)
  pure do
    let want ← oracle.ask ("tls_transcript" :: messages.map fun m => hex (packed m))
    let got := match EthLib.Networking.Quic.Tls.transcript (messages.map packed) with
      | .ok transcript => hexv transcript.hash
      | .error _ => "error"
    cover 7 "a transcript with a retry" (kinds.contains "hrr" && !refused want)
    cover 10 "a retry out of place" (refused want)
    got === want

/-- A private key of 32 bytes: any, or one that P-256 refuses. -/
def genPrivate : Gen (Vector UInt8 32) :=
  Gen.frequency [(8, genVector 32), (1, pure (Vector.replicate 32 0)),
    (1, pure (Vector.replicate 32 0xff))]

/-- The order of the group of P-256. -/
def p256Order : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- The value of 32 bytes, big-endian. -/
def valueOf (bytes : Vector UInt8 32) : Nat :=
  bytes.toList.foldl (fun n b => n * 256 + b.toNat) 0

/-- A key share and a shared secret of X25519 and of P-256 are those of `cryptography`.

A scalar of P-256 outside 1 to `n - 1` is refused, and a share that is no point of the group.

The all-zero output of X25519 is refused, as RFC 8446 section 7.4.2 asks. -/
def groups (oracle : Oracle) : Property IO := propertyM do
  let group ← forAll (Gen.element [0x1d, 0x17])
  let mine ← forAllWith hexv genPrivate
  let theirs ← forAllWith hexv (genVector 32)
  let junk ← forAllWith hex (Gen.frequency [
    -- Points of small order on Curve25519, RFC 7748 section 6.1, as little-endian bytes.
    (2, (fun (n : Nat) => packed ((be 32 n).reverse)) <$> Gen.element [0, 1,
      2 ^ 255 - 19, 2 ^ 255 - 18, 2 ^ 255 - 20,
      325606250916557431795983626356110631294008115727848805560023387167927233504,
      39382357235489614581723060781553021112529911719440698176882885853963445705823]),
    (1, genBytes (.singleton 32)), (1, genBytes (.singleton 65)),
    (1, (packed [4] ++ ·) <$> genBytes (.singleton 64)), (1, genBytes (.linear 0 70))])
  let which ← forAll (Gen.frequency [(3, pure "a share of the peer"), (2, pure "other bytes")])
  pure do
    let code : Wire.CodePoint := Fin.ofNat _ group
    let scalar := group == 0x1d || (0 < valueOf mine && valueOf mine < p256Order)
    cover 16 "X25519" (group == 0x1d)
    cover 16 "P-256" (group == 0x17)
    classify "a scalar that P-256 refuses" (!scalar)
    match Crypto.keyShare code mine with
    | .error _ => ensure (!scalar) "EthLib gives no key share for a valid private key"
    | .ok share =>
      ensure scalar "EthLib gives a key share for a scalar outside the group"
      hex share === (← oracle.ask ["tls_share", toString group, hexv mine])
    let peer ← if which == "other bytes" then pure junk
      else do
        let answer ← oracle.ask ["tls_share", toString group, hexv theirs]
        match unhex? answer with
        | some bytes => pure bytes
        | none => failWith s!"the oracle gave no share: {answer}"
    if scalar then
      let want ← oracle.ask ["tls_shared", toString group, hexv mine, hex peer]
      let got := match Crypto.sharedSecret code mine peer with
        | .ok secret => hexv secret
        | .error _ => "error"
      cover 18 "a shared secret" (!refused want)
      cover 10 "a share that is refused" (refused want)
      got === verdict want

/-- A CertificateVerify signature of EthLib verifies under `cryptography`, and the reverse.

A signature over other content does not verify. -/
def certificateVerify (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith hexv (genVector 32)
  let content ← forAllWith hex (genBytes (.linear 0 120))
  let other ← forAllWith hex (genBytes (.linear 0 120))
  let algorithm ← forAll (Gen.frequency [(5, pure 0x0403), (1, Gen.element [0x0804, 0x0503, 0])])
  pure do
    if 0 < valueOf key && valueOf key < p256Order then
      let code : Wire.CodePoint := Fin.ofNat _ algorithm
      match Crypto.signCertificateVerify code key content with
      | .error _ => ensure (algorithm != 0x0403) "EthLib does not sign with ecdsa_secp256r1_sha256"
      | .ok signature =>
        ensure (algorithm == 0x0403) "EthLib signs with a scheme it does not have"
        (← oracle.ask ["tls_sign_check", hexv key, hex content, hex signature]) === "1"
      match words (← oracle.ask ["tls_sign", hexv key, hex content]) with
      | [spki, signature] =>
        let spki := (unhex? spki).getD .empty
        let signature := (unhex? signature).getD .empty
        Crypto.verifyCertificateVerify code spki content signature === (algorithm == 0x0403)
        if other != content then
          Crypto.verifyCertificateVerify code spki other signature === false
        Crypto.publicKeyMatches key spki === true
      | answer => failWith s!"the oracle answered {answer}"

/-! ## The whole handshake, against aioquic and against itself -/

/-- A libp2p certificate that the oracle made, with its signing key and its peer ID. -/
structure Peer where
  number : String
  certificate : ByteArray
  key : Vector UInt8 32
  peerId : ByteArray
  now : Nat

/-- A vector of the first `n` bytes. -/
def vectorOf (n : Nat) (bytes : ByteArray) : Vector UInt8 n :=
  Vector.ofFn fun i => bytes.data.getD i.val 0

/-- Ask the oracle for a new certificate. -/
def newPeer (oracle : Oracle) : TestT IO Peer := do
  match words (← oracle.ask ["tls_peer"]) with
  | [number, certificate, key, peerId, now] =>
    pure { number, certificate := (unhex? certificate).getD .empty,
           key := vectorOf 32 ((unhex? key).getD .empty), peerId := (unhex? peerId).getD .empty,
           now := now.toNat! }
  | answer => failWith s!"the oracle answered {answer}"

/-- What one end of a handshake is configured with, as numbers that a report can show. -/
structure Setup where
  suites : List Nat
  groups : List Nat
  shares : List Nat
  random : Vector UInt8 32
  secret : Vector UInt8 32
  parameters : ByteArray

instance : Repr Setup where
  reprPrec s _ := s!"suites {s.suites} groups {s.groups} shares {s.shares}"

/-- The configuration of EthLib for a setup and a certificate.

The secret of each group is the setup's, made a valid scalar of P-256 whatever its bytes. -/
def configOf (peer : Peer) (s : Setup) : Handshake.Config :=
  let secret : Vector UInt8 32 :=
    (s.secret.set 0 (s.secret[0] &&& 0x7f)).set 31 (s.secret[31] ||| 1)
  { policy := {
      cipherSuites := s.suites.map (Fin.ofNat _), groups := s.groups.map (Fin.ofNat _),
      signatureSchemes := [0x0403],
      certificates := { hostAlgorithms := [.secp256k1, .p256],
                        certificateAlgorithms := [.p256Sha256], rejectUniqueIds := true },
      rejectLegacySessionId := true },
    now := peer.now, certificates := [peer.certificate], signingKey := peer.key,
    random := s.random, ephemeralKeys := s.groups.map fun g => ⟨Fin.ofNat _ g, secret⟩,
    initialShares := s.shares.map (Fin.ofNat _), transportParameters := s.parameters }

/-- A setup of EthLib: the two suites and the two groups in any order, and shares for some. -/
def genSetup : Gen Setup := do
  let suites ← Gen.element [[0x1301], [0x1303], [0x1301, 0x1303], [0x1303, 0x1301]]
  let groups ← Gen.element [[0x1d], [0x17], [0x1d, 0x17], [0x17, 0x1d]]
  let shares ← Gen.frequency [(4, pure groups), (2, pure (groups.take 1)),
    (1, pure (groups.drop 1)), (1, pure [])]
  pure { suites, groups, shares, random := ← genVector 32, secret := ← genVector 32,
         parameters := ← genBytes (.linear 0 20) }

/-- The letter of a level in the words of the oracle. -/
def letterOf : Handshake.Level → String
  | .initial => "i"
  | .handshake => "h"
  | .application => "a"

/-- The messages of an answer of the oracle, each at its level. -/
def flightOf (answer : String) : TestT IO (List Handshake.FlightMessage) :=
  if answer == "-" then pure []
  else (words answer).mapM fun word =>
    match word.splitOn ":" with
    | [letter, data] =>
      let level := if letter == "i" then Handshake.Level.initial
        else if letter == "h" then .handshake else .application
      pure ⟨level, (unhex? data).getD .empty⟩
    | _ => failWith s!"the oracle answered {answer}"

/-- Numbers between commas. -/
def commas (values : List Nat) : String := ",".intercalate (values.map toString)

/-- The four traffic secrets of a completed handshake of EthLib. -/
def trafficOf (completion : Handshake.Completion) : List String :=
  (secretsOf completion.negotiated.secrets).drop 3

/-- EthLib dials a listener of aioquic, and completes with the secrets that aioquic holds.

aioquic has no HelloRetryRequest, so it refuses a hello with no share of a group of its own.

A dialer that expects another peer ID refuses the certificate. -/
def dialAioquic (oracle : Oracle) : Property IO := propertyM do
  let setup ← forAll genSetup
  let theirSuites ← forAll (Gen.element [[0x1301], [0x1303], [0x1301, 0x1303], [0x1303, 0x1301],
    [0x1302], [0x1302, 0x1303]])
  let theirGroups ← forAll (Gen.element [[0x1d], [0x17], [0x1d, 0x17], [0x17, 0x1d], [0x18]])
  let wrongPeer ← forAll (Gen.frequency [(5, pure false), (1, pure true)])
  pure do
    let mine ← newPeer oracle
    let theirs ← newPeer oracle
    let config := configOf mine setup
    let expectedId := if wrongPeer then mine.peerId else theirs.peerId
    let context ← oracle.ask ["tls_new", "server", theirs.number, commas theirSuites,
      commas theirGroups, hex setup.parameters]
    let common := theirSuites.any setup.suites.contains
    let share := setup.shares.any theirGroups.contains
    cover 8 "the handshake completes" (common && share && !wrongPeer)
    cover 5 "no cipher suite in common" (!common)
    cover 5 "no share of a group of the listener" (common && !share)
    cover 1 "another peer ID than expected" (common && share && wrongPeer)
    classify "X25519" (common && share && (theirGroups.find? setup.shares.contains) == some 0x1d)
    classify "P-256" (common && share && (theirGroups.find? setup.shares.contains) == some 0x17)
    classify "TLS_CHACHA20_POLY1305_SHA256" (common && share &&
      (theirSuites.find? setup.suites.contains) == some 0x1303)
    match Handshake.clientStart config with
    | .error e => failWith s!"EthLib does not start: {repr e}"
    | .ok first =>
      let mut state := first.state
      let mut outgoing := first.output
      let mut completion : Option Handshake.Completion := none
      let mut refusal : Option String := none
      for _ in [0:3] do
        let mut incoming := []
        for message in outgoing do
          let answer ← oracle.ask ["tls_feed", context, letterOf message.level, hex message.data]
          if refused answer then refusal := some s!"aioquic: {answer}"
          else incoming := incoming ++ (← flightOf answer)
        outgoing := []
        for message in incoming do
          if refusal.isNone then
            match Handshake.clientStep config expectedId state message with
            | .error e => refusal := some s!"EthLib: {repr e}"
            | .ok step =>
              state := step.state
              outgoing := outgoing ++ step.output
              if step.completion.isSome then completion := step.completion
      annotate s!"refusal: {refusal}"
      if !common || !share then
        ensure ((refusal.getD "").startsWith "aioquic: error AlertHandshakeFailure")
          "aioquic was to refuse the hello"
      else if wrongPeer then
        ensure ((refusal.getD "").startsWith "EthLib:") "EthLib was to refuse the certificate"
        ensure (((refusal.getD "").splitOn "peerId").length > 1) "the error is not of the peer ID"
      else
        refusal === none
        match completion with
        | none => failWith "EthLib did not complete"
        | some done =>
          done.peerId === theirs.peerId
          let answer := words (← oracle.ask ["tls_secrets", context])
          answer.take 4 === trafficOf done
          answer.getD 4 "" === "1"
          answer.getD 5 "" === hex mine.certificate

/-- EthLib listens to a dialer of aioquic, and completes with the secrets that aioquic holds.

The dialer sends a share of each of its groups, so EthLib asks for no retry. -/
def listenAioquic (oracle : Oracle) : Property IO := propertyM do
  let setup ← forAll genSetup
  let theirSuites ← forAll (Gen.element [[0x1301], [0x1303], [0x1301, 0x1303], [0x1303, 0x1301],
    [0x1302], [0x1302, 0x1303]])
  let theirGroups ← forAll (Gen.element [[0x1d], [0x17], [0x1d, 0x17], [0x17, 0x1d], [0x18]])
  pure do
    let mine ← newPeer oracle
    let theirs ← newPeer oracle
    let config := configOf mine setup
    let common := theirSuites.any setup.suites.contains
    let group := theirGroups.any setup.groups.contains
    cover 12 "the handshake completes" (common && group)
    cover 5 "no cipher suite in common" (!common)
    cover 5 "no group in common" (common && !group)
    classify "X25519" (common && (setup.groups.find? theirGroups.contains) == some 0x1d)
    classify "P-256" (common && (setup.groups.find? theirGroups.contains) == some 0x17)
    classify "TLS_CHACHA20_POLY1305_SHA256" (common && group &&
      (setup.suites.find? theirSuites.contains) == some 0x1303)
    match Handshake.serverStart config with
    | .error e => failWith s!"EthLib does not start: {repr e}"
    | .ok start =>
      let opened := words (← oracle.ask ["tls_new", "client", theirs.number, commas theirSuites,
        commas theirGroups, hex setup.parameters])
      let context := opened.headD ""
      let mut state := start
      let mut incoming ← flightOf (" ".intercalate (opened.drop 1))
      let mut completion : Option Handshake.Completion := none
      let mut refusal : Option String := none
      for _ in [0:3] do
        let mut outgoing := []
        for message in incoming do
          if refusal.isNone then
            match Handshake.serverStep config state message with
            | .error e => refusal := some s!"EthLib: {repr e}"
            | .ok step =>
              state := step.state
              outgoing := outgoing ++ step.output
              if step.completion.isSome then completion := step.completion
        incoming := []
        for message in outgoing do
          let answer ← oracle.ask ["tls_feed", context, letterOf message.level, hex message.data]
          if refused answer then refusal := some s!"aioquic: {answer}"
          else incoming := incoming ++ (← flightOf answer)
      annotate s!"refusal: {refusal}"
      if !common || !group then
        ensure ((refusal.getD "").startsWith "EthLib:") "EthLib was to refuse the hello"
        ensure (((refusal.getD "").splitOn "handshakeFailure").length > 1)
          "the error is not handshake_failure"
      else
        refusal === none
        match completion with
        | none => failWith "EthLib did not complete"
        | some done =>
          done.peerId === theirs.peerId
          let answer := words (← oracle.ask ["tls_secrets", context])
          answer.take 4 === trafficOf done
          answer.getD 4 "" === "1"
          answer.getD 5 "" === hex mine.certificate

/-- EthLib dials EthLib, with a HelloRetryRequest when the dialer sent no share of the group.

Both ends complete with each other's peer ID, and with the secrets and the Finished values

that the reference derives from the messages and from the two private keys. -/
def selfHandshake (oracle : Oracle) : Property IO := propertyM do
  let dialer ← forAll genSetup
  let listener ← forAll genSetup
  pure do
    let dialerPeer ← newPeer oracle
    let listenerPeer ← newPeer oracle
    let client := configOf dialerPeer dialer
    let server := configOf listenerPeer listener
    let suite := listener.suites.find? dialer.suites.contains
    let group := listener.groups.find? dialer.groups.contains
    let retry := match group with
      | some g => !dialer.shares.contains g
      | none => false
    cover 20 "the handshake completes" (suite.isSome && group.isSome)
    cover 8 "with a HelloRetryRequest" (suite.isSome && group.isSome && retry)
    classify "no cipher suite in common" suite.isNone
    cover 2 "no group in common" (suite.isSome && group.isNone)
    match Handshake.clientStart client, Handshake.serverStart server with
    | .ok first, .ok start =>
      let mut clientState := first.state
      let mut serverState := start
      let mut toServer := first.output
      let mut sent : List ByteArray := []
      let mut clientDone : Option Handshake.Completion := none
      let mut serverDone : Option Handshake.Completion := none
      let mut refusal : Option String := none
      let mut helloCount := 0
      let mut serverCount := 0
      for _ in [0:4] do
        let mut toClient := []
        for message in toServer do
          sent := sent ++ [message.data]
          if refusal.isNone then
            match Handshake.serverStep server serverState message with
            | .error e => refusal := some s!"listener: {repr e}"
            | .ok step =>
              serverState := step.state
              toClient := toClient ++ step.output
              if step.completion.isSome then serverDone := step.completion
        toServer := []
        for message in toClient do
          sent := sent ++ [message.data]
          -- The ServerHello that is no retry ends the first part of the transcript.
          if message.data.data.getD 0 0 == 2 &&
              (message.data.extract 6 38).toList != retryRandom.toList then
            helloCount := sent.length
          if message.data.data.getD 0 0 == 20 then serverCount := sent.length
          if refusal.isNone then
            match Handshake.clientStep client listenerPeer.peerId clientState message with
            | .error e => refusal := some s!"dialer: {repr e}"
            | .ok step =>
              clientState := step.state
              toServer := toServer ++ step.output
              if step.completion.isSome then clientDone := step.completion
      annotate s!"refusal: {refusal}"
      match suite, group with
      | some _, some g =>
        refusal === none
        match clientDone, serverDone with
        | some c, some s =>
          c.peerId === listenerPeer.peerId
          s.peerId === dialerPeer.peerId
          trafficOf c === trafficOf s
          (sent.any fun m => m.data.getD 0 0 == 2 &&
            (m.extract 6 38).toList == retryRandom.toList) === retry
          -- The reference: the shared secret from the two private keys, the rest from the bytes.
          let dialerSecret := (client.ephemeralKeys.headD ⟨0, Vector.replicate 32 0⟩).secret
          let listenerSecret := (server.ephemeralKeys.headD ⟨0, Vector.replicate 32 0⟩).secret
          let share ← oracle.ask ["tls_share", toString g, hexv listenerSecret]
          let shared ← oracle.ask ["tls_shared", toString g, hexv dialerSecret, share]
          let want := words (← oracle.ask (["tls_schedule_of", shared, toString helloCount,
            toString serverCount] ++ sent.map hex))
          want.take 4 === trafficOf c
          -- The Finished of the listener and of the dialer hold the reference's values.
          let finished := sent.filter fun m => m.data.getD 0 0 == 20
          (finished.map fun m => hex (m.extract 4 m.size)) === want.drop 4
        | _, _ => failWith "an end did not complete"
      | _, _ =>
        ensure ((refusal.getD "").startsWith "listener:") "the listener was to refuse the hello"
        ensure (((refusal.getD "").splitOn "handshakeFailure").length > 1)
          "the error is not handshake_failure"
    | _, _ => failWith "EthLib does not start"

/-- The messages of the placement table, with the letters of RFC 8446 section 4.2. -/
def contexts : List (Handshake.Context × String) :=
  [(.clientHello, "CH"), (.serverHello, "SH"), (.retry, "HRR"), (.encryptedExtensions, "EE"),
    (.certificateRequest, "CR"), (.certificate, "CT"), (.newSessionTicket, "NST")]

/-- An extension may appear in the messages that the table of RFC 8446 section 4.2 lists for it.

A type that the table does not list may appear anywhere.

Each case asks about one type in all seven messages. -/
def placement (oracle : Oracle) : Property IO := propertyM do
  let kind ← forAll (Gen.frequency [(6, Gen.nat (.constant 0 60)), (1, genNatBits 16)])
  pure do
    let mut listed := false
    for (context, letters) in contexts do
      let want ← oracle.ask ["tls_allowed", letters, toString kind]
      if want == "0" then listed := true
      annotate s!"in {letters} the table says {want}"
      (if Handshake.allowedExtension context (Fin.ofNat _ kind) then "1" else "0") === want
    cover 10 "a type that the table lists" listed
    cover 20 "a type that the table does not list" (!listed)

/-! ### A handshake as commands: delivered, changed on the way, at another level, again -/

/-- Two ends of EthLib and the messages between them.

`spoiled` says that a byte of a message was changed on its way.

`failed` says that an end refused a message, and so left the handshake. -/
structure Session where
  dialer : Option Setup := none
  listener : Option Setup := none
  client : Option Handshake.Config := none
  server : Option Handshake.Config := none
  clientId : ByteArray := .empty
  serverId : ByteArray := .empty
  clientState : Option Handshake.State := none
  serverState : Option Handshake.State := none
  toServer : List Handshake.FlightMessage := []
  toClient : List Handshake.FlightMessage := []
  lastToServer : Option Handshake.FlightMessage := none
  lastToClient : Option Handshake.FlightMessage := none
  clientDone : Option Handshake.Completion := none
  serverDone : Option Handshake.Completion := none
  spoiled : Bool := false
  failed : Bool := false
  deriving Inhabited

/-- Whether a message waits to be delivered. -/
def Session.pending (s : Session) : Bool := !s.toServer.isEmpty || !s.toClient.isEmpty

/-- A session whose two ends share a suite and a group, so that an unchanged handshake completes.

The dialer offers both groups, and shares of some: the listener may have to ask again. -/
def genStart : Gen Session := do
  let dialer ← genSetup
  let listener ← genSetup
  let groups ← Gen.element [[0x1d, 0x17], [0x17, 0x1d]]
  let shares ← Gen.element [groups, groups.take 1, groups.drop 1, []]
  pure { dialer := some { dialer with suites := [0x1301, 0x1303], groups, shares },
         listener := some listener }

/-- Make the certificates of both ends, and send the first ClientHello. -/
def startSession (oracle : Oracle) (s : Session) : TestT IO Session := do
  match s.dialer, s.listener with
  | some dialer, some listener =>
    let dialerPeer ← newPeer oracle
    let listenerPeer ← newPeer oracle
    let client := configOf dialerPeer dialer
    let server := configOf listenerPeer listener
    annotate s!"dialer: {repr dialer}; listener: {repr listener}"
    match Handshake.clientStart client, Handshake.serverStart server with
    | .ok first, .ok start =>
      pure { s with client := some client, server := some server, clientId := dialerPeer.peerId,
                    serverId := listenerPeer.peerId, clientState := some first.state,
                    serverState := some start, toServer := first.output }
    | _, _ => failWith "EthLib does not start"
  | _, _ => failWith "the session has no setup"

/-- One step of the end that the next message is for, on that message or on another. -/
def stepOn (s : Session) (toServer : Bool) (message : Handshake.FlightMessage) :
    TestT IO (Except Handshake.Error Handshake.Step) :=
  if toServer then
    match s.server, s.serverState with
    | some config, some state => pure (Handshake.serverStep config state message)
    | _, _ => failWith "the listener was not started"
  else
    match s.client, s.clientState with
    | some config, some state => pure (Handshake.clientStep config s.serverId state message)
    | _, _ => failWith "the dialer was not started"

/-- The message that is delivered next, and whether it is for the listener. -/
def Session.next (s : Session) : Option (Bool × Handshake.FlightMessage) :=
  match s.toServer, s.toClient with
  | message :: _, _ => some (true, message)
  | [], message :: _ => some (false, message)
  | [], [] => none

/-- Deliver the next message to its end. -/
structure Deliver where

instance : Command Deliver Session Oracle IO where
  check _ _ s := !s.failed && s.pending
  apply _ _ s := do
    let some (toServer, message) := s.next | failWith "nothing to deliver"
    match ← stepOn s toServer message with
    | .error e =>
      -- Only a message that was changed, or one after it, may be refused.
      ensure s.spoiled s!"an unchanged message is refused: {repr e}"
      label "a message refused after a changed byte"
      pure { s with failed := true }
    | .ok step =>
      -- Every byte of a message is in the transcript, so no end may complete after a change.
      ensure (!(s.spoiled && step.completion.isSome)) "an end completes after a changed byte"
      if s.spoiled then label "a message accepted after a changed byte"
      if toServer then
        pure { s with serverState := some step.state, toServer := s.toServer.drop 1,
                      toClient := s.toClient ++ step.output, lastToServer := some message,
                      serverDone := step.completion <|> s.serverDone }
      else
        pure { s with clientState := some step.state, toClient := s.toClient.drop 1,
                      toServer := s.toServer ++ step.output, lastToClient := some message,
                      clientDone := step.completion <|> s.clientDone }
  label _ := "DELIVER"
  build _ := pure {}

/-- Change one byte of the next message on its way. -/
structure Spoil where
  at_ : Nat
  mask : UInt8

instance : Command Spoil Session Oracle IO where
  -- One change in a sequence: a second one with the same place and mask undoes the first.
  check _ _ s := !s.failed && s.pending && !s.spoiled
  apply _ c s := do
    let change (message : Handshake.FlightMessage) : Handshake.FlightMessage :=
      let i := c.at_ % message.data.size
      ⟨message.level, message.data.set! i (message.data[i]! ^^^ c.mask)⟩
    label "a byte changed on the way"
    match s.toServer, s.toClient with
    | message :: rest, _ => pure { s with toServer := change message :: rest, spoiled := true }
    | [], message :: rest => pure { s with toClient := change message :: rest, spoiled := true }
    | [], [] => pure s
  label c := s!"SPOIL({c.at_}, {c.mask})"
  build _ := do pure ⟨← Gen.nat (.linear 0 400), ← Gen.element [1, 2, 0x10, 0x80, 0xff]⟩

/-- Offer the next message at another encryption level, without delivering it.

RFC 9001 section 4.1.3: data at a lower level than expected is a PROTOCOL_VIOLATION.

Data at a higher level is not yet due, so the message is unexpected. -/
structure WrongLevel where
  level : Handshake.Level

instance : Command WrongLevel Session Oracle IO where
  check _ c s := !s.failed && !s.spoiled && s.pending &&
    (s.next.map (·.2.level != c.level)).getD false
  apply _ c s := do
    let some (toServer, message) := s.next | failWith "nothing to offer"
    let lower := c.level.rank < message.level.rank
    match ← stepOn s toServer ⟨c.level, message.data⟩ with
    | .ok _ => failWith "a message at another level is accepted"
    | .error e =>
      label (if lower then "a message at a lower level" else "a message at a higher level")
      e === (if lower then Handshake.Error.protocolViolation else .unexpectedMessage)
    pure s
  label c := s!"WRONG_LEVEL({repr c.level})"
  build _ := WrongLevel.mk <$> Gen.element [.initial, .handshake, .application]

/-- Offer the last delivered message to its end again, which must refuse it. -/
structure Again where
  toServer : Bool

instance : Command Again Session Oracle IO where
  check _ c s := !s.failed && !s.spoiled &&
    (if c.toServer then s.lastToServer.isSome else s.lastToClient.isSome)
  apply _ c s := do
    let some message := (if c.toServer then s.lastToServer else s.lastToClient)
      | failWith "nothing was delivered"
    match ← stepOn s c.toServer message with
    | .ok _ => failWith "a message that was delivered before is accepted again"
    | .error _ => label "a message offered again"
    pure s
  label c := s!"AGAIN({if c.toServer then "listener" else "dialer"})"
  build _ := Again.mk <$> Gen.bool

/-- When nothing is left to deliver and no byte was changed, both ends have completed. -/
structure Settle where

instance : Command Settle Session Oracle IO where
  check _ _ s := !s.failed && !s.spoiled && !s.pending
  apply _ _ s := do
    match s.clientDone, s.serverDone with
    | some c, some d =>
      label "both ends completed"
      c.peerId === s.serverId
      d.peerId === s.clientId
      trafficOf c === trafficOf d
    | _, _ => failWith "nothing is left to deliver and an end has not completed"
    pure s
  label _ := "SETTLE"
  build _ := pure {}

/-- A handshake between two ends of EthLib, as commands in any order.

An unchanged message is accepted, and at the end both ends hold the same secrets.

After a changed byte no end completes; a message at another level or offered twice is refused. -/
def handshakeCommands (oracle : Oracle) : Property IO :=
  -- A handshake takes eleven deliveries at least, so most commands deliver.
  let deliver := List.replicate 14 (Command.gen Deliver (σ := Session))
  scenarioFrom genStart .madhouse oracle (deliver ++ [Command.gen Spoil, Command.gen WrongLevel,
    Command.gen WrongLevel, Command.gen Again, Command.gen Settle, Command.gen Settle,
    Command.gen Settle]) (.linear 1 80) (startSession oracle)

/-- The properties that must pass. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("tls: a handshake message of each type, RFC 8446 section 4",
    (messageDecode oracle (cases ≥ 1000)).withTests cases),
  ("tls: the payload of an extension in each form",
    (payloadDecode oracle (cases ≥ 1000)).withTests cases),
  ("tls: the key schedule, RFC 8446 section 7.1",
    (scheduleSecrets oracle).withTests (min cases 300)),
  ("tls: the transcript hash and its retry", (transcriptHash oracle).withTests cases),
  ("tls: key shares and shared secrets of both groups", (groups oracle).withTests (min cases 200)),
  ("tls: the CertificateVerify signature", (certificateVerify oracle).withTests (min cases 50)),
  ("tls: EthLib dials aioquic", (dialAioquic oracle).withTests (min cases 60)),
  ("tls: EthLib listens to aioquic", (listenAioquic oracle).withTests (min cases 60)),
  ("tls: EthLib dials EthLib, with and without a retry",
    (selfHandshake oracle).withTests (min cases 60)),
  ("tls: the messages that may carry an extension", (placement oracle).withTests cases),
  ("tls: a handshake as commands, with changed bytes (`Command`, madhouse)",
    (handshakeCommands oracle).withTests (min cases 300))]

/-- The properties that fail by design: each is a finding. -/
def findings (_oracle : Oracle) (_cases : Nat) : List (String × Property IO) := []

end DecodersProperty.Tls

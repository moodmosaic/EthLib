import Hedgehog
import Support
import Property.Networking.Common
import EthLib.Networking.Enr.V4
import EthLib.Networking.Discv4.Packet

/-!
# Node records and discv4 packets, on generated inputs

The reference builds and reads records from the text of EIP-778, with `rlp` and libsecp256k1.

It reads discv4 packets from `discv4.md`, EIP-8 and EIP-868.

The inputs are valid records and packets with one rule of the source broken.
-/

open Hedgehog Support EthLib EthLib.Networking
open EthLib.Serialization.Rlp (Item)
open EthLib.Cryptography.Secp256k1 (Fn)

namespace NetworkingProperty.Records

open NetworkingProperty

/-- The keys that a record may hold beside `id` and `secp256k1`, in key order. -/
def extraKeys : List String := ["attnets", "eth", "eth2", "ip", "ip6", "quic", "tcp", "udp", "zz"]

/-- Some of the extra keys, in order, each with a value of bytes. -/
def genPairs : Gen (List (ByteArray × ByteArray)) := do
  let keys ← Gen.subsequence extraKeys
  keys.mapM fun k => (k.toUTF8, ·) <$> Gen.frequency [
    (5, genBytes (.linear 0 8)), (1, genBytes (.linear 0 120))]

/-- A signed record is the reference's, byte for byte, and both refuse one over 300 bytes. -/
def enrMake (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let seq ← forAll genUInt64
  let pairs ← forAll genPairs
  pure do
    let want ← oracle.ask ["enr_make", secretHex sk, toString seq.toNat,
      ",".intercalate (pairs.map fun (k, v) => s!"{hex k}:{hex v}") ++ ","]
    match Enr.makeRecordV4 (Fin.ofNat _ sk) seq (pairs.map fun (k, v) => (k, .bytes v)) with
    | .ok r => hex (r.encode.toOption.getD .empty) === want
    | .error _ => ensure (want.startsWith "error") s!"EthLib refuses, the reference gives {want}"

/-- One rule of EIP-778 to break in a valid record. -/
inductive Break where
  | none
  /-- Exchange two neighbouring pairs, so the keys are not sorted. -/
  | swap (i : Nat)
  /-- Repeat a pair. -/
  | repeatPair (i : Nat)
  /-- Drop a pair, `id` and `secp256k1` included. -/
  | drop (i : Nat)
  /-- Drop the last value. -/
  | odd
  /-- Change a byte of the signature. -/
  | signature (i : Nat)
  /-- Replace `s` by `n - s`. -/
  | highS
  /-- Give the signature another length. -/
  | signatureSize (n : Nat)
  /-- Write the sequence number as these bytes. -/
  | seq (bytes : List UInt8)
  /-- Replace the value of a pair. -/
  | value (i : Nat) (value : Item)
  /-- Make a key a list. -/
  | listKey (i : Nat)
  /-- Change one byte of the encoding. -/
  | flip (i : Nat) (x : UInt8)
  /-- Append bytes to the encoding. -/
  | trailing (bytes : List UInt8)
  deriving Repr

/-- A break, with values that sit at the edges of the rules. -/
def genBreak : Gen Break :=
  Gen.frequency [
    (4, pure .none),
    (2, Break.swap <$> Gen.nat (.constant 0 5)),
    (2, Break.repeatPair <$> Gen.nat (.constant 0 5)),
    (2, Break.drop <$> Gen.nat (.constant 0 5)),
    (1, pure .odd),
    (2, Break.signature <$> Gen.nat (.constant 0 63)),
    (1, pure .highS),
    (1, Break.signatureSize <$> Gen.element [0, 63, 65]),
    (2, Break.seq <$> Gen.element [[0], [0, 1], [1, 0, 0, 0, 0, 0, 0, 0, 0],
      [255, 255, 255, 255, 255, 255, 255, 255], [0x80]]),
    (2, Gen.zipWith Break.value (Gen.nat (.constant 0 5)) (Gen.element [
      Item.bytes "v5".toUTF8, .bytes .empty, .list [], .bytes ⟨Array.replicate 33 2⟩,
      .bytes ⟨Array.replicate 32 2⟩, .list [.bytes "v4".toUTF8]])),
    (1, Break.listKey <$> Gen.nat (.constant 0 5)),
    (2, Gen.zipWith Break.flip (Gen.nat (.linear 0 300)) (Gen.element [1, 0x80, 0xff])),
    (1, Break.trailing <$> genByteList (.linear 1 3))]

/-- The pairs of a list, as items. -/
def pairItems (pairs : List (Item × Item)) : List Item :=
  pairs.flatMap fun (k, v) => [k, v]

/-- The bytes of a record with one rule broken. -/
def Break.apply (r : Enr.Enr) (b : Break) : ByteArray :=
  let pairs : List (Item × Item) := r.pairs.map fun (k, v) => (.bytes k, v)
  let n := pairs.length
  let seq : Item := .scalar r.seq.toNat
  let build (sig : ByteArray) (seq : Item) (rest : List Item) :=
    rlp (.list (.bytes sig :: seq :: rest))
  match b with
  | .none => build r.signature seq (pairItems pairs)
  | .swap i =>
    let i := i % (n - 1)
    build r.signature seq
      (pairItems (pairs.take i ++ ((pairs.drop i).take 2).reverse ++ pairs.drop (i + 2)))
  | .repeatPair i =>
    let i := i % n
    build r.signature seq (pairItems (pairs.take (i + 1) ++ pairs.drop i))
  | .drop i => build r.signature seq (pairItems (pairs.eraseIdx (i % n)))
  | .odd => build r.signature seq ((pairItems pairs).dropLast)
  | .signature i =>
    build (r.signature.set! (i % 64) (r.signature[i % 64]! ^^^ 1)) seq (pairItems pairs)
  | .highS =>
    let s := Base.bytesToNat (r.signature.toList.drop 32)
    build ⟨(r.signature.toList.take 32 ++ Base.natToBytes 32 (Fn.modulus - s)).toArray⟩ seq
      (pairItems pairs)
  | .signatureSize k =>
    build ⟨((r.signature.toList ++ [0]).take k).toArray⟩ seq (pairItems pairs)
  | .seq bytes => build r.signature (.bytes ⟨bytes.toArray⟩) (pairItems pairs)
  | .value i v =>
    let i := i % n
    build r.signature seq (pairItems (pairs.mapIdx fun j p => if j = i then (p.1, v) else p))
  | .listKey i =>
    let i := i % n
    build r.signature seq
      (pairItems (pairs.mapIdx fun j p => if j = i then (.list [p.1], p.2) else p))
  | .flip i x =>
    let bytes := build r.signature seq (pairItems pairs)
    bytes.set! (i % bytes.size) (bytes[i % bytes.size]! ^^^ x)
  | .trailing extra => build r.signature seq (pairItems pairs) ++ ⟨extra.toArray⟩

/-- What EthLib reads of a record: the words of the reference's answer. -/
def readRecord (bytes : ByteArray) : String :=
  match Enr.decode bytes with
  | .error _ => "error"
  | .ok r =>
    let id := match Enr.nodeId r with
      | .ok id => hex ⟨id.toArray⟩
      | .error _ => "-"
    s!"{r.seq.toNat} {id} {if Enr.verifyV4 r then 1 else 0}"

/-- A record with a rule broken reads as EIP-778 says: refused, or its node ID and validity. -/
def enrRead (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let seq ← forAll genUInt64
  let pairs ← forAll genPairs
  let broken ← forAll genBreak
  pure do
    match Enr.makeRecordV4 (Fin.ofNat _ sk) seq (pairs.map fun (k, v) => (k, .bytes v)) with
    | .error _ => pure ()
    | .ok r =>
      let bytes := broken.apply r
      annotate s!"record: {hex bytes}"
      readRecord bytes === verdict (← oracle.ask ["enr_read", hex bytes])

/-- A record of exactly 300 bytes is read, and one of 301 is refused, as the reference does. -/
def enrSize (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let size ← forAll (Gen.nat (.constant 173 177))
  pure do
    let pairs := [("zz".toUTF8, Item.bytes ⟨Array.replicate size 7⟩)]
    let want ← oracle.ask ["enr_make", secretHex sk, "1",
      s!"{hex "zz".toUTF8}:{hex ⟨Array.replicate size 7⟩},"]
    match Enr.makeRecordV4 (Fin.ofNat _ sk) 1 pairs with
    | .ok r =>
      let bytes := r.encode.toOption.getD .empty
      annotate s!"size: {bytes.size}"
      hex bytes === want
      readRecord bytes === verdict (← oracle.ask ["enr_read", hex bytes])
    | .error _ => ensure (want.startsWith "error") "EthLib refuses a record the reference makes"

/-- The text form reads back, and only with the prefix `enr:`. -/
def enrText : Property IO := pureIO do
  let sk ← forAll genSecret
  let pairs ← forAll genPairs
  match Enr.makeRecordV4 (Fin.ofNat _ sk) 7 (pairs.map fun (k, v) => (k, .bytes v)) with
  | .error _ => pure ()
  | .ok r =>
    let .ok text := r.toText | failWith "toText"
    ensure ((Enr.fromText text).toOption == some r) "the text does not read back"
    ensure (text.all fun c => c.isAlphanum || c == '-' || c == '_' || c == ':') "not base64url"
    ensure (Enr.fromText ("ENR:" ++ text.drop 4)).toOption.isNone "an upper-case prefix reads"
    ensure (Enr.fromText (text ++ "=")).toOption.isNone "padding reads"

/-! ## discv4 -/

/-- A port: the edges and any. -/
def genPort : Gen UInt16 := UInt16.ofNat <$> genNatBits 16

/-- An endpoint with an address of 4 or 16 bytes. -/
def genEndpoint : Gen Discv4.Endpoint := do
  let ip ← Gen.choice [genBytes (.singleton 4), genBytes (.singleton 16)]
  let (udp, tcp) ← Gen.zip genPort genPort
  pure ⟨ip, udp, tcp⟩

/-- A packet of each of the six types. -/
def genPacket : Gen Discv4.Packet :=
  let expiration := genNatBits 64
  let seq := Gen.option genUInt64
  Gen.choice [
    do pure (.ping (← genNatBits 16) (← genEndpoint) (← genEndpoint) (← expiration) (← seq)),
    do pure (.pong (← genEndpoint) (← genVector 32) (← expiration) (← seq)),
    do pure (.findNode (← genVector 64) (← expiration)),
    do pure (.neighbors (← Gen.list (.linear 0 4)
      (Gen.zipWith Discv4.Node.mk genEndpoint (genVector 64))) (← expiration)),
    Discv4.Packet.enrRequest <$> expiration,
    do pure (.enrResponse (← genVector 32) (.list [.bytes (← genBytes (.linear 0 9))]))]

/-- A packet that EthLib signs is the reference's packet around the same RLP data. -/
def discv4Make (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let packet ← forAllWith (fun p => showItem (.list p.fields)) genPacket
  pure do
    let want ← oracle.ask ["discv4_make", secretHex sk, toString packet.type.toNat,
      hex (rlp (.list packet.fields))]
    match Discv4.encode (Fin.ofNat _ sk) packet with
    | .ok bytes => hex bytes === want
    | .error _ => failWith "EthLib does not encode the packet"

/-- A change to the data of a packet that the source accepts, or one that it refuses. -/
inductive Tweak where
  | none
  /-- Further items at the end of the list, which EIP-8 asks a reader to ignore. -/
  | extraItems (items : List Item)
  /-- Bytes after the list, which EIP-8 asks a reader to ignore. -/
  | trailing (bytes : List UInt8)
  /-- Replace one field. -/
  | field (i : Nat) (item : Item)
  /-- Drop the last field. -/
  | dropLast
  /-- Another packet type for the same data. -/
  | type (type : Nat)
  deriving Repr

/-- Items that sit at the edges of what a field accepts. -/
def genOddItem : Gen Item :=
  Gen.element [.bytes .empty, .list [], .bytes ⟨#[0]⟩, .bytes ⟨#[0, 1]⟩, .bytes ⟨#[1, 0, 0]⟩,
    .bytes ⟨Array.replicate 9 1⟩, .bytes ⟨Array.replicate 31 1⟩, .bytes ⟨Array.replicate 33 1⟩,
    .bytes ⟨Array.replicate 63 1⟩, .bytes ⟨Array.replicate 65 1⟩,
    .list [.bytes ⟨Array.replicate 4 1⟩, .bytes ⟨#[1]⟩, .bytes ⟨#[1]⟩],
    .list [.bytes ⟨Array.replicate 4 1⟩, .bytes ⟨#[1, 0, 0]⟩, .bytes ⟨#[1]⟩],
    .list [.bytes ⟨Array.replicate 4 1⟩, .bytes ⟨#[1]⟩],
    .list [.list [.bytes ⟨Array.replicate 4 1⟩, .bytes ⟨#[1]⟩, .bytes ⟨#[1]⟩, .bytes ⟨#[1]⟩]]]

/-- A tweak. -/
def genTweak : Gen Tweak :=
  Gen.frequency [
    (3, pure .none),
    (3, Tweak.extraItems <$> Gen.list (.linear 1 3) genOddItem),
    (2, Tweak.trailing <$> genByteList (.linear 1 4)),
    (4, Gen.zipWith Tweak.field (Gen.nat (.constant 0 4)) genOddItem),
    (1, pure .dropLast),
    (1, Tweak.type <$> Gen.nat (.constant 0 7))]

/-- The packet type and the data after a tweak. -/
def Tweak.apply (p : Discv4.Packet) : Tweak → Nat × ByteArray
  | .none => (p.type.toNat, rlp (.list p.fields))
  | .extraItems items => (p.type.toNat, rlp (.list (p.fields ++ items)))
  | .trailing bytes => (p.type.toNat, rlp (.list p.fields) ++ ⟨bytes.toArray⟩)
  | .field i item =>
    (p.type.toNat,
      rlp (.list (p.fields.mapIdx fun j f => if j = i % p.fields.length then item else f)))
  | .dropLast => (p.type.toNat, rlp (.list p.fields.dropLast))
  | .type t => (t, rlp (.list p.fields))

/-- What EthLib reads of a packet, in the words of the reference. -/
def readPacket (bytes : ByteArray) : String :=
  match Discv4.decode bytes with
  | .error _ => "error"
  | .ok r =>
    s!"{hex ⟨(Rlpx.encodePublicKey r.sender).toArray⟩} {hex ⟨r.hash.toArray⟩} " ++
      s!"{r.packet.type.toNat} {hex (rlp (.list r.packet.fields))}"

/-- A packet with tweaked data reads as `discv4.md`, EIP-8 and EIP-868 say. -/
def discv4Read (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let packet ← forAllWith (fun p => showItem (.list p.fields)) genPacket
  let tweak ← forAll genTweak
  let flip ← forAll (Gen.frequency [(6, pure none), (1, some <$> Gen.nat (.linear 0 200))])
  pure do
    let (type, data) := tweak.apply packet
    let made ← oracle.ask ["discv4_make", secretHex sk, toString type, hex data]
    let some bytes := unhex? made | failWith "oracle"
    -- A changed byte breaks the hash, the signature or the data.
    let bytes := match flip with
      | some i => bytes.set! (i % bytes.size) (bytes[i % bytes.size]! ^^^ 0x10)
      | none => bytes
    annotate s!"packet: {hex bytes}"
    readPacket bytes === verdict (← oracle.ask ["discv4_read", hex bytes])

/-- A signature that is changed under a recomputed hash recovers the key the reference does. -/
def discv4Signature (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let packet ← forAllWith (fun p => showItem (.list p.fields)) genPacket
  let at_ ← forAll (Gen.nat (.constant 0 64))
  let value ← forAll (Gen.element [(0 : UInt8), 1, 2, 27, 28, 0xff])
  pure do
    let made ← oracle.ask ["discv4_make", secretHex sk, toString packet.type.toNat,
      hex (rlp (.list packet.fields))]
    let some bytes := unhex? made | failWith "oracle"
    let body := (bytes.extract 32 bytes.size).set! at_ value
    let bytes := ⟨(Discv4.keccak body.toList).toArray⟩ ++ body
    annotate s!"packet: {hex bytes}"
    readPacket bytes === verdict (← oracle.ask ["discv4_read", hex bytes])

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  let slow := min cases 300
  [("enr: a signed record is the reference's", (enrMake oracle).withTests slow),
   ("enr: a record with a rule broken", (enrRead oracle).withTests slow),
   ("enr: the limit of 300 bytes", (enrSize oracle).withTests (min cases 30)),
   ("enr: the text form", enrText.withTests (min cases 100)),
   ("discv4: a packet is the reference's", (discv4Make oracle).withTests slow),
   ("discv4: a packet with tweaked data", (discv4Read oracle).withTests slow),
   ("discv4: a changed signature", (discv4Signature oracle).withTests slow)]

end NetworkingProperty.Records

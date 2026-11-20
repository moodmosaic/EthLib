import Hedgehog
import Support
import Property.Decoders.Devp2p.Common
import EthLib.Networking.Discv4.Packet
import EthLib.Networking.Discv5.Handshake
import EthLib.Networking.Discv5.Session

/-!
# The session packets of discv5 and the record check of discv4, on generated inputs

The reference is written from `discv5-wire.md`, with AES by `cryptography`.

It reproduces the Ping and WHOAREYOU packets of `discv5-wire-test-vectors.md` when it starts.

The record check is EIP-778's, with libsecp256k1 for the signature.
-/

open Hedgehog Support EthLib EthLib.Networking
open EthLib.Serialization.Rlp (Item)

namespace DecodersProperty.Devp2p.Discv

open DecodersProperty DecodersProperty.Devp2p

/-! ## WHOAREYOU -/

/-- A sequence number of a record: zero, small ones and the ends of 64 bits. -/
def genSeq : Gen UInt64 :=
  Gen.frequency [(1, pure 0), (3, genUInt64)]

/-- The packet and the challenge data of a WHOAREYOU are those of `discv5-wire.md`.

Node A reads back what node B wrote. -/
def whoareyou (oracle : Oracle) : Property IO := propertyM do
  let dest ← forAllWith hexv (genVector 32)
  let (iv, nonce) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}")
    (Gen.zip (genVector 16) (genVector 12))
  let idNonce ← forAllWith hexv (genVector 16)
  let seq ← forAll genSeq
  pure do
    let want ← oracle.ask ["d5_whoareyou", hexv dest, hexv iv, hexv nonce, hexv idNonce,
      toString seq.toNat]
    match Discv5.makeWhoareyou dest iv nonce idNonce seq with
    | .error _ => failWith "makeWhoareyou refuses"
    | .ok (packet, challenge) =>
      s!"{hex packet} {hex challenge}" === want
      packet.size === 63
      match Discv5.readWhoareyou dest packet with
      | .error _ => failWith "readWhoareyou refuses"
      | .ok c =>
        s!"{hexv c.nonce} {hexv c.idNonce} {c.enrSeq.toNat} {hex c.challengeData}" ===
          s!"{hexv nonce} {hexv idNonce} {seq.toNat} {hex challenge}"
    classify "the sequence number 0" (seq == 0)

/-- Header fields of a packet that is a WHOAREYOU, another kind of packet, or neither.

A message packet has 32 bytes of authdata.

A handshake packet has 34 or more, here with an empty signature and an empty key. -/
def genChallengeFields : Gen (Nat × ByteArray × ByteArray) := do
  let body ← genBytes (.linear 16 30)
  let whole ← Gen.frequency [
    (6, (fun a => (1, a, ByteArray.empty)) <$> genBytes (.singleton 24)),
    (1, (fun a => (0, a, body)) <$> genBytes (.singleton 32)),
    (1, (fun a => (2, a ++ ⟨#[0, 0]⟩, body)) <$> genBytes (.singleton 32))]
  let (flag, authdata, message) := whole
  Gen.frequency [
    (5, pure whole),
    (1, (fun n => (flag, ⟨Array.replicate n 5⟩, message)) <$> Gen.element [0, 23, 25, 32, 34]),
    (1, (fun f => (f, authdata, message)) <$> Gen.element [0, 1, 2, 3, 255]),
    (1, pure (flag, authdata, body))]

/-- A packet read as a challenge gives the fields of the reference, or is refused.

Only a packet with the flag 1 is a challenge.

The packet may have another flag, another authdata size, a message, or one byte changed. -/
def whoareyouReads (oracle : Oracle) (long : Bool := true) : Property IO := propertyM do
  let dest ← forAllWith hexv (genVector 32)
  let (iv, nonce) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}")
    (Gen.zip (genVector 16) (genVector 12))
  let (flag, authdata, message) ← forAll genChallengeFields
  let change ← forAll (Gen.frequency [(2, pure none), (1, some <$> genChange)])
  pure do
    let made ← oracle.ask ["d5_write", hexv dest, hexv iv, toString flag, hexv nonce, hex authdata,
      hex message]
    let some packet := unhex? made | failWith s!"oracle: {made}"
    let packet := match change with
      | some change => mutate change packet
      | none => packet
    annotate s!"packet: {hex packet}"
    let read ← oracle.ask ["d5_read", hexv dest, hex packet]
    -- The reference reads any packet: a challenge is one with the flag 1.
    let want := match words read with
      | ["1", nonce, authdata, _, challenge] => s!"{nonce} {authdata} {challenge}"
      | _ => "error"
    let got := match Discv5.readWhoareyou dest packet with
      | .ok c => s!"{hexv c.nonce} {hexv c.idNonce}" ++
          s!"{hex ⟨(Base.natToBytes 8 c.enrSeq.toNat).toArray⟩} {hex c.challengeData}"
      | .error _ => "error"
    got === want
    let valid := flag == 1 && authdata.size == 24 && message.isEmpty && change.isNone
    cover 7 "valid as generated" (valid && want != "error")
    coverLong long 1 "mutated and still accepted by the reference" (!valid && want != "error")
    cover 5 "refused by the reference" (want == "error")
    cover 5 "a packet of another flag that the reference reads" (want == "error" && !refused read)

/-! ## Ordinary message packets -/

/-- A session key of 16 bytes. -/
def genKey : Gen (Vector UInt8 16) := genVector 16

/-- A plaintext: short, or of a length around the largest that fits a packet of 1280 bytes.

The packet has 16 + 23 + 32 bytes before the message, and the tag adds 16. -/
def genPlaintext : Gen ByteArray :=
  -- A long plaintext repeats one byte, so that a failing case has little to shrink.
  Gen.frequency [(1, pure .empty), (5, genBytes (.linear 1 80)),
    (2, Gen.zipWith (fun n (fill : UInt8) => ⟨Array.replicate n fill⟩)
      (Gen.nat (.constant 1190 1196)) genByte)]

/-- A message packet is the one of `discv5-wire.md`, and node B opens it with the key of node A.

A plaintext that makes the packet longer than 1280 bytes is refused by both. -/
def message (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith hexv genKey
  let (src, dest) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}")
    (Gen.zip (genVector 32) (genVector 32))
  let (iv, nonce) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}")
    (Gen.zip (genVector 16) (genVector 12))
  let plaintext ← forAllWith hex genPlaintext
  pure do
    let want ← oracle.ask ["d5_seal", hexv key, hexv src, hexv dest, hexv iv, hexv nonce,
      hex plaintext]
    match Discv5.sealMessage key src dest iv nonce plaintext with
    | .error _ => ensure (refused want) "EthLib refuses a message that the reference seals"
    | .ok packet =>
      hex packet === want
      -- Node B knows the key of node A only.
      let keyOf (id : Discv5.NodeId) := if id = src then some key else none
      match Discv5.openMessage keyOf dest packet with
      | .ok (from_, got) => s!"{hexv from_} {hex got}" === s!"{hexv src} {hex plaintext}"
      | .error _ => failWith "openMessage refuses"
    cover 3 "the packet would pass 1280 bytes" (refused want)
    cover 5 "a packet of 1270 bytes or more" (!refused want && plaintext.size ≥ 1183)
    classify "an empty plaintext" plaintext.isEmpty

/-- What node B holds for the source of a packet. -/
inductive Held where
  | theKey
  | anotherKey
  | noKey
  deriving Repr, BEq

/-- A packet opened as an ordinary message gives what the reference reads, or is refused.

Node B may hold another key or none, the packet may be for another node or of another flag.

One byte of it may be changed. -/
def messageReads (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith hexv genKey
  let (src, dest) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}")
    (Gen.zip (genVector 32) (genVector 32))
  let (iv, nonce) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}")
    (Gen.zip (genVector 16) (genVector 12))
  let plaintext ← forAllWith hex (genBytes (.linear 0 60))
  let held ← forAll (Gen.frequency [(6, pure Held.theKey), (1, pure .anotherKey), (1, pure .noKey)])
  let flag ← forAll (Gen.frequency [(8, pure 0), (1, pure 1), (1, pure 2)])
  let other ← forAll (Gen.frequency [(8, pure false), (1, pure true)])
  let change ← forAll (Gen.frequency [(3, pure none), (1, some <$> genChange)])
  pure do
    let made ← if flag == 0 then
        oracle.ask ["d5_seal", hexv key, hexv src, hexv dest, hexv iv, hexv nonce, hex plaintext]
      else
        -- A WHOAREYOU packet, or a handshake packet with empty signature and key.
        oracle.ask ["d5_write", hexv dest, hexv iv, toString flag, hexv nonce,
          if flag == 1 then hex ⟨Array.replicate 24 3⟩ else hexv src ++ "0000",
          if flag == 1 then "-" else hex plaintext]
    let some packet := unhex? made | failWith s!"oracle: {made}"
    let packet := match change with
      | some change => mutate change packet
      | none => packet
    let reader : Discv5.NodeId := if other then dest.set! 0 (dest[0]! ^^^ 1) else dest
    let theirs : Vector UInt8 16 := match held with
      | .anotherKey => key.set! 3 (key[3]! ^^^ 0x40)
      | _ => key
    annotate s!"packet: {hex packet}"
    let read ← oracle.ask ["d5_open", hexv theirs, hexv reader, hex packet]
    let want := if held == .noKey then "error" else verdict read
    let keyOf (_ : Discv5.NodeId) := if held == .noKey then none else some theirs
    let got := match Discv5.openMessage keyOf reader packet with
      | .ok (from_, got) => s!"{hexv from_} {hex got}"
      | .error _ => "error"
    got === want
    let valid := held == .theKey && flag == 0 && !other && change.isNone
    cover 7 "valid as generated" (valid && want != "error")
    cover 5 "refused by the reference" (want == "error")
    classify "mutated and still accepted by the reference" (!valid && want != "error")
    classify "another key" (held == .anotherKey)
    classify "no key" (held == .noKey)
    classify "another flag" (flag != 0)
    classify "a byte changed" change.isSome

/-! ## Step 4 of the handshake -/

/-- An ephemeral public key in a form that node A might send. -/
inductive KeyForm where
  | compressed
  | uncompressed
  | changed (at_ : Nat)
  | prefixed (first : UInt8)
  | short
  | none
  deriving Repr, BEq

/-- The bytes of an ephemeral key in a form. -/
def KeyForm.bytes (form : KeyForm) (ephemeral : Nat) : ByteArray :=
  let point := publicOf ephemeral
  let compressed := point.encodeCompressed
  match form with
  | .compressed => compressed
  | .uncompressed => ⟨#[4]⟩ ++ ⟨(Rlpx.encodePublicKey point).toArray⟩
  | .changed at_ => compressed.set! (1 + at_ % 32) (compressed[1 + at_ % 32]! ^^^ 1)
  | .prefixed first => compressed.set! 0 first
  | .short => compressed.extract 0 32
  | .none => .empty

/-- Node B derives the session keys of `discv5-theory.md`, or refuses the handshake.

The ephemeral key comes in every form: compressed, uncompressed, off the curve, cut.

The ID signature is over those very bytes, by node A or by another key, or it is changed.

The reference derives the keys with the HKDF of `cryptography`. -/
def accepts (oracle : Oracle) : Property IO := propertyM do
  let (staticA, staticB) ← forAll (Gen.zip genSecret genSecret)
  let (ephemeral, other) ← forAll (Gen.zip genSecret genSecret)
  let challenge ← forAllWith hex (genBytes (.linear 0 70))
  let (idA, idB) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}")
    (Gen.zip (genVector 32) (genVector 32))
  let form ← forAll (Gen.frequency [(5, pure KeyForm.compressed), (1, pure .uncompressed),
    (2, KeyForm.changed <$> Gen.nat (.constant 0 31)),
    (1, KeyForm.prefixed <$> Gen.element [0, 1, 4, 5, 6, 7]), (1, pure .short), (1, pure .none)])
  let fault ← forAll (Gen.frequency [(5, pure "none"), (1, pure "flip"), (1, pure "otherSigner")])
  pure do
    let eph := form.bytes ephemeral
    let signer := if fault == "otherSigner" then other else staticA
    let made ← oracle.ask ["d5_idsign", secretHex signer, hex challenge, hex eph, hexv idB]
    let some sig := unhex? made | failWith s!"oracle: {made}"
    let sig := if fault == "flip" then sig.set! 7 (sig[7]! ^^^ 2) else sig
    let pubA := publicOf staticA
    let want ← oracle.ask ["d5_accept", secretHex staticB, hex challenge, hexv idA, hexv idB,
      hex pubA.encodeCompressed, hex eph, hex sig]
    let accepted := Discv5.acceptHandshake (Fin.ofNat _ staticB) challenge idA idB pubA eph sig
    let got := match accepted with
      | .ok keys => s!"{hex keys.initiatorKey} {hex keys.recipientKey}"
      | .error _ => "error"
    got === verdict want
    if form == .compressed && fault == "none" then
      -- Node A derives the same keys from its side.
      match Discv5.initiateHandshake (Fin.ofNat _ ephemeral) (Fin.ofNat _ staticA) challenge idA idB
        (publicOf staticB) with
      | .ok init => s!"{hex init.keys.initiatorKey} {hex init.keys.recipientKey}" === got
      | .error e => failWith s!"initiateHandshake refuses: {repr e}"
    let valid := form == .compressed && fault == "none"
    cover 7 "valid as generated" (valid && !refused want)
    cover 1 "mutated and still accepted by the reference" (!valid && !refused want)
    cover 5 "refused by the reference" (refused want)
    classify "a signed key that is not a compressed point" (fault == "none" && refused want)

/-! ## discv4: the record of an ENRResponse -/

/-- A record to check: who signs it, under which scheme, with what changed, and how large. -/
structure Signed where
  signer : Nat
  sender : Nat
  seq : UInt64
  scheme : String
  tweak : String
  filler : Nat

instance : Repr Signed where
  reprPrec s _ := s!"signer {secretHex s.signer} sender {secretHex s.sender} seq {s.seq} " ++
    s!"scheme {s.scheme} tweak {s.tweak} filler {s.filler}"

/-- A record signed by the sender, or with one rule of EIP-778 or of discv4 broken.

The filler is a pair that takes the record to a size around the limit of 300 bytes. -/
def genSigned : Gen Signed := do
  let signer ← genSecret
  let sender ← Gen.frequency [(5, pure signer), (1, genSecret)]
  let scheme ← Gen.frequency [(8, pure "v4"), (1, Gen.element ["v5", "", "V4", "v4 "])]
  let tweak ← Gen.frequency [(6, pure "none"),
    (3, Gen.element ["flip", "high", "high", "short", "seq", "nokey"])]
  let filler ← Gen.frequency [(4, Gen.nat (.linear 0 60)), (2, Gen.nat (.constant 170 184))]
  pure ⟨signer, sender, ← genSeq, scheme, tweak, filler⟩

/-- A record is the sender's exactly when it is a valid "v4" record with the sender's key.

The reference reads the record as EIP-778 says and verifies it with libsecp256k1. -/
def recordSignedBy (oracle : Oracle) : Property IO := propertyM do
  let s ← forAll genSigned
  pure do
    let pairs := if s.filler == 0 then "-" else s!"7a={hex ⟨Array.replicate s.filler 0x11⟩}"
    let made ← oracle.ask ["enr_make", secretHex s.signer, toString s.seq.toNat,
      hex s.scheme.toUTF8, pairs, s.tweak]
    let some record := unhex? made | failWith s!"oracle: {made}"
    annotate s!"record of {record.size} bytes: {hex record}"
    let .ok item := Serialization.Rlp.decode record | failWith "the record is not RLP"
    let sender := publicOf s.sender
    let want ← oracle.ask ["enr_signed_by", hex record, hexv (Rlpx.encodePublicKey sender)]
    flag (Discv4.recordSignedBy sender item) === want
    let valid := s.signer == s.sender && s.scheme == "v4" && s.tweak == "none"
    cover 7 "valid as generated" (valid && want == "1")
    cover 1 "mutated and still accepted by the reference" (!valid && want == "1")
    cover 5 "refused by the reference" (want == "0")
    cover 3 "a valid record of more than 300 bytes" (valid && record.size > 300)
    classify "a record of 299 to 301 bytes" (299 ≤ record.size && record.size ≤ 301)
    classify "a high s" (s.tweak == "high")

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  [("discv5: WHOAREYOU is the packet of the specification", (whoareyou oracle).withTests cases),
   ("discv5: a packet read as a challenge",
     (whoareyouReads oracle (cases ≥ 1000)).withTests cases),
   ("discv5: a message packet is the specification's", (message oracle).withTests cases),
   ("discv5: a packet opened as a message", (messageReads oracle).withTests cases),
   ("discv5: node B accepts a handshake", (accepts oracle).withTests (min cases 300)),
   ("discv4: the record of an ENRResponse is the sender's",
     (recordSignedBy oracle).withTests (min cases 300))]

end DecodersProperty.Devp2p.Discv

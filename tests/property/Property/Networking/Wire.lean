import Hedgehog
import Support
import Property.Networking.Common
import EthLib.Networking.Discv5.Handshake
import EthLib.Networking.Discv5.Message
import EthLib.Networking.Discv5.Session
import EthLib.Networking.Rlpx.Frame

/-!
# discv5 and RLPx, on generated inputs

The reference is `oracle/networking_wire.py`.

It is written from `discv5-wire.md`, `discv5-theory.md` and `rlpx.md`.

It reproduces the test vectors of discv5 when it starts.
-/

open Hedgehog Support EthLib EthLib.Networking NetworkingProperty
open EthLib.Serialization.Rlp (Item)
open EthLib.Cryptography.Secp256k1 (Fn Point)

namespace NetworkingProperty.Wire

/-! ## discv5 -/

/-- Two node IDs: any two, or two that share a prefix of any length. -/
def genIdPair : Gen (Discv5.NodeId × Discv5.NodeId) := do
  let a ← genVector 32
  let b ← Gen.choice [genVector 32,
    (fun (i, x) => a.set! (i % 32) (a[i % 32]! ^^^ x)) <$>
      Gen.zip (Gen.nat (.constant 0 31)) (Gen.element [0, 1, 2, 0x40, 0x80, 0xff])]
  pure (a, b)

/-- The logarithmic distance is the bit length of the XOR. -/
def distance (oracle : Oracle) : Property IO := propertyM do
  let (a, b) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}") genIdPair
  pure do
    toString (Discv5.logDistance a b) === (← oracle.ask ["discv5_distance", hexv a, hexv b])

/-- The authdata of each flag, with a handshake of the sizes of "v4" and of other sizes. -/
def genAuthdata : Gen Discv5.Authdata :=
  Gen.choice [
    Discv5.Authdata.message <$> genVector 32,
    Gen.zipWith Discv5.Authdata.whoareyou (genVector 16) genUInt64,
    do
      let sig ← Gen.frequency [(3, genBytes (.singleton 64)), (1, genBytes (.linear 0 70))]
      let key ← Gen.frequency [(3, genBytes (.singleton 33)), (1, genBytes (.linear 0 40))]
      pure (.handshake (← genVector 32) sig key (← genBytes (.linear 0 60)))]

/-- A packet with its destination. -/
structure Sent where
  dest : Discv5.NodeId
  iv : Vector UInt8 16
  nonce : Vector UInt8 12
  authdata : Discv5.Authdata
  message : ByteArray

instance : Repr Sent where
  reprPrec s _ := s!"dest {hexv s.dest} iv {hexv s.iv} nonce {hexv s.nonce} flag " ++
    s!"{s.authdata.flag} authdata {hex ⟨s.authdata.encode.toArray⟩} message {hex s.message}"

/-- A packet of any flag; a WHOAREYOU packet has no message. -/
def genSent : Gen Sent := do
  let authdata ← genAuthdata
  let message ← if authdata.flag = 1 then pure .empty else genBytes (.linear 0 60)
  pure ⟨← genVector 32, ← genVector 16, ← genVector 12, authdata, message⟩

/-- A packet is masked as `discv5-wire.md` says. -/
def packetWrite (oracle : Oracle) : Property IO := propertyM do
  let s ← forAll genSent
  pure do
    let want ← oracle.ask ["discv5_write", hexv s.dest, hexv s.iv, toString s.authdata.flag,
      hexv s.nonce, hex ⟨s.authdata.encode.toArray⟩, hex s.message]
    answer (Discv5.Packet.encode s.dest ⟨s.iv, ⟨s.nonce, s.authdata⟩, s.message⟩) === want

/-- What EthLib reads of a packet, in the words of the reference. -/
def readPacket (dest : Discv5.NodeId) (bytes : ByteArray) : String :=
  match Discv5.Packet.decode dest bytes with
  | .error _ => "error"
  | .ok p => s!"{p.header.authdata.flag} {hexv p.header.nonce} " ++
      s!"{hex ⟨p.header.authdata.encode.toArray⟩} {hex p.message}"

/-- Raw header fields: a flag and authdata that may not fit each other. -/
def genRawPacket : Gen (Nat × ByteArray × ByteArray) := do
  let flag ← Gen.frequency [(3, pure 0), (3, pure 1), (4, pure 2), (1, pure 3), (1, pure 255)]
  let authdata ← Gen.frequency [
    (2, Gen.element [32, 24, 23, 25, 31, 33, 34] >>= fun n => genBytes (.singleton n)),
    (2, genBytes (.linear 0 140)),
    (4, do
      -- A handshake whose two sizes may run past the authdata.
      let sig ← Gen.element [0, 64, 65, 200, 255]
      let key ← Gen.element [0, 33, 34, 255]
      let body ← genBytes (.linear 0 110)
      let cut ← Gen.frequency [(3, pure (sig + key)), (1, pure (sig + key - 1)), (1, pure 0)]
      pure (⟨Array.replicate 32 7⟩ ++ ⟨#[UInt8.ofNat sig, UInt8.ofNat key]⟩ ++
        (⟨Array.replicate cut 9⟩ : ByteArray) ++ body))]
  let message ← Gen.frequency [(1, pure .empty), (3, genBytes (.linear 0 40))]
  pure (flag, authdata, message)

/-- A packet whose header fields may not fit reads as `discv5-wire.md` says, or is refused. -/
def packetRead (oracle : Oracle) : Property IO := propertyM do
  let dest ← forAllWith hexv (genVector 32)
  let (flag, authdata, message) ← forAll genRawPacket
  let cut ← forAll (Gen.frequency [(6, pure 0), (1, Gen.nat (.linear 1 40))])
  let flip ← forAll (Gen.frequency [(6, pure none), (1, some <$> Gen.nat (.constant 16 40))])
  pure do
    let made ← oracle.ask ["discv5_write", hexv dest, hex ⟨Array.replicate 16 3⟩, toString flag,
      hex ⟨Array.replicate 12 5⟩, hex authdata, hex message]
    let some bytes := unhex? made | failWith "oracle"
    let bytes := bytes.extract 0 (bytes.size - cut)
    let bytes := match flip with
      | some i => bytes.set! (i % bytes.size) (bytes[i % bytes.size]! ^^^ 0x21)
      | none => bytes
    annotate s!"packet: {hex bytes}"
    readPacket dest bytes === verdict (← oracle.ask ["discv5_read", hexv dest, hex bytes])

/-- The two ends of the size of a packet: 63 and 1280 bytes are read, 62 and 1281 are not.

The smallest packet is a WHOAREYOU packet, and a packet of 62 bytes is one cut by a byte. -/
def packetSize (oracle : Oracle) : Property IO := propertyM do
  let size ← forAll (Gen.element [62, 63, 1279, 1280, 1281])
  pure do
    let dest : Discv5.NodeId := Vector.replicate 32 1
    let (flag, authdata, message) : String × Nat × Nat :=
      if size < 71 then ("1", size - 39, 0) else ("0", 32, size - 71)
    let made ← oracle.ask ["discv5_write", hexv dest, hex ⟨Array.replicate 16 3⟩, flag,
      hex ⟨Array.replicate 12 5⟩, hex ⟨Array.replicate authdata 2⟩, hex ⟨Array.replicate message 4⟩]
    let some bytes := unhex? made | failWith "oracle"
    bytes.size === size
    let got := readPacket dest bytes
    got === verdict (← oracle.ask ["discv5_read", hexv dest, hex bytes])
    (got != "error") === (size == 63 || size == 1279 || size == 1280)

/-- The handshake: keys, ID signature and the whole packet are those of the specification.

Node B then opens the packet to the same keys and the plaintext. -/
def handshake (oracle : Oracle) : Property IO := propertyM do
  let (ephemeral, staticA) ← forAll (Gen.zip genSecret genSecret)
  let staticB ← forAll genSecret
  let challenge ← forAllWith hex (genBytes (.linear 0 70))
  let (idA, idB) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}") (Gen.zip (genVector 32)
    (genVector 32))
  let (iv, nonce) ← forAllWith (fun (a, b) => s!"{hexv a} {hexv b}") (Gen.zip (genVector 16)
    (genVector 12))
  let (record, plaintext) ← forAll (Gen.zip (genBytes (.linear 0 50)) (genBytes (.linear 0 50)))
  pure do
    let pubB := publicOf staticB
    let ephPub := (publicOf ephemeral).encodeCompressed
    let keys ← oracle.ask ["discv5_keys", secretHex ephemeral, hex pubB.encodeCompressed,
      hex challenge, hexv idA, hexv idB]
    let sig ← oracle.ask ["discv5_idsign", secretHex staticA, hex challenge, hex ephPub, hexv idB]
    let .ok init := Discv5.initiateHandshake (Fin.ofNat _ ephemeral) (Fin.ofNat _ staticA)
      challenge idA idB pubB | failWith "initiateHandshake"
    let [_, initiator, recipient] := keys.splitOn " " | failWith "oracle"
    hex init.keys.initiatorKey === initiator
    hex init.keys.recipientKey === recipient
    hex init.idSignature === sig
    hex init.ephemeralPubkey === hex ephPub
    -- The packet: the authdata, the encrypted message, then the masking.
    let authdata := hexv idA ++ "4021" ++ sig ++ hex ephPub ++
      (if record.isEmpty then "" else hex record)
    let size := (authdata.length / 2)
    let header := "646973637635" ++ "0001" ++ "02" ++ hexv nonce ++
      hex ⟨(Base.natToBytes 2 size).toArray⟩ ++ authdata
    let message ← oracle.ask ["discv5_gcm", initiator, hexv nonce, hex plaintext, hexv iv ++ header]
    let want ← oracle.ask ["discv5_write", hexv idB, hexv iv, "2", hexv nonce, authdata, message]
    let sealed := Discv5.sealHandshake (Fin.ofNat _ ephemeral) (Fin.ofNat _ staticA) challenge
      idA idB pubB iv nonce record plaintext
    answer (sealed.map (·.1)) === want
    let .ok (packet, _) := sealed | failWith "sealHandshake"
    match Discv5.openHandshake (Fin.ofNat _ staticB) challenge idB (publicOf staticA) packet with
    | .error _ => failWith "node B does not open the packet"
    | .ok got =>
      hex got.message === hex plaintext
      hex got.record === hex record
      hex got.keys.initiatorKey === initiator
      hex got.keys.recipientKey === recipient
    -- Node B refuses the packet under another challenge or another key of node A.
    ensure (Discv5.openHandshake (Fin.ofNat _ staticB) (challenge.push 0) idB (publicOf staticA)
      packet).toOption.isNone "another challenge is accepted"
    ensure (staticA + 1 == Fn.modulus ||
      (Discv5.openHandshake (Fin.ofNat _ staticB) challenge idB (publicOf (staticA + 1))
        packet).toOption.isNone) "another key of node A is accepted"

/-- An ID signature that is changed verifies exactly when libsecp256k1 says so. -/
def idVerify (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let challenge ← forAllWith hex (genBytes (.linear 0 40))
  let ephPub ← forAllWith hex (genBytes (.linear 0 34))
  let idB ← forAllWith hexv (genVector 32)
  let change ← forAll (Gen.element ["none", "flip", "high", "short", "long", "zero"])
  let at_ ← forAll (Gen.nat (.constant 0 63))
  pure do
    let .ok sig := Discv5.idSign (Fin.ofNat _ sk) challenge ephPub idB | failWith "idSign"
    let s := Base.bytesToNat (sig.toList.drop 32)
    let sig : ByteArray := match change with
      | "flip" => sig.set! at_ (sig[at_]! ^^^ 4)
      | "high" => ⟨(sig.toList.take 32 ++ Base.natToBytes 32 (Fn.modulus - s)).toArray⟩
      | "short" => sig.extract 0 63
      | "long" => sig.push 0
      | "zero" => ⟨(sig.toList.take 32 ++ List.replicate 32 0).toArray⟩
      | _ => sig
    let pub := publicOf sk
    let want ← oracle.ask ["discv5_idverify", hex pub.encodeCompressed, hex challenge, hex ephPub,
      hexv idB, hex sig]
    (if Discv5.idVerify pub challenge ephPub idB sig then "1" else "0") === want

/-- A request ID: up to 8 bytes, and now and then 9. -/
def genRequestId : Gen ByteArray :=
  Gen.frequency [(8, genBytes (.linear 0 8)), (1, genBytes (.singleton 9))]

/-- Distances around the ends of their range. -/
def genDistances : Gen (List Nat) :=
  Gen.list (.linear 0 4) (Gen.frequency [(4, Gen.nat (.constant 1 256)),
    (1, Gen.element [0, 256, 257, 65536])])

/-- A message of each of the ten types. -/
def genMessage : Gen Discv5.Message :=
  let ip := Gen.frequency [(4, Gen.element [4, 16] >>= fun n => genBytes (.singleton n)),
    (1, Gen.element [0, 5, 15, 17] >>= fun n => genBytes (.singleton n))]
  let record : Gen Item := (fun b => Item.list [.bytes b]) <$> genBytes (.linear 0 6)
  Gen.choice [
    Gen.zipWith .ping genRequestId genUInt64,
    do pure (.pong (← genRequestId) (← genUInt64) (← ip) (UInt16.ofNat (← genNatBits 16))),
    Gen.zipWith .findnode genRequestId genDistances,
    do pure (.nodes (← genRequestId) (← genUInt64) (← Gen.list (.linear 0 3) record)),
    do pure (.talkreq (← genRequestId) (← genBytes (.linear 0 9)) (← genBytes (.linear 0 9))),
    Gen.zipWith .talkresp genRequestId (genBytes (.linear 0 9)),
    do pure (.regtopic (← genRequestId) (← genVector 32) (← record) (← genBytes (.linear 0 9))
      (← genDistances)),
    do pure (.regconfirmation (← genRequestId) (← genUInt64) (← genBytes (.linear 0 9))
      (← genUInt64)),
    do pure (.topicquery (← genRequestId) (← genVector 32) (← genDistances)),
    do pure (.topicnodes (← genRequestId) (← genUInt64) (← Gen.list (.linear 0 3) record))]

/-- A field of the wrong shape or size. -/
def genOddField : Gen Item :=
  Gen.element [.bytes .empty, .list [], .bytes ⟨#[0]⟩, .bytes ⟨#[0, 1]⟩, .bytes ⟨#[1, 0, 0]⟩,
    .bytes ⟨Array.replicate 9 1⟩, .bytes ⟨Array.replicate 31 1⟩, .bytes ⟨Array.replicate 33 1⟩,
    .list [.bytes ⟨#[1, 1]⟩], .list [.bytes ⟨#[0]⟩], .list [.list []], .bytes ⟨#[1, 0]⟩]

/-- A message with one thing changed reads as `discv5-wire.md` says, or is refused. -/
def message (oracle : Oracle) : Property IO := propertyM do
  let m ← forAllWith (fun m => s!"{m.type} {showItem (.list m.fields)}") genMessage
  let change ← forAll (Gen.frequency [(4, pure 0), (3, pure 1), (1, pure 2), (1, pure 3),
    (1, pure 4), (1, pure 5)])
  let (at_, item) ← forAll (Gen.zip (Gen.nat (.constant 0 4)) genOddField)
  let type ← forAll (Gen.element [(0 : UInt8), 1, 4, 10, 11, 255])
  pure do
    let fields := m.fields
    let (t, body) : UInt8 × ByteArray := match change with
      | 1 => (m.type,
        rlp (.list (fields.mapIdx fun j f => if j = at_ % fields.length then item else f)))
      | 2 => (m.type, rlp (.list (fields ++ [item])))
      | 3 => (m.type, rlp (.list fields.dropLast))
      | 4 => (type, rlp (.list fields))
      | 5 => (m.type, rlp (.list fields) ++ ⟨#[0]⟩)
      | _ => (m.type, rlp (.list fields))
    let bytes := (⟨#[t]⟩ : ByteArray) ++ body
    annotate s!"plaintext: {hex bytes}"
    let got := match Discv5.Message.decode bytes with
      | .error _ => "error"
      | .ok m => s!"{m.type} {hex (rlp (.list m.fields))}"
    got === verdict (← oracle.ask ["discv5_msg", hex bytes])
    if change = 0 then
      answer (m.encode.mapError fun _ => ()) === hex bytes

/-! ## RLPx -/

/-- ECIES: the ciphertext is the one of `rlpx.md`, and a changed one opens as the reference. -/
def ecies (oracle : Oracle) : Property IO := propertyM do
  let (sk, r) ← forAll (Gen.zip genSecret genSecret)
  let iv ← forAllWith hexv (genVector 16)
  let (shared, m) ← forAll (Gen.zip (genBytes (.linear 0 4)) (genBytes (.linear 0 70)))
  let change ← forAll (Gen.frequency [(3, pure none), (2, some <$> Gen.nat (.linear 0 200))])
  let first ← forAll (Gen.frequency [(6, pure none),
    (1, some <$> Gen.element [(0 : UInt8), 2, 3, 6, 7])])
  let cut ← forAll (Gen.frequency [(6, pure 0), (1, Gen.nat (.linear 1 120))])
  pure do
    let pub := publicOf sk
    let pub64 := hexv (Rlpx.encodePublicKey pub)
    let want ← oracle.ask ["ecies_enc", pub64, secretHex r, hexv iv, hex shared, hex m]
    let got := Rlpx.Ecies.encrypt pub (Fin.ofNat _ r) iv shared m
    answer got === want
    let .ok ct := got | failWith "encrypt"
    let ct := match change with
      | some i => ct.set! (i % ct.size) (ct[i % ct.size]! ^^^ 0x02)
      | none => ct
    let ct := match first with
      | some b => ct.set! 0 b
      | none => ct
    let ct := ct.extract 0 (ct.size - cut)
    annotate s!"ciphertext: {hex ct}"
    answer (Rlpx.Ecies.decrypt (Fin.ofNat _ sk) shared ct) ===
      verdict (← oracle.ask ["ecies_dec", secretHex sk, hex shared, hex ct])

/-- The `auth` packet of EthLib is read by the reference to the initiator's keys and nonce. -/
def auth (oracle : Oracle) : Property IO := propertyM do
  let (staticA, ephemeralA) ← forAll (Gen.zip genSecret genSecret)
  let (staticB, r) ← forAll (Gen.zip genSecret genSecret)
  let nonce ← forAllWith hexv (genVector 32)
  let iv ← forAllWith hexv (genVector 16)
  let padding ← forAll (genBytes (.linear 0 120))
  pure do
    let keys : Rlpx.Keys := ⟨Fin.ofNat _ staticA, Fin.ofNat _ ephemeralA, nonce⟩
    let .ok packet := Rlpx.makeAuth keys (publicOf staticB) ⟨Fin.ofNat _ r, iv, padding⟩
      | failWith "makeAuth"
    let want := s!"{hexv (Rlpx.encodePublicKey (publicOf staticA))} {hexv nonce} 4 " ++
      hexv (Rlpx.encodePublicKey (publicOf ephemeralA))
    (← oracle.ask ["rlpx_auth", secretHex staticB, hex packet]) === want
    match Rlpx.readAuth (Fin.ofNat _ staticB) packet with
    | .error _ => failWith "readAuth"
    | .ok (msg, remoteStatic, remoteEphemeral) =>
      ensure (msg.initiatorNonce == nonce && remoteStatic == publicOf staticA &&
        remoteEphemeral == publicOf ephemeralA) "readAuth reads other values"

/-- One side of a session: its role, the handshake values and the packets. -/
structure Session where
  initiator : Bool
  ephemeral : Vector UInt8 32
  initiatorNonce : Vector UInt8 32
  recipientNonce : Vector UInt8 32
  auth : ByteArray
  ack : ByteArray

instance : Repr Session where
  reprPrec s _ := s!"initiator {s.initiator} eph {hexv s.ephemeral} inonce " ++
    s!"{hexv s.initiatorNonce} rnonce {hexv s.recipientNonce} auth {hex s.auth} ack {hex s.ack}"

/-- A session with any values: the secrets are a function of them. -/
def genSession : Gen Session := do
  pure ⟨← Gen.bool, ← genVector 32, ← genVector 32, ← genVector 32, ← genBytes (.linear 0 40),
    ← genBytes (.linear 0 40)⟩

/-- The secrets of the side. -/
def Session.secrets (s : Session) : Rlpx.Secrets :=
  Rlpx.deriveSecrets s.initiator s.ephemeral s.initiatorNonce s.recipientNonce s.auth s.ack

/-- Frame data of the lengths around a block: 0, 15, 16, 17 and more. -/
def genFrameData : Gen ByteArray :=
  Gen.frequency [(3, genBytes (.linear 0 50)),
    (1, Gen.element [0, 1, 15, 16, 17, 32, 33] >>= fun n => genBytes (.singleton n))]

/-- The frames that one side writes in a row are those of `rlpx.md`, with the same secrets. -/
def frames (oracle : Oracle) : Property IO := propertyM do
  let s ← forAll genSession
  let datas ← forAll (Gen.list (.linear 1 6) genFrameData)
  pure do
    let secrets := s.secrets
    let mut state := secrets.egress
    let mut out := ByteArray.empty
    for data in datas do
      let .ok (frame, next) := Rlpx.writeFrame state data | failWith "writeFrame"
      out := out ++ frame
      state := next
    let want ← oracle.ask ["rlpx_session", if s.initiator then "1" else "0", hexv s.ephemeral,
      hexv s.initiatorNonce, hexv s.recipientNonce, hex s.auth, hex s.ack,
      ",".intercalate (datas.map hex)]
    s!"{hexv secrets.aesSecret} {hexv secrets.macSecret} {hex out}" === want

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  let slow := min cases 200
  [("discv5: the logarithmic distance", (distance oracle).withTests cases),
   ("discv5: a packet is masked as the specification says", (packetWrite oracle).withTests cases),
   ("discv5: a packet with header fields that may not fit", (packetRead oracle).withTests cases),
   ("discv5: the sizes 63 and 1280", (packetSize oracle).withTests (min cases 30)),
   ("discv5: the handshake packet and its keys", (handshake oracle).withTests slow),
   ("discv5: a changed ID signature", (idVerify oracle).withTests slow),
   ("discv5: a message with one thing changed", (message oracle).withTests cases),
   ("rlpx: ECIES", (ecies oracle).withTests slow),
   ("rlpx: the reference reads auth", (auth oracle).withTests slow),
   ("rlpx: the frames of one side", (frames oracle).withTests cases)]

end NetworkingProperty.Wire

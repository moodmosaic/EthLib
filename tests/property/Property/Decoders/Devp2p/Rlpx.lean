import Hedgehog
import Support
import Property.Decoders.Devp2p.Common
import EthLib.Networking.Rlpx.Frame

/-!
# The handshake of RLPx, on generated inputs

The reference is written from `rlpx.md`: ECIES, the two packets and the secrets.

It uses libsecp256k1 for the curve, `cryptography` for AES, and the `rlp` package.
-/

open Hedgehog Support EthLib EthLib.Networking
open EthLib.Serialization.Rlp (Item)
open EthLib.Cryptography.Secp256k1 (Fn Point)

namespace DecodersProperty.Devp2p.Rlpx

open DecodersProperty DecodersProperty.Devp2p

/-- The 64 bytes of the public key of a private key, in hexadecimal. -/
def public64 (sk : Nat) : String := hexv (Rlpx.encodePublicKey (publicOf sk))

/-- The secret inputs of one side, and the randomness of its one packet. -/
structure Side where
  static : Nat
  ephemeral : Nat
  nonce : Vector UInt8 32
  r : Nat
  iv : Vector UInt8 16
  padding : ByteArray

instance : Repr Side where
  reprPrec s _ := s!"static {secretHex s.static} ephemeral {secretHex s.ephemeral} nonce " ++
    s!"{hexv s.nonce} r {secretHex s.r} iv {hexv s.iv} padding {hex s.padding}"

/-- A side with any keys, and a padding of any small length, none included. -/
def genSide : Gen Side := do
  let (static, ephemeral) ← Gen.zip genSecret genSecret
  let padding ← Gen.frequency [(1, pure .empty), (3, genBytes (.linear 1 200))]
  pure ⟨static, ephemeral, ← genVector 32, ← genSecret, ← genVector 16, padding⟩

/-- The keys of a side, as EthLib takes them. -/
def Side.keys (s : Side) : Rlpx.Keys := ⟨Fin.ofNat _ s.static, Fin.ofNat _ s.ephemeral, s.nonce⟩

/-- The randomness of a side, as EthLib takes it. -/
def Side.sealing (s : Side) : Rlpx.Sealing := ⟨Fin.ofNat _ s.r, s.iv, s.padding⟩

/-! ## The ack packet -/

/-- EthLib's ack is the reference's packet, byte for byte, and both read it back. -/
def ackWrites (oracle : Oracle) : Property IO := propertyM do
  let b ← forAll genSide
  let staticA ← forAllWith secretHex genSecret
  pure do
    let .ok packet := Rlpx.makeAck b.keys (publicOf staticA) b.sealing | failWith "makeAck"
    let body : Item := .list [.bytes ⟨(Rlpx.encodePublicKey (publicOf b.ephemeral)).toArray⟩,
      .bytes ⟨b.nonce.toArray⟩, natItem 4]
    hex packet === (← oracle.ask ["rlpx_ack_make", public64 staticA, secretHex b.r, hexv b.iv,
      itemText body, hex b.padding, "0"])
    let want := s!"{public64 b.ephemeral} {hexv b.nonce} 4"
    (← oracle.ask ["rlpx_ack_read", secretHex staticA, hex packet]) === want
    match Rlpx.readAck (Fin.ofNat _ staticA) packet with
    | .error e => failWith s!"readAck refuses: {repr e}"
    | .ok (msg, ephemeral) =>
      s!"{hexv msg.ephemeralPubkey} {hexv msg.recipientNonce} {msg.version}" === want
      ensure (ephemeral == publicOf b.ephemeral) "readAck gives another ephemeral key"
    classify "no padding" b.padding.isEmpty

/-- An ack to read: the body before it is sealed, and what is done to the packet after. -/
structure Ack where
  body : Item
  padding : ByteArray
  delta : Int
  change : Option (Nat × Nat × UInt8)
  tweaked : Bool

instance : Repr Ack where
  reprPrec a _ := s!"body {itemText a.body} padding {hex a.padding} delta {a.delta} " ++
    s!"change {repr a.change}"

/-- A field of an ack of the wrong shape or size, or a version that is not 4. -/
def genAckField : Gen Item :=
  Gen.element [.bytes .empty, .list [], .bytes ⟨#[0]⟩, .bytes ⟨#[0, 4]⟩, .bytes ⟨#[5]⟩,
    .bytes ⟨#[0xff]⟩, .bytes ⟨#[1, 0]⟩, .bytes ⟨Array.replicate 9 0xff⟩,
    .bytes ⟨Array.replicate 31 1⟩, .bytes ⟨Array.replicate 32 1⟩, .bytes ⟨Array.replicate 33 1⟩,
    .bytes ⟨Array.replicate 63 1⟩, .bytes ⟨Array.replicate 64 1⟩, .bytes ⟨Array.replicate 65 1⟩,
    .list [.bytes ⟨#[4]⟩]]

/-- The body of an ack as it should be, or with one thing changed. -/
def genAck (ephemeral : Nat) : Gen Ack := do
  let nonce ← genBytes (.singleton 32)
  let fields : List Item :=
    [.bytes ⟨(Rlpx.encodePublicKey (publicOf ephemeral)).toArray⟩, .bytes nonce, natItem 4]
  let padding ← Gen.frequency [(1, pure .empty), (2, genBytes (.linear 1 60))]
  let plain : Ack := ⟨.list fields, padding, 0, none, false⟩
  Gen.frequency [
    (4, pure plain),
    (4, do
      let at_ ← Gen.nat (.constant 0 2)
      let odd ← genAckField
      pure { plain with tweaked := true, body := .list (fields.set at_ odd) }),
    (2, (fun more => { plain with tweaked := true, body := .list (fields ++ more) }) <$>
      Gen.list (.constant 1 3) genAckField),
    (1, pure { plain with tweaked := true, body := .list fields.dropLast }),
    (1, pure { plain with tweaked := true, body := .bytes nonce }),
    (1, (fun delta => { plain with tweaked := true, delta }) <$> Gen.element [(1 : Int), -1, 256]),
    (3, (fun change => { plain with tweaked := true, change := some change }) <$> genChange)]

/-- An ack with a field of another shape, more or fewer fields, another size, or a changed byte.

The initiator reads what `rlpx.md` says, or refuses the packet. -/
def ackReads (oracle : Oracle) : Property IO := propertyM do
  let (staticA, ephemeral) ← forAll (Gen.zip genSecret genSecret)
  let (r, iv) ← forAllWith (fun (r, iv) => s!"{secretHex r} {hexv iv}")
    (Gen.zip genSecret (genVector 16))
  let a ← forAll (genAck ephemeral)
  pure do
    let made ← oracle.ask ["rlpx_ack_make", public64 staticA, secretHex r, hexv iv,
      itemText a.body, hex a.padding, toString a.delta]
    let some packet := unhex? made | failWith s!"oracle: {made}"
    let packet := match a.change with
      | some change => mutate change packet
      | none => packet
    annotate s!"packet: {hex packet}"
    let want ← oracle.ask ["rlpx_ack_read", secretHex staticA, hex packet]
    let got := match Rlpx.readAck (Fin.ofNat _ staticA) packet with
      | .ok (msg, _) => s!"{hexv msg.ephemeralPubkey} {hexv msg.recipientNonce} {msg.version}"
      | .error _ => "error"
    got === verdict want
    cover 7 "valid as generated" (!a.tweaked && !refused want)
    cover 1 "mutated and still accepted by the reference" (a.tweaked && !refused want)
    cover 5 "refused by the reference" (refused want)
    classify "a byte of the packet changed" a.change.isSome

/-- The ack of before EIP-8 has no size and a fixed plaintext, and EthLib refuses it.

The module says so: "EthLib reads only this form, and rejects the older fixed-size form". -/
def ackOld (oracle : Oracle) : Property IO := propertyM do
  let (staticA, ephemeral) ← forAll (Gen.zip genSecret genSecret)
  let (r, iv) ← forAllWith (fun (r, iv) => s!"{secretHex r} {hexv iv}")
    (Gen.zip genSecret (genVector 16))
  let nonce ← forAllWith hexv (genVector 32)
  pure do
    let made ← oracle.ask ["rlpx_ack_old", public64 staticA, secretHex r, hexv iv,
      public64 ephemeral, hexv nonce]
    let some packet := unhex? made | failWith s!"oracle: {made}"
    packet.size === 210
    ensure (Rlpx.readAck (Fin.ofNat _ staticA) packet).toOption.isNone
      "the old form of ack is read"

/-! ## The auth packet -/

/-- The names of the changes that the reference makes to the body of an auth. -/
def authTweaks : List String :=
  ["extra", "fewer", "version-", "version05", "versionff", "version0100", "version00",
    "version0004", "versionlist", "recid", "otherid", "sigflip", "highs", "zeros", "sigshort",
    "nonceshort", "noncelong", "offcurve", "otherkey", "keyshort", "bytes", "sizeup", "sizedown"]

/-- An auth with one field changed before it is sealed reads as `rlpx.md` says, or is refused.

A changed signature that still recovers a key must recover the key libsecp256k1 recovers. -/
def authReads (oracle : Oracle) : Property IO := propertyM do
  let a ← forAll genSide
  let staticB ← forAllWith secretHex genSecret
  let tweak ← forAll (Gen.frequency [(1, pure "none"), (3, Gen.element authTweaks)])
  let change ← forAll (Gen.frequency [(5, pure none), (1, some <$> genChange)])
  pure do
    let made ← oracle.ask ["rlpx_auth_make", secretHex a.static, secretHex a.ephemeral,
      hexv a.nonce, public64 staticB, secretHex a.r, hexv a.iv, hex a.padding, tweak]
    let some packet := unhex? made | failWith s!"oracle: {made}"
    if tweak == "none" then
      -- The reference's auth is EthLib's, byte for byte.
      match Rlpx.makeAuth a.keys (publicOf staticB) a.sealing with
      | .ok ours => hex ours === hex packet
      | .error e => failWith s!"makeAuth refuses: {repr e}"
    let packet := match change with
      | some change => mutate change packet
      | none => packet
    annotate s!"packet: {hex packet}"
    let want ← oracle.ask ["rlpx_auth_read", secretHex staticB, hex packet]
    let got := match Rlpx.readAuth (Fin.ofNat _ staticB) packet with
      | .ok (msg, remoteStatic, remoteEphemeral) =>
        if Rlpx.encodePublicKey remoteStatic != msg.initiatorPubkey then "another static key"
        else s!"{hexv msg.initiatorPubkey} {hexv msg.initiatorNonce} {msg.version} " ++
          hexv (Rlpx.encodePublicKey remoteEphemeral)
      | .error _ => "error"
    got === verdict want
    let valid := tweak == "none" && change.isNone
    cover 7 "valid as generated" (valid && !refused want)
    cover 1 "mutated and still accepted by the reference" (!valid && !refused want)
    cover 5 "refused by the reference" (refused want)
    classify "accepted with another ephemeral key than the initiator's"
      (!refused want && !want.endsWith (public64 a.ephemeral))

/-! ## The secrets -/

/-- The MAC of a state as 16 bytes, in hexadecimal. -/
def macHex (h : Cryptography.Hash.Keccak.Hasher256) : String := hex (Rlpx.macBytes h)

/-- Both sides of a handshake derive the secrets of `rlpx.md`, each from its own keys.

The reference derives them from the private keys of both, and checks what the packets hold.

A frame that one side then writes is read by the other. -/
def secrets (oracle : Oracle) : Property IO := propertyM do
  let a ← forAll genSide
  let b ← forAll genSide
  let data ← forAllWith hex (genBytes (.linear 0 40))
  pure do
    let .ok auth := Rlpx.makeAuth a.keys (publicOf b.static) a.sealing | failWith "makeAuth"
    let .ok (ack, secretsB) := Rlpx.respond b.keys b.sealing auth | failWith "respond"
    let .ok secretsA := Rlpx.finish a.keys auth ack | failWith "finish"
    let want ← oracle.ask ["rlpx_secrets", secretHex a.static, secretHex a.ephemeral, hexv a.nonce,
      secretHex b.static, secretHex b.ephemeral, hexv b.nonce, hex auth, hex ack]
    let [aes, mac, initiatorEgress, recipientEgress] := words want | failWith s!"oracle: {want}"
    let side (s : Rlpx.Secrets) : String :=
      s!"{hexv s.aesSecret} {hexv s.macSecret} {macHex s.egressMac} {macHex s.ingressMac}"
    side secretsA === s!"{aes} {mac} {initiatorEgress} {recipientEgress}"
    side secretsB === s!"{aes} {mac} {recipientEgress} {initiatorEgress}"
    -- The ack that the recipient made is the one `makeAck` makes.
    (Rlpx.makeAck b.keys (publicOf a.static) b.sealing).toOption.map hex === some (hex ack)
    for (writer, reader) in [(secretsA, secretsB), (secretsB, secretsA)] do
      let .ok (frame, _) := Rlpx.writeFrame writer.egress data | failWith "writeFrame"
      match Rlpx.readFrame reader.ingress frame with
      | .ok (got, _, rest) =>
        hex got === hex data
        hex rest === "-"
      | .error e => failWith s!"readFrame refuses: {repr e}"
    classify "no padding in auth" a.padding.isEmpty
    classify "no padding in ack" b.padding.isEmpty

/-- A packet with one byte changed is refused by the side that reads it.

The whole packet is authenticated: the size as shared data, the rest by the tag of ECIES. -/
def changed (oracle : Oracle) : Property IO := propertyM do
  let a ← forAll genSide
  let b ← forAll genSide
  let ofAuth ← forAll Gen.bool
  let change ← forAll genChange
  pure do
    let .ok auth := Rlpx.makeAuth a.keys (publicOf b.static) a.sealing | failWith "makeAuth"
    let .ok (ack, _) := Rlpx.respond b.keys b.sealing auth | failWith "respond"
    if ofAuth then
      let bad := mutate change auth
      let want ← oracle.ask ["rlpx_auth_read", secretHex b.static, hex bad]
      (Rlpx.respond b.keys b.sealing bad).toOption.isSome === !refused want
      ensure (bad == auth || refused want) "the reference reads a changed auth"
    else
      let bad := mutate change ack
      let want ← oracle.ask ["rlpx_ack_read", secretHex a.static, hex bad]
      (Rlpx.finish a.keys auth bad).toOption.isSome === !refused want
      ensure (bad == ack || refused want) "the reference reads a changed ack"
    cover 15 "a changed auth" ofAuth
    cover 17 "a changed ack" (!ofAuth)

/-- A packet of 65535 bytes after its size is written and read, and one byte more is refused. -/
def sizeLimit (oracle : Oracle) : Property IO := propertyM do
  let b ← forAll genSide
  let staticA ← forAllWith secretHex genSecret
  -- The body of an ack has 102 bytes, and ECIES adds 113.
  let over ← forAll (Gen.element [0, 1, 2])
  pure do
    let padding : ByteArray := ⟨Array.replicate (65535 - 113 - 102 - 1 + over) 7⟩
    let sealing : Rlpx.Sealing := ⟨Fin.ofNat _ b.r, b.iv, padding⟩
    match Rlpx.makeAck b.keys (publicOf staticA) sealing with
    | .ok packet =>
      ensure (over ≤ 1) "a packet past 16 bits is written"
      packet.size === 65535 + 2 - 1 + over
      (← oracle.ask ["rlpx_ack_read", secretHex staticA, hex packet]) ===
        s!"{public64 b.ephemeral} {hexv b.nonce} 4"
      ensure (Rlpx.readAck (Fin.ofNat _ staticA) packet).toOption.isSome "readAck refuses"
    | .error e => ensure (over == 2) s!"makeAck refuses: {repr e}"
    cover 1 "the largest packet" (over == 1)
    cover 5 "one byte more" (over == 2)

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  let slow := min cases 300
  [("rlpx: the reference reads and writes EthLib's ack", (ackWrites oracle).withTests slow),
   ("rlpx: an ack with one thing changed", (ackReads oracle).withTests cases),
   ("rlpx: the ack of before EIP-8 is refused, as documented",
     (ackOld oracle).withTests (min cases 50)),
   ("rlpx: an auth with one thing changed", (authReads oracle).withTests cases),
   ("rlpx: both sides derive the secrets of rlpx.md", (secrets oracle).withTests slow),
   ("rlpx: a packet with a changed byte is refused", (changed oracle).withTests slow),
   ("rlpx: the size limit of a packet", (sizeLimit oracle).withTests (min cases 20))]

end DecodersProperty.Devp2p.Rlpx

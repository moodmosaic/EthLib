import Hedgehog
import Support
import Property.Networking.Common
import EthLib.Networking.Encoding.Uvarint
import EthLib.Networking.Encoding.Varint
import EthLib.Networking.Quic.Keys
import EthLib.Networking.Quic.Packet
import EthLib.Networking.Quic.Protection
import EthLib.Networking.Quic.Varint

/-!
# Varints and QUIC, on generated inputs

The three varints of the layer against decoders written from their sources, and QUIC's integers,
packet numbers, keys and packet protection against aioquic.
-/

open Hedgehog Support EthLib EthLib.Networking

namespace NetworkingProperty.Codecs

open NetworkingProperty

/-- The words of an answer of the oracle. -/
def words (s : String) : List String := s.splitOn " "

/-! ## Base-128 varints -/

/-- The groups of a number, least significant first, with no continuation bits. -/
def groupsOf (n : Nat) : List Nat :=
  if n < 128 then [n] else n % 128 :: groupsOf (n / 128)
termination_by n
decreasing_by omega

/-- Groups as bytes: the continuation bit on every byte but the last. -/
def groupBytes (groups : List Nat) : List UInt8 :=
  groups.mapIdx fun i g => UInt8.ofNat (g % 128 + if i + 1 < groups.length then 128 else 0)

/-- A varint that is valid, or nearly: padded, too long, past 64 bits, cut, or followed. -/
def genVarintBytes : Gen (List UInt8) := do
  let value ← Gen.frequency [(6, genNatBits 64), (2, genNatBits 63), (1, genNatBits 70),
    (1, Gen.element [2 ^ 63 - 1, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 70 - 1])]
  let padding ← Gen.frequency [(6, pure 0), (2, Gen.nat (.constant 1 3)), (1, pure 10)]
  let bytes := groupBytes (groupsOf value ++ List.replicate padding 0)
  let cut ← Gen.frequency [(8, pure 0), (1, Gen.nat (.linear 0 3))]
  let tail ← Gen.frequency [(5, pure []), (1, genByteList (.linear 1 3))]
  pure (bytes.take (bytes.length - cut) ++ tail)

/-- The consensus varint: one minimal varint of a 64-bit value fills the input. -/
def pbVarint (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAll genVarintBytes
  pure do
    let want ← oracle.ask ["pb_varint", hex ⟨bytes.toArray⟩]
    match Encoding.Varint.decode bytes with
    | .ok v => toString v.toNat === want
    | .error _ => ensure (want.startsWith "error") s!"EthLib refuses, the reference reads {want}"

/-- A 64-bit value encodes to the bytes that the reference reads as that value. -/
def pbVarintEncode (oracle : Oracle) : Property IO := propertyM do
  let v ← forAll genUInt64
  pure do
    let bytes := Encoding.Varint.encode v
    (← oracle.ask ["pb_varint", hex ⟨bytes.toArray⟩]) === toString v.toNat
    tripping v Encoding.Varint.encode fun bs => (Encoding.Varint.decode bs).toOption

/-- The unsigned varint of libp2p: minimal, nine bytes at most, with the bytes after it. -/
def uvarint (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAll genVarintBytes
  pure do
    let want ← oracle.ask ["uvarint", hex ⟨bytes.toArray⟩]
    match Encoding.Uvarint.decode bytes with
    | .ok (v, rest) => s!"{v} {hex ⟨rest.toArray⟩}" === want
    | .error _ => ensure (want.startsWith "error") s!"EthLib refuses, the reference reads {want}"

/-! ## QUIC integers and packet numbers -/

/-- A QUIC integer near the edge of one of its four widths. -/
def genQuicValue : Gen Quic.Varint := do
  let n ← Gen.choice [genNatBits 6, genNatBits 14, genNatBits 30, genNatBits 62,
    Gen.element [63, 64, 16383, 16384, 2 ^ 30 - 1, 2 ^ 30, 2 ^ 62 - 1]]
  pure (Fin.ofNat _ n)

/-- Any bytes read as a QUIC integer as aioquic reads them. -/
def quicVarintDecode (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAllWith hex (genBytes (.linear 0 10))
  pure do
    let want ← oracle.ask ["quic_varint_dec", hex bytes]
    match Quic.Varint.decode bytes with
    | .ok (v, rest) => s!"{v.val} {hex rest}" === want
    | .error _ => ensure (want.startsWith "error") s!"EthLib refuses, the reference reads {want}"

/-- The shortest form is aioquic's, and every longer form reads as the same value. -/
def quicVarintEncode (oracle : Oracle) : Property IO := propertyM do
  let v ← forAll genQuicValue
  pure do
    hex (Quic.Varint.encode v) === (← oracle.ask ["quic_varint_enc", toString v.val])
    for w in List.finRange 4 do
      if h : v.val < Quic.Varint.capacity w then
        let bytes := Quic.Varint.encodeWith w v h
        bytes.size === 2 ^ w.val
        s!"{v.val} -" === (← oracle.ask ["quic_varint_dec", hex bytes])

/-- A packet number is reconstructed as RFC 9000 Appendix A.3 and aioquic do it. -/
def quicPacketNumber (oracle : Oracle) : Property IO := propertyM do
  let width ← forAll (Gen.element (List.finRange 4))
  let bits := 8 * (width.val + 1)
  -- The expected number is one past the largest, so it is at most 2^62.
  let expected ← forAll (Gen.choice [genNatBits 62, genNatBits 34, (2 ^ 62 - ·) <$> genNatBits 34,
    Gen.element [0, 1, 2 ^ 62 - 1, 2 ^ 62]])
  let truncated ← forAll (Gen.choice [genNatBits bits,
    (fun d => (expected + d) % 2 ^ bits) <$> Gen.nat (.linear 0 300),
    (fun d => (expected + 2 ^ bits - d % 2 ^ bits) % 2 ^ bits) <$> Gen.nat (.linear 0 300),
    (fun d => (expected + 2 ^ (bits - 1) + d - 2) % 2 ^ bits) <$> Gen.nat (.constant 0 4)])
  pure do
    let want ← oracle.ask ["quic_pn", toString bits, toString truncated, toString expected]
    match Quic.Packet.decodePacketNumber width truncated expected with
    | .ok n => toString n === want
    -- The format has no number of 2^62 or more, so EthLib refuses one that the formula gives.
    | .error _ => ensure ((want.toNat?.getD 0) ≥ 2 ^ 62) s!"EthLib refuses, the reference: {want}"

/-! ## QUIC keys and packet protection -/

/-- The Initial secrets and the packet keys of each suite are aioquic's. -/
def quicKeys (oracle : Oracle) : Property IO := propertyM do
  let dcid ← forAllWith hex (genBytes (.linear 0 20))
  pure do
    let .ok (client, server) := Quic.initialSecrets dcid | failWith "initialSecrets"
    s!"{hex ⟨client.toArray⟩} {hex ⟨server.toArray⟩}" === (← oracle.ask ["quic_initial", hex dcid])
    for (name, suite) in [("aes", Quic.CipherSuite.aes128GcmSha256),
        ("chacha", Quic.CipherSuite.chacha20Poly1305Sha256)] do
      let .ok keys := Quic.packetKeys suite server | failWith "packetKeys"
      s!"{hex ⟨keys.key.toArray⟩} {hex ⟨keys.iv.toArray⟩} {hex ⟨keys.hp.toArray⟩}" ===
        (← oracle.ask ["quic_keys", name, hex ⟨server.toArray⟩])

/-- A packet to protect: its header kind, connection IDs, number and payload. -/
structure Sealed where
  /-- 0 Initial, 1 0-RTT, 2 Handshake, 3 1-RTT. -/
  kind : Nat
  chacha : Bool
  destination : ByteArray
  source : ByteArray
  token : ByteArray
  width : Fin 4
  number : Nat
  payload : ByteArray
  secret : ByteArray
  deriving Repr

/-- Packets of every type and packet number width, with payloads from the shortest sample on. -/
def genSealed : Gen Sealed := do
  let kind ← Gen.nat (.constant 0 3)
  let chacha ← if kind = 0 then pure false else Gen.bool
  let (destination, source) ← Gen.zip (genBytes (.linear 0 20)) (genBytes (.linear 0 20))
  let token ← genBytes (.linear 0 70)
  let width ← Gen.element (List.finRange 4)
  let number ← genNatBits 62
  let payload ← genBytes (.linear (3 - width.val) 80)
  let secret ← genBytesN 32
  pure ⟨kind, chacha, destination, source, token, width, number, payload, secret⟩

/-- The header of a packet, with the Length that its payload and tag give. -/
def Sealed.header (p : Sealed) : Quic.Packet.Header :=
  let truncated := p.number % 256 ^ (p.width.val + 1)
  let length : Quic.Varint := Fin.ofNat _ (p.width.val + 1 + p.payload.size + 16)
  match p.kind with
  | 0 => .initial p.destination p.source p.token p.width length truncated
  | 1 => .zeroRtt p.destination p.source p.width length truncated
  | 2 => .handshake p.destination p.source p.width length truncated
  | _ => .oneRtt p.destination (p.number % 2 = 1) (p.number % 3 = 1) p.width truncated

/-- A protected packet is aioquic's, and it opens again to its header and its payload.

Then one changed byte makes it fail to open. -/
def quicProtect (oracle : Oracle) : Property IO := propertyM do
  let p ← forAll genSealed
  let flip ← forAll (Gen.nat (.linear 0 200))
  pure do
    let suite := if p.chacha then Quic.CipherSuite.chacha20Poly1305Sha256 else .aes128GcmSha256
    let some secret := (if h : p.secret.size = 32 then some (⟨p.secret.data, h⟩ : Vector UInt8 32)
      else none) | failWith "secret"
    let .ok keys := Quic.packetKeys suite secret | failWith "packetKeys"
    let .ok header := Quic.Packet.encode p.header | failWith "the header does not encode"
    let offset := header.size - (p.width.val + 1)
    let number : Quic.Varint := Fin.ofNat _ p.number
    let got := Quic.Protection.protect suite keys number offset header p.payload
    let want ← oracle.ask ["quic_protect", if p.chacha then "chacha" else "aes", hex p.secret,
      toString number.val, hex header, hex p.payload]
    match got with
    | .error _ => failWith s!"EthLib does not protect; the reference gives {want}"
    | .ok packet =>
      hex packet === want
      -- The receiver expects a number near the one sent.
      match Quic.Protection.unprotect suite keys number.val offset packet with
      | .ok (h, plain) => do hex h === hex header; hex plain === hex p.payload
      | .error _ => failWith "the packet does not open"
      let i := flip % packet.size
      let bad := packet.set! i (packet[i]! ^^^ 0x01)
      ensure (Quic.Protection.unprotect suite keys number.val offset bad).toOption.isNone
        s!"the packet opens with byte {i} changed"

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("varint: the consensus varint decodes as its rules say", (pbVarint oracle).withTests cases),
  ("varint: the consensus varint encodes", (pbVarintEncode oracle).withTests cases),
  ("varint: the unsigned varint of libp2p", (uvarint oracle).withTests cases),
  ("quic: an integer decodes as aioquic's", (quicVarintDecode oracle).withTests cases),
  ("quic: an integer encodes as aioquic's", (quicVarintEncode oracle).withTests cases),
  ("quic: a packet number, RFC 9000 A.3", (quicPacketNumber oracle).withTests cases),
  ("quic: Initial secrets and packet keys", (quicKeys oracle).withTests (min cases 300)),
  ("quic: packet protection is aioquic's", (quicProtect oracle).withTests (min cases 300))]

end NetworkingProperty.Codecs

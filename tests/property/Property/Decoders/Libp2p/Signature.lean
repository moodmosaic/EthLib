import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Networking.Libp2p.Tls

/-!
# ECDSA signatures in DER, and P-256 signatures under a certificate key

The DER of two scalars against `cryptography`, at every length of a scalar.

A P-256 signature under a SubjectPublicKeyInfo against OpenSSL, valid and changed.
-/

open Hedgehog Support EthLib EthLib.Networking EthLib.Networking.Libp2p

namespace DecodersProperty.Libp2p.Signature

open DecodersProperty

/-- The order of the group of P-256, from FIPS 186-4 D.1.2.3. -/
def p256Order : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- A scalar below `2 ^ 256`: every byte length, and the values where the top bit turns. -/
def genScalar : Gen Nat :=
  Gen.frequency [(4, genNatBits 256),
    (3, do
      let bytes ← Gen.nat (.constant 1 32)
      genNatBits (8 * bytes)),
    (2, Gen.element [0, 1, 127, 128, 255, 256, 2 ^ 255 - 1, 2 ^ 255, 2 ^ 256 - 1, 2 ^ 248 - 1,
      2 ^ 248, 2 ^ 247])]

/-- The DER of two scalars is the reference's. -/
def encode (oracle : Oracle) : Property IO := propertyM do
  let r ← forAll genScalar
  let s ← forAll genScalar
  pure do
    let der := Libp2p.encodeSignature r s
    hex der === (← oracle.ask ["sig_der", toString r, toString s])
    -- The reader takes it back, unless a scalar is zero.
    Libp2p.decodeScalars der === (if 0 < r ∧ 0 < s then some (r, s) else none)
    classify "a scalar is zero" (r = 0 ∨ s = 0)
    cover 9 "r takes 33 bytes" (2 ^ 255 ≤ r)
    cover 19 "r takes fewer than 32 bytes" (r < 2 ^ 247)
    cover 9 "s takes 33 bytes" (2 ^ 255 ≤ s)

/-- A way to change a DER signature. -/
inductive Change where
  | none
  | flip (index : Nat) (mask : UInt8)
  /-- A zero byte before `r`, which DER forbids unless the top bit is set. -/
  | padR
  /-- A zero byte before `s`. -/
  | padS
  | append
  | cut
  /-- The length of the sequence in the long form, which DER forbids below 128. -/
  | longLength
  /-- The leading zero byte of a scalar dropped, so that it reads as negative. -/
  | negative
  deriving Repr

/-- A DER integer of bytes taken as they are. -/
def integer (bytes : List UInt8) : List UInt8 := [0x02, UInt8.ofNat bytes.length] ++ bytes

/-- The bytes of a scalar as DER writes them, from X.690 section 8.3. -/
def magnitude (n : Nat) : List UInt8 :=
  let bytes := (Base.natToBytes 33 n).dropWhile (· == 0)
  match bytes with
  | [] => [0]
  | b :: _ => if b ≥ 128 then 0 :: bytes else bytes

/-- A sequence of two integers given by their bytes. -/
def sequence (r s : List UInt8) : ByteArray :=
  let body := integer r ++ integer s
  packed ([0x30, UInt8.ofNat body.length] ++ body)

/-- The changed signature of two scalars. -/
def Change.apply (change : Change) (r s : Nat) : ByteArray :=
  let sound := sequence (magnitude r) (magnitude s)
  match change with
  | .none => sound
  | .flip index mask =>
    let i := index % sound.size
    sound.set! i (sound[i]! ^^^ mask)
  | .padR => sequence (0 :: magnitude r) (magnitude s)
  | .padS => sequence (magnitude r) (0 :: magnitude s)
  | .append => sound.push 0
  | .cut => sound.extract 0 (sound.size - 1)
  | .longLength => packed ([0x30, 0x81] ++ sound.data.toList.drop 1)
  | .negative => sequence ((magnitude r).dropWhile (· == 0)) (magnitude s)

/-- A change, with a flip at any byte of the signature. -/
def genChange : Gen Change :=
  Gen.frequency [(4, pure .none),
    (4, Change.flip <$> Gen.nat (.constant 0 80) <*>
      (UInt8.ofNat <$> Gen.element [1, 2, 4, 8, 16, 32, 64, 128])),
    (1, pure .padR), (1, pure .padS), (1, pure .append), (1, pure .cut), (1, pure .longLength),
    (1, pure .negative)]

/-- The reader of two scalars takes exactly the strict DER that the reference takes. -/
def decode (oracle : Oracle) : Property IO := propertyM do
  let r ← forAll genScalar
  let s ← forAll genScalar
  let change ← forAll genChange
  pure do
    let der := change.apply r s
    let reference ← oracle.ask ["sig_scalars", hex der]
    annotate s!"the signature: {hex der}"
    match Libp2p.decodeScalars der with
    | some (r, s) => s!"{r} {s}" === reference
    | none => ensure (refused reference) s!"EthLib refuses, the reference reads {reference}"
    let changed := match change with
      | .none => false
      | _ => true
    label (kind changed reference)
    cover 8 "valid as generated" (!changed && !refused reference)
    cover 8 "mutated and still accepted by the reference" (changed && !refused reference)
    cover 16 "refused by the reference" (refused reference)

/-- What is changed of a signed message before it is verified. -/
inductive Tamper where
  | nothing
  | signature (change : Change)
  /-- The other signature of the same message: `n - s`. -/
  | highS
  | message
  | key
  deriving Repr

/-- A P-256 signature under a certificate key verifies exactly when OpenSSL takes it. -/
def verify (oracle : Oracle) : Property IO := propertyM do
  let secret ← forAllWith hex (genBytesN 32)
  let other ← forAllWith hex (genBytesN 32)
  let message ← forAllWith hex (genBytes (.linear 0 60))
  let tamper ← forAll (Gen.frequency [(4, pure Tamper.nothing), (2, pure .highS),
    (4, Tamper.signature <$> genChange), (1, pure .message), (1, pure .key)])
  pure do
    let [spkiWord, signatureWord] := words (← oracle.ask ["p256_sign", hex secret, hex message])
      | failWith "the oracle gave no signature"
    let [otherSpki, _] := words (← oracle.ask ["p256_sign", hex other, hex message])
      | failWith "the oracle gave no second key"
    let some signature := unhex? signatureWord | failWith "the signature is not hexadecimal"
    let some (r, s) := Libp2p.decodeScalars signature
      | failWith "EthLib does not read a signature of the reference"
    let (spki, message, signature) := match tamper with
      | .nothing => (spkiWord, message, signature)
      | .signature change => (spkiWord, message, change.apply r s)
      | .highS => (spkiWord, message, sequence (magnitude r) (magnitude (p256Order - s)))
      | .message => (spkiWord, message.push 1, signature)
      | .key => (otherSpki, message, signature)
    let some key := unhex? spki | failWith "the key is not hexadecimal"
    let reference ← oracle.ask ["p256_verify", spki, hex message, hex signature]
    annotate s!"the signature: {hex signature}"
    (if Tls.verifyP256 key message signature then "1" else "0") === reference
    cover 20 "verifies" (reference == "1")
    cover 13 "does not verify" (reference == "0")
    cover 5 "the other signature of the message verifies" (reference == "1" && (match tamper with
      | .highS => true
      | _ => false))

/-- The properties of the signatures. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("peerid: the DER of a signature is the reference's", (encode oracle).withTests cases),
  ("peerid: a changed DER signature is read as the reference reads it",
    (decode oracle).withTests cases),
  ("libp2p-tls: a P-256 signature verifies as OpenSSL says", (verify oracle).withTests cases)]

end DecodersProperty.Libp2p.Signature

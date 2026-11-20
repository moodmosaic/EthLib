import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Cryptography.Secp256k1.Sign
import EthLib.Serialization.Rlp.Codec

/-!
# What the modules of the devp2p family share

RLP items as the oracle reads them, and secp256k1 keys.
-/

open Hedgehog Support EthLib
open EthLib.Serialization.Rlp (Item)
open EthLib.Cryptography.Secp256k1 (Fn Point)

namespace DecodersProperty.Devp2p

/-- An RLP item as text: bytes in hexadecimal, `-` for none, a list in brackets. -/
partial def itemText : Item → String
  | .bytes b => hex b
  | .list items => "[" ++ ",".intercalate (items.map itemText) ++ "]"

instance : Repr Item := ⟨fun i _ => itemText i⟩

/-- The big-endian bytes of a number, with no leading zero byte, so none for zero. -/
def natBytes (n : Nat) : List UInt8 :=
  if h : n = 0 then [] else natBytes (n / 256) ++ [UInt8.ofNat (n % 256)]
termination_by n
decreasing_by omega

/-- A number as the RLP item of a scalar. -/
def natItem (n : Nat) : Item := .bytes ⟨(natBytes n).toArray⟩

/-- A private key: small ones, ones near the group order, any one. -/
def genSecret : Gen Nat :=
  (fun n => n % (Fn.modulus - 1) + 1) <$> genNatBits 256

/-- The 32 big-endian bytes of a number. -/
def bytes32 (n : Nat) : ByteArray := ⟨(Base.natToBytes 32 n).toArray⟩

/-- The 32 bytes of a private key, in hexadecimal. -/
def secretHex (sk : Nat) : String := hex (bytes32 sk)

/-- The public key of a private key. -/
def publicOf (sk : Nat) : Point := Point.mul (Fin.ofNat _ sk) Point.generator

/-- A `0` or a `1`, as the oracle writes a flag. -/
def flag (b : Bool) : String := if b then "1" else "0"

/-- What one change does to bytes: set a byte, flip a bit, drop, add, or cut.

The position is taken modulo the length, since the bytes are known only in the test. -/
def mutate (change : Nat × Nat × UInt8) (bytes : ByteArray) : ByteArray :=
  let (kind, position, byte) := change
  let list := bytes.data.toList
  let at_ := if list.isEmpty then 0 else position % list.length
  packed (match kind % 5 with
    | 0 => list.set at_ byte
    | 1 => list.set at_ (list.getD at_ 0 ^^^ (1 <<< (byte % 8)))
    | 2 => list.eraseIdx at_
    | 3 => list.take at_ ++ [byte] ++ list.drop at_
    | _ => list.take at_)

/-- A change of bytes: its kind, a position and a byte. -/
def genChange : Gen (Nat × Nat × UInt8) :=
  Gen.zip (Gen.nat (.constant 0 4)) (Gen.zip (Gen.nat (.constant 0 4000)) genByte)

end DecodersProperty.Devp2p

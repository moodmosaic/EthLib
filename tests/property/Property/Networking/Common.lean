import Hedgehog
import Support
import EthLib.Cryptography.Secp256k1.Sign
import EthLib.Serialization.Rlp.Codec

/-!
# What the modules of the networking driver share
-/

open Hedgehog Support EthLib
open EthLib.Serialization.Rlp (Item)
open EthLib.Cryptography.Secp256k1 (Fn Point)

namespace NetworkingProperty

instance : Repr ByteArray := ⟨fun b _ => hex b⟩

/-- An RLP item as text, for reports. -/
partial def showItem : Item → String
  | .bytes b => hex b
  | .list items => "[" ++ ", ".intercalate (items.map showItem) ++ "]"

instance : Repr Item := ⟨fun i _ => showItem i⟩

/-- A private key: small ones, ones near the group order, any one. -/
def genSecret : Gen Nat :=
  (fun n => n % (Fn.modulus - 1) + 1) <$> genNatBits 256

/-- The 32 bytes of a private key. -/
def secretHex (sk : Nat) : String := hex ⟨(Base.natToBytes 32 sk).toArray⟩

/-- The public key of a private key. -/
def publicOf (sk : Nat) : Point := Point.mul (Fin.ofNat _ sk) Point.generator

/-- The RLP bytes of an item, or none. -/
def rlp (item : Item) : ByteArray :=
  (Serialization.Rlp.encode item).toOption.getD .empty

/-- A vector of `n` bytes. -/
def genVector (n : Nat) : Gen (Vector UInt8 n) :=
  (fun (l : List UInt8) => Vector.ofFn fun i => l.getD i.val 0) <$> genByteList (.singleton n)

/-- The bytes of a vector in hexadecimal. -/
def hexv {n : Nat} (v : Vector UInt8 n) : String := hex ⟨v.toArray⟩

/-- An answer of the oracle with the reason of an error dropped. -/
def verdict (s : String) : String :=
  if s.startsWith "error" then "error" else s

/-- EthLib's bytes in the words of the oracle, or `error`. -/
def answer {ε : Type} (r : Except ε ByteArray) : String :=
  match r with
  | .ok out => hex out
  | .error _ => "error"

end NetworkingProperty

import Hedgehog
import Support
import EthLib.Cryptography.Hash
import EthLib.Cryptography.Aes

/-!
# What the properties of symmetric cryptography share

Lengths biased to the block and padding boundaries, bytes biased to the carries, and the
conversions between byte arrays and the fixed-size vectors of EthLib.
-/

open Hedgehog Support

namespace HashesProperty

/-- The first `n` bytes as a vector, zero where the array ends. -/
def vec (n : Nat) (bytes : ByteArray) : Vector UInt8 n := Vector.ofFn fun i => bytes.data.getD i 0

/-- The bytes of a vector. -/
def unvec {n : Nat} (v : Vector UInt8 n) : ByteArray := ⟨v.toArray⟩

/-- The hexadecimal of a vector. -/
def hexv {n : Nat} (v : Vector UInt8 n) : String := hex (unvec v)

/-- A length near a multiple of `block`: from 10 below it to 2 above, or any small one.

Padding rules change at the block boundary and a few bytes before it (9 for SHA-256, 1 for
Keccak), so most draws land there. -/
def genLen (block : Nat) (blocks : Nat := 3) : Gen Nat :=
  Gen.frequency [
    (2, Gen.nat (.linear 0 (2 * block))),
    (5, Gen.zipWith (fun k d => k * block + 2 - d) (Gen.nat (.constant 1 blocks))
      (Gen.nat (.constant 0 12))),
    (1, Gen.element [0, 1])]

/-- A byte: any, or one of the two that carry. -/
def genEdgeByte : Gen UInt8 :=
  Gen.frequency [(6, genByte), (1, pure 0xff), (1, pure 0x00), (1, pure 0x80)]

/-- Bytes of a given length: random, all ones, or all zeros. -/
def genBytesOf (n : Nat) : Gen ByteArray :=
  Gen.frequency [
    (6, genBytesN n),
    (1, pure ⟨Array.replicate n 0xff⟩),
    (1, pure ⟨Array.replicate n 0⟩),
    (1, (fun bytes => ByteArray.mk bytes.toArray) <$> Gen.list (.singleton n) genEdgeByte)]

/-- A message whose length is near a multiple of `block`. -/
def genMsg (block : Nat) (blocks : Nat := 3) : Gen ByteArray := do
  genBytesOf (← genLen block blocks)

/-- A short byte string, for a salt, a label or additional data. -/
def genShort : Gen ByteArray := genBytes (.linear 0 40)

/-- The same bytes with one bit flipped, or with a byte appended when there is none. -/
def flipBit (bytes : ByteArray) (bit : Nat) : ByteArray :=
  if bytes.isEmpty then ⟨#[1]⟩
  else
    let i := (bit / 8) % bytes.size
    ⟨bytes.data.modify i (· ^^^ (1 <<< (bit % 8).toUInt8))⟩

/-- The two words of an answer that has two. -/
def two (answer : String) : String × String :=
  match answer.splitOn " " with
  | [a, b] => (a, b)
  | _ => (answer, "")

/-- The hexadecimal of a result, or `error`. -/
def answerOf {ε : Type} (result : Except ε ByteArray) : String :=
  match result with
  | .ok bytes => hex bytes
  | .error _ => "error"

/-- The AES forward cipher under a key of 16 or of 32 bytes. -/
def aesCiph (key : ByteArray) : EthLib.Cryptography.Aes.Block → EthLib.Cryptography.Aes.Block :=
  if key.size = 16 then EthLib.Cryptography.Aes.ciph .aes128 (vec _ key)
  else EthLib.Cryptography.Aes.ciph .aes256 (vec _ key)

/-- An AES key: 16 or 32 bytes. -/
def genAesKey : Gen ByteArray := do genBytesOf (← Gen.element [16, 32])

end HashesProperty

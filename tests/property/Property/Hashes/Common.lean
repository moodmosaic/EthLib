import Hedgehog
import Support
import EthLib.Cryptography.Hash
import EthLib.Cryptography.Aes

/-!
# What the properties of symmetric cryptography share

Lengths biased to the block and padding boundaries, and bytes biased to the carries.

Also the conversions between byte arrays and the fixed-size vectors of EthLib.
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

Padding rules change at the block boundary and a few bytes before it (9 for SHA-256, 1 for Keccak).

So most draws land there, and a quarter of them on a boundary or one byte from it. -/
def genLen (block : Nat) (blocks : Nat := 3) : Gen Nat :=
  Gen.frequency [
    (2, Gen.nat (.linear 0 (2 * block))),
    (4, Gen.zipWith (fun k d => k * block + 2 - d) (Gen.nat (.constant 1 blocks))
      (Gen.nat (.constant 0 12))),
    (3, Gen.zipWith (fun k d => k * block + 1 - d) (Gen.frequency [(3, pure 1),
      (1, Gen.nat (.constant 2 blocks))]) (Gen.nat (.constant 0 2))),
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

/-- A message for a hash that pads as FIPS 180-4 §5.1.1 does, in blocks of 64 bytes.

The padding takes 9 bytes, so 55 bytes fill a block exactly and 56 need one more. -/
def genMdMsg : Gen ByteArray :=
  Gen.frequency [(10, genMsg 64 4), (1, pure .empty),
    (4, do genBytesOf (← Gen.zipWith (fun k d => 64 * k + 54 + d) (Gen.nat (.constant 0 3))
      (Gen.nat (.constant 0 2))))]

/-- The messages of a generator, and now and then one of some thousand bytes.

The lengths around a block show the padding, and a long message shows the chain of blocks. -/
def orLong (g : Gen ByteArray) : Gen ByteArray :=
  Gen.frequency [(12, g), (1, do genBytesN (← Gen.nat (.constant 1000 5000)))]

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

/-- The AES forward cipher under a key of 16, of 24 or of 32 bytes.

EthLib names two key sizes, and AES-192 is its general cipher with `Nk = 6` and `Nr = 12`. -/
def aesCiph (key : ByteArray) : EthLib.Cryptography.Aes.Block → EthLib.Cryptography.Aes.Block :=
  if key.size = 16 then EthLib.Cryptography.Aes.ciph .aes128 (vec _ key)
  else if key.size = 24 then
    EthLib.Cryptography.Aes.cipher 12 (EthLib.Cryptography.Aes.keyExpansion 6 12 (vec 24 key))
  else EthLib.Cryptography.Aes.ciph .aes256 (vec _ key)

/-- An AES key: 16, 24 or 32 bytes. -/
def genAesKey : Gen ByteArray := do genBytesOf (← Gen.element [16, 24, 32])

/-! ## Coverage -/

/-- Count the case under the class of a length against a block of `block` bytes. -/
def labelLength {m : Type → Type} [Monad m] (what : String) (block size : Nat) :
    TestT m Unit := do
  classify s!"{what}: empty" (size == 0)
  classify s!"{what}: under a block" (0 < size && size < block)
  classify s!"{what}: exactly a block" (size == block)
  classify s!"{what}: a block plus one" (size == block + 1)
  classify s!"{what}: many blocks" (size ≥ 2 * block)

/-- Count the case under the class of its padding by FIPS 180-4 §5.1.1.

The padding is one byte and eight bytes of length, so it fits after at most 55 bytes of a block. -/
def labelMdPadding {m : Type → Type} [Monad m] (size : Nat) : TestT m Unit := do
  classify "padding: fits in the last block" (size % 64 < 55)
  classify "padding: fills the last block exactly" (size % 64 == 55)
  classify "padding: needs one more block" (size % 64 > 55)

/-- Count the case under the class of its padding by FIPS 202 §5.1, at a rate in bytes. -/
def labelSpongePadding {m : Type → Type} [Monad m] (rate size : Nat) : TestT m Unit := do
  classify "padding: the one byte 0x81" (size % rate == rate - 1)
  classify "padding: a whole block" (size % rate == 0)
  classify "padding: two bytes or more, under a block" (size % rate != 0 && size % rate < rate - 1)

/-- The name of the constructor of a value, from its `Repr`. -/
def ctorName {α : Type} [Repr α] (x : α) : String :=
  (((reprStr x).splitOn " ").headD "").splitOn "." |>.getLastD ""

/-- Count the case under the outcome of a call: accepted, or the reason of the refusal. -/
def labelOutcome {m : Type → Type} [Monad m] {ε α : Type} [Repr ε] (result : Except ε α)
    (what : String := "outcome") : TestT m Unit :=
  match result with
  | .ok _ => label s!"{what}: accepted"
  | .error e => label s!"{what}: refused, {ctorName e}"

/-- Require a share of each named class, in a run long enough for the shares to settle.

A run starts at size 0 and grows by one, so a short run has small cases and other shares.

Each minimum is about a third of the share seen at 1,000 cases. -/
def withMinimums (cases : Nat) (minimums : List (Nat × String)) (p : Property IO) :
    Property IO :=
  if cases < 500 then p else
  { p with test := do
      let test ← p.test
      pure do
        test
        for (minimum, name) in minimums do
          cover minimum name false }

end HashesProperty

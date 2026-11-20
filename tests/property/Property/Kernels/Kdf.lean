import Property.Kernels.Common
import EthLib.Cryptography.Hash

/-!
# Key derivations at the boundaries of every parameter

HMAC, HKDF, PBKDF2, the Concatenation KDF and scrypt, over SHA-256.

Each length is drawn around the boundaries of its parameter.

They are the block of 64 bytes, the output of 32 bytes and the largest count of blocks.

Each property counts the cases on each side of a boundary.
-/

open Hedgehog Support EthLib EthLib.Cryptography.Hash

namespace KernelsProperty.Kdf

/-- A length near a multiple of `unit`: zero, one below, on and one above the first few. -/
def genAroundUnit (unit most : Nat) : Gen Nat :=
  Gen.frequency [
    (5, (fun (k, d) => k * unit + d - 1) <$>
      Gen.zip (Gen.nat (.constant 0 most)) (Gen.nat (.constant 0 2))),
    (1, pure 0), (2, Gen.nat (.linear 0 (most * unit)))]

/-- Bytes of a length near a multiple of `unit`. -/
def genBytesAround (unit most : Nat) : Gen ByteArray := do
  let size ← genAroundUnit unit most
  Gen.bytes (.singleton size)

/-- The text of an answer: the bytes of a result, or the name of its error. -/
def shown {ε : Type} (name : ε → String) : Except ε ByteArray → String
  | .ok bytes => hex bytes
  | .error e => s!"error {name e}"

/-- HMAC-SHA-256 with keys shorter than, as long as and longer than a block of 64 bytes. -/
def hmac (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith bytesHex (genBytesAround 64 3)
  let message ← forAllWith bytesHex (genBytesAround 64 3)
  pure do
    classify "the key is empty" (key.size == 0)
    classify "the key is shorter than a block" (key.size < 64)
    classify "the key is exactly a block" (key.size == 64)
    classify "the key is one byte longer than a block" (key.size == 65)
    classify "the key is longer than a block" (key.size > 64)
    classify "the message is empty" (message.size == 0)
    let want ← oracle.ask ["hmac", hex key, hex message]
    hex (Hmac.hmac key message) === want
    hex ⟨(Hmac.hmac32 key message).toArray⟩ === want
    (Hmac.blockKey key).size === 64

/-- HKDF-Expand and HKDF at every class of output length, key length and info. -/
def hkdf (oracle : Oracle) : Property IO := propertyM do
  let prk ← forAllWith bytesHex (Gen.frequency [
    (2, Gen.bytes (.constant 30 34)), (2, Gen.bytes (.singleton 32)), (1, genBytesAround 64 2)])
  let info ← forAllWith bytesHex (Gen.frequency [(1, pure .empty), (2, genBytesAround 64 2)])
  let salt ← forAllWith bytesHex (Gen.frequency [(1, pure .empty), (2, genBytesAround 64 2)])
  let length ← forAll (Gen.frequency [
    (4, genAroundUnit 32 4), (3, (fun d => 255 * 32 + d - 2) <$> Gen.nat (.constant 0 4)),
    (1, (fun d => 254 * 32 + d - 1) <$> Gen.nat (.constant 0 2)),
    (1, Gen.nat (.exponential 0 (2 ^ 40)))])
  pure do
    classify "the output is empty" (length == 0)
    classify "the output is not whole blocks" (length % 32 != 0)
    classify "the output is exactly 255 blocks" (length == 255 * 32)
    classify "the output is longer than 255 blocks" (length > 255 * 32)
    classify "the key is shorter than 32 bytes" (prk.size < 32)
    classify "the key is exactly 32 bytes" (prk.size == 32)
    classify "the info is empty" (info.size == 0)
    classify "the salt is empty" (salt.size == 0)
    let name : Hkdf.HkdfError → String
      | .keyTooShort _ => "keyTooShort"
      | .outputTooLong _ => "outputTooLong"
    shown name (Hkdf.expand prk info length) ===
      (← oracle.ask ["hkdf_expand", hex prk, hex info, toString length])
    shown name (Hkdf.hkdf salt prk info length) ===
      (← oracle.ask ["hkdf", hex salt, hex prk, hex info, toString length])
    hex (Hkdf.extract salt prk) === (← oracle.ask ["hmac", hex salt, hex prk])

/-- PBKDF2 at every class of iteration count, output length, password and salt. -/
def pbkdf2 (oracle : Oracle) : Property IO := propertyM do
  let password ← forAllWith bytesHex (genBytesAround 64 2)
  let salt ← forAllWith bytesHex (Gen.frequency [(1, pure .empty), (2, genBytesAround 64 2)])
  let iterations ← forAll (Gen.frequency [(1, pure 0), (3, Gen.nat (.constant 1 4)),
    (1, Gen.nat (.linear 1 40))])
  let length ← forAll (Gen.frequency [(5, genAroundUnit 32 5), (1, Gen.nat (.linear 0 400))])
  pure do
    classify "no iteration" (iterations == 0)
    classify "one iteration" (iterations == 1)
    classify "the output is empty" (length == 0)
    classify "the output is not whole blocks" (length % 32 != 0)
    classify "the output has several blocks" (length > 32)
    classify "the password is longer than a block" (password.size > 64)
    classify "the salt is empty" (salt.size == 0)
    let name : Pbkdf2.Pbkdf2Error → String
      | .zeroIterations => "zeroIterations"
      | .emptyOutput => "emptyOutput"
      | .outputTooLong _ => "outputTooLong"
      | .inputTooLong => "inputTooLong"
    shown name (Pbkdf2.pbkdf2 password salt iterations length) ===
      (← oracle.ask ["pbkdf2", hex password, hex salt, toString iterations, toString length])

/-- The Concatenation KDF at every class of output length, secret and fixed info. -/
def concatKdf (oracle : Oracle) : Property IO := propertyM do
  let z ← forAllWith bytesHex (genBytesAround 64 2)
  let info ← forAllWith bytesHex (Gen.frequency [(1, pure .empty), (2, genBytesAround 64 2)])
  let length ← forAll (Gen.frequency [(5, genAroundUnit 32 5), (1, Gen.nat (.linear 0 400))])
  pure do
    classify "the output is empty" (length == 0)
    classify "the output is not whole blocks" (length % 32 != 0)
    classify "the output has several blocks" (length > 32)
    classify "the secret is empty" (z.size == 0)
    classify "the info is empty" (info.size == 0)
    let name : ConcatKdf.ConcatKdfError → String
      | .emptyOutput => "emptyOutput"
      | .outputTooLong _ => "outputTooLong"
      | .inputTooLong => "inputTooLong"
    shown name (ConcatKdf.concatKdf z info length) ===
      (← oracle.ask ["concat", hex z, hex info, toString length])

/-- The limits of the lengths that cannot be reached with real bytes, as the texts state them.

PBKDF2 admits `(2^32 - 1) * 32` bytes and the Concatenation KDF `2^32 - 1` blocks. -/
def limits : Property IO := pureIO do
  let d ← forAll (Gen.nat (.constant 0 2))
  let length := (2 ^ 32 - 1) * 32 + d - 1
  classify "at the limit" (d == 1)
  classify "one past the limit" (d == 2)
  -- The refusal comes before any hashing, so one past the limit answers at once.
  if d == 2 then
    Pbkdf2.pbkdf2 .empty .empty 1 length === .error (.outputTooLong length)
    ConcatKdf.concatKdf .empty .empty length === .error (.outputTooLong length)
    Scrypt.scrypt .empty .empty 2 1 1 length === .error (.outputTooLong length)
  Pbkdf2.MAX_LENGTH === (2 ^ 32 - 1) * 32

/-- scrypt at every class of cost, block size, parallelization and length, as RFC 7914 rules.

The cost reaches `2^15` at `r = 1`, the last one below the bound `2^(16 r)`, and `2^16` past it. -/
def scrypt (oracle : Oracle) : Property IO := propertyM do
  let r ← forAll (Gen.frequency [(1, pure 0), (4, pure 1), (2, Gen.nat (.constant 2 4))])
  let n ← forAll (Gen.frequency [
    (4, (2 ^ ·) <$> Gen.nat (.constant 1 7)), (1, Gen.nat (.constant 0 9)),
    (1, (fun d => 2 ^ 6 + d - 1) <$> Gen.nat (.constant 0 2)),
    (2, (2 ^ ·) <$> Gen.nat (.constant 14 17))])
  let p ← forAll (Gen.frequency [(1, pure 0), (4, Gen.nat (.constant 1 3))])
  let length ← forAll (Gen.frequency [(4, genAroundUnit 32 3), (1, Gen.nat (.linear 0 200))])
  let password ← forAllWith bytesHex (Gen.bytes (.linear 0 70))
  let salt ← forAllWith bytesHex (Gen.bytes (.linear 0 40))
  pure do
    -- A cost of `2^14` or more at a wide block is slow: only `r = 1` reaches it.
    if n ≥ 2 ^ 14 && r > 1 then pure () else
    let name : Scrypt.ScryptError → String
      | .invalidCost _ => "invalidCost"
      | .invalidBlockSize _ => "invalidBlockSize"
      | .invalidParallelization _ => "invalidParallelization"
      | .emptyOutput => "emptyOutput"
      | .outputTooLong _ => "outputTooLong"
      | .invalidInputSize _ _ => "invalidInputSize"
      | .pbkdf2 _ => "pbkdf2"
    let got := Scrypt.scrypt password salt n r p length
    classify "accepted" (got matches .ok _)
    classify "the cost is not a power of two above 1" (n < 2 || n &&& (n - 1) != 0)
    classify "the cost is 2^15 at r = 1, the last one admitted" (n == 2 ^ 15 && r == 1)
    classify "the cost is 2^16 at r = 1, the first one refused" (n == 2 ^ 16 && r == 1)
    classify "r is zero" (r == 0)
    classify "p is zero" (p == 0)
    classify "the output is empty" (length == 0)
    classify "several blocks are mixed" (p > 1)
    shown name got === (← oracle.ask ["scrypt", hex password, hex salt, toString n, toString r,
      toString p, toString length])
    Scrypt.validCost n r === (decide (1 < n) && n &&& (n - 1) == 0 && decide (n < 2 ^ (16 * r)))

end KernelsProperty.Kdf

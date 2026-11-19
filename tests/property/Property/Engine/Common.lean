import Hedgehog
import Support
import EthLib.Engine.Json

/-!
# What the properties of the Engine API share

Generators of hashes and of hexadecimal text that is almost valid, and the text forms that the
oracle reads.
-/

open Hedgehog Support EthLib EthLib.Base

namespace EngineProperty

/-- The UTF-8 bytes of a text in hexadecimal, the form in which the oracle takes text. -/
def textHex (text : String) : String := hex text.toUTF8

/-- A JSON value as the oracle takes it: its compact text, in hexadecimal. -/
def jsonHex (j : Lean.Json) : String := textHex j.compress

/-- A vector of `n` bytes. -/
def genVector (n : Nat) : Gen (Vector UInt8 n) :=
  (fun bytes => Vector.ofFn fun i => bytes.getD i.val 0) <$> genByteList (.singleton n)

/-- A hash of 32 bytes: zero, small, or any. -/
def genHash : Gen Hash32 :=
  Gen.frequency [(1, pure (Vector.replicate 32 0)), (4, genVector 32)]

/-- Lower-case hexadecimal digits of a list of bytes, without a marker. -/
def digitsOf (bytes : List UInt8) : String :=
  String.ofList ((hex ⟨bytes.toArray⟩).toList.filter (· ≠ '-'))

/-- A hexadecimal digit as a writer of a JSON-RPC API may write it: mostly lower case.

Upper case and a character that is no digit are the near misses. -/
def genHexChar : Gen Char :=
  Gen.frequency [(30, Gen.element "0123456789abcdef".toList), (2, Gen.element "ABCDEF".toList),
    (1, Gen.element "gG xX-_".toList)]

/-- A marker of hexadecimal text: mostly `0x`. -/
def genMarker : Gen String :=
  Gen.frequency [(20, pure "0x"), (1, pure "0X"), (1, pure ""), (1, pure "x"), (1, pure "00x")]

/-- Text that is almost the hexadecimal form of `size` bytes.

The length is that of the size, or one or two digits off, and a digit may be upper case. -/
def genHexText (size : Nat) : Gen String := do
  let length ← Gen.frequency [(8, pure (2 * size)), (1, pure (2 * size + 1)),
    (1, pure (2 * size - 1)), (1, pure (2 * size + 2)), (1, pure (2 * size - 2)),
    (1, Gen.nat (.linear 0 (2 * size + 4)))]
  let (marker, digits) ← Gen.zip genMarker (Gen.string (.singleton length) genHexChar)
  pure (marker ++ digits)

/-- Text that is almost a quantity below `2 ^ bits`.

A quantity has no leading zero, and zero is `0x0`, so zeros in front are the near misses.
The values sit near the top of the width, where one digit more is out of range. -/
def genQuantityText (bits : Nat) : Gen String := do
  let n ← Gen.choice [genNatBits bits, (2 ^ bits + ·) <$> Gen.nat (.exponential 0 (2 ^ bits)),
    genNatBits (bits + 8)]
  let digits := String.ofList (Nat.toDigits 16 n)
  let shape ← Gen.frequency [(12, pure digits), (1, pure ("0" ++ digits)),
    (1, pure ("00" ++ digits)),
    (1, pure digits.toUpper), (1, pure ""), (1, pure (digits ++ "g")), (1, pure (" " ++ digits))]
  let marker ← genMarker
  pure (marker ++ shape)

/-- The verdict of a decoding as the oracle spells it. -/
def verdict {ε α : Type} : Except ε α → String
  | .ok _ => "ok"
  | .error _ => "error"

end EngineProperty

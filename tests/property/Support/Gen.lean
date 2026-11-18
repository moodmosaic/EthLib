import Hedgehog

/-!
# Generators and text forms that every driver shares
-/

open Hedgehog

namespace Support

/-- Any byte; it shrinks to `0`. -/
def genByte : Gen UInt8 := Gen.integral (.constant 0 255)

/-- A list of bytes of a length in the range. -/
def genByteList (range : Range Nat) : Gen (List UInt8) := Gen.list range genByte

/-- A byte array of a length in the range. -/
def genBytes (range : Range Nat) : Gen ByteArray :=
  (fun bytes => ByteArray.mk bytes.toArray) <$> genByteList range

/-- A byte array of exactly `n` bytes. -/
def genBytesN (n : Nat) : Gen ByteArray := genBytes (.singleton n)

/-- A natural number below `2 ^ bits`: small ones, ones near the top, any one.

The edges of a fixed-width type hold most of its bugs, so a third of the draws are near them. -/
def genNatBits (bits : Nat) : Gen Nat :=
  let top := 2 ^ bits - 1
  Gen.choice [Gen.nat (.exponential 0 top), (top - ·) <$> Gen.nat (.exponential 0 top),
    Gen.nat (.constant 0 top)]

/-- A 64-bit word, with the same bias to the edges. -/
def genUInt64 : Gen UInt64 := UInt64.ofNat <$> genNatBits 64

/-- Bytes in lower-case hexadecimal, `-` for none, so a line never has an empty word. -/
def hex (bytes : ByteArray) : String :=
  if bytes.isEmpty then "-"
  else String.join (bytes.toList.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length = 1 then '0' :: digits else digits))

/-- The value of a hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The bytes that `hex` wrote, or none for another string. -/
def unhex? (text : String) : Option ByteArray :=
  if text = "-" then some ByteArray.empty
  else
    let rec go : List Char → Array UInt8 → Option ByteArray
      | [], acc => some (ByteArray.mk acc)
      | [_], _ => none
      | hi :: lo :: rest, acc => do
        go rest (acc.push (UInt8.ofNat ((← hexDigit? hi) * 16 + (← hexDigit? lo))))
    go text.toList #[]

/-- The number of cases, from the first argument that is a number, or the default. -/
def casesOf (args : List String) (default : Nat := 100) : Nat :=
  (args.findSome? String.toNat?).getD default

/-- A pure property, in `IO` so one group holds it beside those that ask an oracle. -/
def pureIO (test : PropertyM Unit) : Property IO :=
  { test := (fun _ => pure ()) <$> test }

end Support

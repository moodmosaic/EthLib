import Property.Kernels.Common
import EthLib.Base

/-!
# The base layer, definition by definition

What `Property/Base.lean` left: bytes, addresses, words, both byte orders, hexadecimal and lengths.

Each property takes a number or a length that does not fit as often as one that does.

The answer is arithmetic on `Nat`, or the list that the definition stands for.
-/

open Hedgehog Support EthLib EthLib.Base

namespace KernelsProperty.Base

/-- A word of 256 bits: `0`, `1`, `2 ^ 255 - 1`, `2 ^ 255`, `2 ^ 256 - 1`, near them, or any. -/
def genWord : Gen Nat :=
  Gen.frequency [
    (4, Gen.element [0, 1, 2 ^ 255 - 1, 2 ^ 255, 2 ^ 256 - 1, 2 ^ 160 - 1, 2 ^ 160]),
    (2, genAround (2 ^ 255) (2 ^ 256)), (2, genAround (2 ^ 160) (2 ^ 256)),
    (2, genLimbs 8), (3, genNatBits 256)]

/-- A number for a field of `len` bytes: one that fits, the first that does not, or a larger one. -/
def genFor (len : Nat) : Gen Nat :=
  let bound := 256 ^ len
  Gen.frequency [
    (4, Gen.nat (.constant 0 (bound - 1))), (1, pure (bound - 1)), (2, pure bound),
    (1, pure (bound + 1)), (2, (bound + ·) <$> Gen.nat (.exponential 0 (bound * 2 ^ 70))),
    (1, (bound * ·) <$> Gen.nat (.constant 1 300))]

/-- Big-endian bytes of a number at any width keep the number modulo `256 ^ len`.

`natToBytes` says so: a number that does not fit loses its higher bytes. -/
def bigEndian : Property IO := pureIO do
  let len ← forAll (Gen.nat (.linear 0 40))
  let n ← forAll (genFor len)
  let bytes := natToBytes len n
  classify "the number fits" (n < 256 ^ len)
  classify "the number does not fit" (n ≥ 256 ^ len)
  classify "the width is zero" (len == 0)
  bytes.length === len
  bytesToNat bytes === n % 256 ^ len
  bytes === (List.range len).map fun i => UInt8.ofNat (n / 256 ^ (len - 1 - i) % 256)
  (natToBytes4 n).toList === natToBytes 4 n
  bytesToNat (natToBytes4 n).toList === n % 2 ^ 32
  -- The reader is Horner's rule on any list, also one with leading zeros.
  let zeros ← forAll (Gen.nat (.linear 0 4))
  bytesToNat (List.replicate zeros 0 ++ bytes) === n % 256 ^ len

/-- Little-endian bytes of a number at any width keep the number modulo `256 ^ k`.

At most eight bytes read as a 64-bit word, at every width from 0 to 8. -/
def littleEndian : Property IO := pureIO do
  let k ← forAll (Gen.frequency [(2, Gen.nat (.constant 0 8)), (1, Gen.nat (.linear 0 40))])
  let n ← forAll (genFor k)
  let bytes := uintToBytes k n
  classify "the number fits" (n < 256 ^ k)
  classify "the number does not fit" (n ≥ 256 ^ k)
  label (if k ≤ 8 then s!"width {k}" else "width above 8")
  bytes.toList === (List.range k).map fun i => UInt8.ofNat (n / 256 ^ i % 256)
  bytesToUint bytes === n % 256 ^ k
  if h : k ≤ 8 then (bytesToUint64 bytes h).toNat === n % 256 ^ k

/-- The 32-bit word helpers are their arithmetic, at every shift and every byte index. -/
def words32 : Property IO := pureIO do
  let x ← forAll (UInt32.ofNat <$> genNatBits 32)
  let shift ← forAll (Gen.frequency [(3, Gen.nat (.constant 0 33)), (1, Gen.nat (.constant 0 255))])
  let (b0, b1, b2, b3) ← forAll (Gen.zip genByte (Gen.zip genByte (Gen.zip genByte genByte)))
  let i ← forAll (Gen.nat (.constant 0 3))
  classify "the shift is 0 mod 32" (shift % 32 == 0)
  classify "the shift is 32 or more" (shift ≥ 32)
  let s := shift % 32
  (rotl32 x (UInt32.ofNat shift)).toNat ===
    x.toNat * 2 ^ s % 2 ^ 32 + x.toNat / 2 ^ (32 - s) % 2 ^ 32
  (uint32OfBytes b0 b1 b2 b3).toNat ===
    b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat
  (uint32Byte x i).toNat === x.toNat / 256 ^ i % 256

/-- A word, its 32 big-endian bytes, its address and its signed value are those of the number. -/
def word : Property IO := pureIO do
  let n ← forAll genWord
  let w : U256 := BitVec.ofNat 256 n
  let bytes := U256.toBeBytes w
  classify "the word is 2 ^ 255 or more" (n ≥ 2 ^ 255)
  classify "the word is 2 ^ 160 or more" (n ≥ 2 ^ 160)
  bytes.toList === (List.range 32).map fun i => UInt8.ofNat (n / 256 ^ (31 - i) % 256)
  (U256.fromBeBytes bytes).toNat === n
  -- Two's complement: Appendix H of the Yellow Paper.
  U256.toSigned w === (if n < 2 ^ 255 then (n : Int) else (n : Int) - 2 ^ 256)
  (U256.fromSigned (U256.toSigned w)).toNat === n
  -- An address is the low 20 bytes: the word modulo `2 ^ 160`.
  let address := toAddressMasked w
  address.toList === (List.range 20).map fun i => UInt8.ofNat (n / 256 ^ (19 - i) % 256)
  (Address.toU256 address).toNat === n % 2 ^ 160
  toAddressMasked (Address.toU256 address) === address

/-- An integer outside the range of a signed word reduces modulo `2 ^ 256`, as the text says. -/
def fromSigned : Property IO := pureIO do
  let magnitude ← forAll (Gen.frequency [(3, genWord), (1, (· * 2 ^ 200) <$> genWord)])
  let negative ← forAll Gen.bool
  let v : Int := if negative then -(magnitude : Int) else magnitude
  classify "inside the range" (decide (-(2 : Int) ^ 255 ≤ v ∧ v < 2 ^ 255))
  classify "outside the range" (decide (v < -(2 : Int) ^ 255 ∨ 2 ^ 255 ≤ v))
  ((U256.fromSigned v).toNat : Int) === v % 2 ^ 256

/-- Byte strings: the fixed-length forms, a read at an offset, and both exclusive ors.

`xorByteArray` keeps the length of the first string and reads zero past the end of the second. -/
def byteStrings : Property IO := pureIO do
  let a ← forAllWith bytesHex (Gen.bytes (.linear 0 40))
  let b ← forAllWith bytesHex (Gen.frequency [
    (2, Gen.bytes (.singleton a.size)), (3, Gen.bytes (.linear 0 40))])
  let n ← forAll (Gen.frequency [(2, pure a.size), (1, Gen.nat (.linear 0 41))])
  classify "the second string is shorter" (b.size < a.size)
  classify "the second string is longer" (b.size > a.size)
  classify "the lengths are equal" (b.size == a.size)
  classify "exactBytes? gets the exact length" (n == a.size)
  -- The exclusive or, byte by byte, over the length of the first.
  (xorByteArray a b).toList ===
    (List.range a.size).map fun i => a.toList[i]! ^^^ (b.toList[i]?.getD 0)
  -- The fixed-length forms.
  (exactBytes? n a).map (·.toList) === (if a.size = n then some a.toList else none)
  if h : a.size = n then
    let v : Vector UInt8 n := ⟨a.data, h⟩
    (packBytes v).toList === a.toList
    if h2 : b.size = n then
      (xorBytes v ⟨b.data, h2⟩).toList === (a.toList.zip b.toList).map fun (x, y) => x ^^^ y
  -- A read at an offset, and a byte past the end.
  let offset ← forAll (Gen.nat (.constant 0 (a.size + 2)))
  let count ← forAll (Gen.nat (.constant 0 (a.size + 2)))
  classify "the read reaches the end" (offset + count == a.size)
  if h : offset + count ≤ a.size then
    (readBytes a offset count h).toList === (a.toList.drop offset).take count
  byteAt a offset === (a.toList[offset]?.getD 0)

/-- Hexadecimal: digits of bytes, a number padded to a width, and the value of every digit. -/
def hexadecimal : Property IO := pureIO do
  let bytes ← forAll (genByteList (.linear 0 20))
  let lower := "0123456789abcdef".toList
  hexString bytes === "0x" ++ String.ofList (bytes.flatMap fun b =>
    [lower[b.toNat / 16]!, lower[b.toNat % 16]!])
  -- A number: at least `width` digits, and all of its digits when it has more.
  let value ← forAll (Gen.frequency [(1, Gen.nat (.linear 0 300)), (2, genNatBits 80)])
  let digits := if value = 0 then 1 else Nat.log2 value / 4 + 1
  let width ← forAll (Gen.frequency [
    (2, Gen.nat (.constant 0 24)), (3, (fun d => digits + d - 1) <$> Gen.nat (.constant 0 2))])
  classify "the width is below the digits" (width < digits)
  classify "the width is the digits" (width == digits)
  classify "the width is above the digits" (width > digits)
  let text := hexNat width value
  text.length === 2 + max width digits
  ensure (text.toList.take 2 == ['0', 'x']) "no 0x marker"
  let read := (text.toList.drop 2).foldl (fun acc c => acc * 16 + (lower.idxOf c)) 0
  ensure ((text.toList.drop 2).all lower.contains) "a character is not a lower-case digit"
  read === value
  -- The value of a digit, for any character.
  let c ← forAll (Gen.frequency [(3, Gen.element "0123456789abcdefABCDEF/:@G`g".toList),
    (1, Gen.ascii), (1, Gen.unicode)])
  let want : Option UInt8 :=
    if c.toNat ≥ 48 && c.toNat ≤ 57 then some (UInt8.ofNat (c.toNat - 48))
    else if c.toNat ≥ 97 && c.toNat ≤ 102 then some (UInt8.ofNat (c.toNat - 87))
    else if c.toNat ≥ 65 && c.toNat ≤ 70 then some (UInt8.ofNat (c.toNat - 55))
    else none
  classify "the character is a digit" want.isSome
  hexValue? c === want

/-- A bound on a length is the comparison with the length, for both instances. -/
def lengths : Property IO := pureIO do
  let l ← forAll (Gen.list (.linear 0 20) (pure ()))
  let n ← forAll (Gen.frequency [
    (3, (fun d => l.length + d - 1) <$> Gen.nat (.constant 0 2)), (2, Gen.nat (.linear 0 25))])
  classify "the bound is the length" (n == l.length)
  classify "the bound is below the length" (n < l.length)
  classify "the bound is above the length" (n > l.length)
  Length.hasAtLeast n l === decide (n ≤ l.length)
  (@decide (n ≤ l.length) (Length.decideLeLength n l)) === decide (n ≤ l.length)
  (@decide (l.length < n) (Length.decideLengthLt l n)) === decide (l.length < n)

/-- Checked conversions and the remaining 64-bit helpers, at the edges of the word. -/
def uint64 : Property IO := pureIO do
  let n ← forAll (Gen.frequency [
    (3, genNatBits 64), (2, (2 ^ 64 + ·) <$> Gen.nat (.exponential 0 (2 ^ 70))),
    (1, genAround (2 ^ 64) (2 ^ 65))])
  classify "the number fits 64 bits" (n < 2 ^ 64)
  classify "the number is exactly 2 ^ 64" (n == 2 ^ 64)
  (match Uint64.ofNatChecked n with
    | .ok x => some x.toNat
    | .error _ => none) === (if n < 2 ^ 64 then some n else none)
  let (a, b) ← forAll (Gen.zip genUInt64 (Gen.frequency [(3, genUInt64), (1, pure 0)]))
  let near ← forAll (Gen.nat (.constant 0 2))
  -- A second operand one below, at and one above the first.
  let c := UInt64.ofNat (a.toNat + near - 1)
  classify "saturating: the operands are equal" (c == a)
  (Uint64.saturatingSub a c).toNat === a.toNat - c.toNat
  (Uint64.saturatingSub a b).toNat === a.toNat - b.toNat
  (Uint64.subChecked a c).toOption.map (·.toNat) ===
    (if c.toNat ≤ a.toNat then some (a.toNat - c.toNat) else none)
  Uint64.subChecked a c === (if c ≤ a then .ok (a - c) else .error (.underflow a c))
  -- The integer square root, at a square, one below and one above.
  let root ← forAll (Gen.frequency [(3, genNatBits 32), (1, pure (2 ^ 32 - 1))])
  let square := root * root + near - 1
  if square < 2 ^ 64 then
    let got := (Uint64.integerSquareroot (UInt64.ofNat square)).toNat
    ensure (got * got ≤ square && square < (got + 1) * (got + 1)) "not the integer square root"
  GWEI_TO_WEI === 1000000000
  (Base.ensure (a ≤ b) "error" : Except String Unit) === (if a ≤ b then .ok () else .error "error")

/-- The gas limit toward a target is the limit that the rule of Gloas calls compatible.

The rule is `is_gas_limit_target_compatible` of the consensus specifications.

The oracle transcribes it.

It is also the closest limit that EIP-1559 accepts.

EIP-1559 accepts a limit that differs from the parent's by less than a 1024th of it.

The smallest gas limit, 5000, is not this function's: the payload build raises its target. -/
def gasLimit (oracle : Oracle) : Property IO := propertyM do
  let parent ← forAll (Gen.frequency [
    (2, Gen.nat (.constant 0 4100)), (2, (fun (k, d) => 1024 * k + d - 1) <$>
      Gen.zip (Gen.nat (.constant 1 40)) (Gen.nat (.constant 0 2))),
    (1, pure 5000), (3, genNatBits 40)])
  let step := parent / 1024 - 1
  let target ← forAll (Gen.frequency [
    (3, (fun d => (parent + step + d) - 2) <$> Gen.nat (.constant 0 4)),
    (3, (fun d => (parent + d) - (step + 2)) <$> Gen.nat (.constant 0 4)),
    (1, pure parent), (1, pure 0), (2, genNatBits 41)])
  pure do
    let limit := gasLimitToward parent target
    let bound := parent / 1024
    classify "the target is within one step" (limit == target)
    classify "the target is above the step" (target > limit)
    classify "the target is below the step" (target < limit)
    classify "the target is exactly one step away" (target == parent + step ||
      target + step == parent)
    classify "the target is one past the step" (target == parent + step + 1 ||
      target + step + 1 == parent)
    classify "the parent is below 2048, so the limit cannot move" (parent < 2048)
    classify "the limit is below 5000" (limit < 5000)
    toString limit === (← oracle.ask ["gaslimit", toString parent, toString target])
    -- EIP-1559: strictly less than a 1024th of the parent's away, or the parent's itself.
    ensure (limit == parent || ((limit : Int) - parent).natAbs < bound) "out of bounds"
    ensure (limit == target ||
      (¬ ((limit + 1 : Int) - parent).natAbs < bound ∨ target < limit) ∧
      (¬ ((limit : Int) - 1 - parent).natAbs < bound ∨ limit < target)) "a closer limit is valid"

end KernelsProperty.Base

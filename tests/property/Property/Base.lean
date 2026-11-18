import Hedgehog
import Support
import EthLib.Base

/-!
# The base layer, on generated inputs

Each property generates inputs and requires an answer that EthLib did not compute: the one of a
reference implementation (`oracle/base.py`), or of arithmetic on `Nat` and `Int`.

    lake exe base-property            # 100 cases of each
    lake exe base-property 10000
-/

open Hedgehog Support EthLib EthLib.Base

namespace BaseProperty

/-! ## Base64 -/

/-- The encoder writes the text of the reference. -/
def base64Encode (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAll (genBytes (.linear 0 64))
  pure do
    let text := Base64.encode bytes
    (if text.isEmpty then "-" else text) === (← oracle.ask ["b64enc", hex bytes])

/-- A text over the alphabet and a little outside it, of a length that reaches every tail. -/
def genBase64Text : Gen String :=
  Gen.string (.linear 0 12) (Gen.frequency [
    (8, Gen.element "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList),
    (1, Gen.element "=+/ ".toList)])

/-- The decoder accepts the canonical texts, and gives the bytes of the reference. -/
def base64Decode (oracle : Oracle) : Property IO := propertyM do
  let text ← forAll genBase64Text
  pure do
    let expected ← oracle.ask ["b64dec", hex text.toUTF8]
    match Base64.decode text with
    | .ok bytes => hex bytes === expected
    | .error _ => expected === "error"

/-! ## NFKD -/

/-- A code point: mostly from the blocks that decompose or combine. -/
def genChar : Gen Char :=
  Gen.frequency [
    (2, Gen.char (.constant 'a' 'z')),
    (3, Gen.char (.constant (Char.ofNat 0xA0) (Char.ofNat 0x36F))),
    (2, Gen.char (.constant (Char.ofNat 0x900) (Char.ofNat 0x33FF))),
    (2, Gen.char (.constant (Char.ofNat 0xAC00) (Char.ofNat 0xD7A3))),
    (2, Gen.char (.constant (Char.ofNat 0xF900) (Char.ofNat 0xFFEF))),
    (2, Gen.char (.constant (Char.ofNat 0x10000) (Char.ofNat 0x1FBFF))),
    (1, Gen.unicode)]

/-- Code points in hexadecimal. -/
def points (chars : List Char) : List String := chars.map fun c => String.ofList (Nat.toDigits 16 c.toNat)

/-- NFKD is the host's, on the code points the host knows. -/
def nfkd (oracle : Oracle) : Property IO := propertyM do
  let chars ← forAllWith (fun cs => " ".intercalate (points cs)) (Gen.list (.linear 0 8) genChar)
  pure do
    let expected ← oracle.ask ("nfkd" :: points chars)
    if expected = "skip" then pure ()
    else
      let got := points (Unicode.nfkd (String.ofList chars)).toList
      (if got.isEmpty then "-" else " ".intercalate got) === expected

/-! ## Integers -/

/-- The integer square root is the reference's. -/
def squareRoot (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll genUInt64
  pure do
    toString (Uint64.integerSquareroot n).toNat === (← oracle.ask ["isqrt", toString n.toNat])

/-- Checked arithmetic is arithmetic on `Nat`, and an error exactly out of range. -/
def checked : Property IO := pureIO do
  let a ← forAll genUInt64
  let b ← forAll genUInt64
  let agrees (got : Except ArithError UInt64) (want : Option Nat) : Bool :=
    match got, want with
    | .ok x, some n => x.toNat == n && n < 2 ^ 64
    | .error _, some n => n ≥ 2 ^ 64
    | .error _, none => true
    | .ok _, none => false
  ensure (agrees (Uint64.addChecked a b) (some (a.toNat + b.toNat))) "addChecked"
  ensure (agrees (Uint64.mulChecked a b) (some (a.toNat * b.toNat))) "mulChecked"
  ensure (agrees (Uint64.subChecked a b) (if b ≤ a then some (a.toNat - b.toNat) else none)) "subChecked"
  ensure (agrees (Uint64.divChecked a b) (if b = 0 then none else some (a.toNat / b.toNat))) "divChecked"
  (Uint64.saturatingSub a b).toNat === a.toNat - b.toNat

/-- A 256-bit word read as two's complement and written back. -/
def signed : Property IO := pureIO do
  let n ← forAll (genNatBits 256)
  let w : U256 := BitVec.ofNat 256 n
  let v := U256.toSigned w
  ensure (-(2 : Int) ^ 255 ≤ v ∧ v < 2 ^ 255) "toSigned is out of range"
  ensure (v % 2 ^ 256 == (n : Int)) "toSigned is not the word modulo 2^256"
  (U256.fromSigned v).toNat === n

/-- Big-endian and little-endian bytes are the digits of the number. -/
def endian : Property IO := pureIO do
  let len ← forAll (Gen.nat (.linear 0 40))
  let n ← forAll (genNatBits (8 * len))
  let be := natToBytes len n
  be.length === len
  bytesToNat be === n
  let le := (uintToBytes len n).toList
  le === be.reverse
  bytesToUint (uintToBytes len n) === n

/-- Hexadecimal text reads back, in either case, and nothing else reads. -/
def hexRoundTrip : Property IO := pureIO do
  let bytes ← forAll (genByteList (.linear 0 40))
  let marked := hexString bytes
  ensure (marked.toList.take 2 == ['0', 'x']) "no 0x marker"
  let text := String.ofList (marked.toList.drop 2)
  ensure ((hexBytes? text.toList).map (·.toList) == some bytes) "lower case does not read back"
  ensure ((hexBytes? text.toUpper.toList).map (·.toList) == some bytes) "upper case does not read back"
  let junk ← forAll (Gen.string (.linear 0 6) Gen.ascii)
  let valid := junk.length % 2 == 0 && junk.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  (hexBytes? junk.toList).isSome === valid

/-- The gas limit moves toward the target and stays within the bound of a child. -/
def gasLimit : Property IO := pureIO do
  let parent ← forAll (genNatBits 40)
  let target ← forAll (Gen.choice [genNatBits 40, (parent + ·) <$> Gen.nat (.linear 0 5000),
    (parent - ·) <$> Gen.nat (.linear 0 5000)])
  let limit := gasLimitToward parent target
  let delta := parent / 1024
  -- EIP-1559: the limit differs from the parent's by less than a 1024th of it.
  ensure (limit == parent || ((limit : Int) - parent).natAbs < delta) "the limit is out of bounds"
  ensure (((limit : Int) - target).natAbs ≤ ((parent : Int) - target).natAbs) "the limit moved away"
  -- No valid limit is closer to the target.
  ensure (limit == target ||
    (¬ ((limit + 1 : Int) - parent).natAbs < delta ∨ target < limit) ∧
    (¬ ((limit : Int) - 1 - parent).natAbs < delta ∨ limit < target)) "a closer limit is valid"

end BaseProperty

open BaseProperty in
def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "base"
  let ok ← checkGroup "base" [
    ("base64 encodes as RFC 4648", (base64Encode oracle).withTests cases),
    ("base64 decodes the canonical texts only", (base64Decode oracle).withTests cases),
    ("NFKD is the host's", (nfkd oracle).withTests cases),
    ("the integer square root", (squareRoot oracle).withTests cases),
    ("checked 64-bit arithmetic", checked.withTests cases),
    ("two's complement of a word", signed.withTests cases),
    ("big-endian and little-endian bytes", endian.withTests cases),
    ("hexadecimal reads back", hexRoundTrip.withTests cases),
    ("the gas limit toward a target", gasLimit.withTests cases)]
  pure (if ok then 0 else 1)

import Hedgehog
import Support

/-!
# What the properties of the public-key layer share

Generators biased to the edges of a modulus, and the text forms of the oracle's protocol.
-/

open Hedgehog Support

namespace CurvesProperty

/-- A number near the edges of `[0, modulus]`, or anywhere below `2 ^ bits`.

Most of the draws sit within a few units of `0`, half the modulus, the modulus and `2 ^ bits`. -/
def genNear (modulus : Nat) (bits : Nat := 256) : Gen Nat :=
  let top := 2 ^ bits - 1
  let near (centre : Nat) : Gen Nat :=
    (fun d : Int => (((centre : Int) + d).toNat) % (top + 1)) <$> Gen.int (.linearFrom 0 (-3) 3)
  Gen.frequency [
    (3, near 0), (3, near modulus), (2, near (modulus / 2)), (1, near top),
    (2, Gen.nat (.exponential 0 top)),
    (2, (modulus - ·) <$> Gen.nat (.exponential 0 modulus)),
    (4, Gen.nat (.constant 0 top))]

/-- A scalar in `[1, modulus - 1]`, small, large or anywhere. -/
def genScalar (modulus : Nat) : Gen Nat :=
  Gen.frequency [
    (2, Gen.nat (.exponential 1 (modulus - 1))),
    (2, (modulus - ·) <$> Gen.nat (.exponential 1 (modulus - 1))),
    (3, Gen.nat (.constant 1 (modulus - 1)))]

/-- `a ^ e mod m` on `Nat`, by squaring; the exponent halves at each step. -/
def modPow (m a e : Nat) : Nat := Id.run do
  let mut (result, base, e) := (1 % m, a % m, e)
  while e > 0 do
    if e % 2 = 1 then result := result * base % m
    base := base * base % m
    e := e / 2
  return result

/-- The 32 big-endian bytes of a number below `2 ^ 256`. -/
def vec32 (n : Nat) : Vector UInt8 32 :=
  Vector.ofFn fun i => UInt8.ofNat (n >>> (8 * (31 - i.val)))

/-- The `len` big-endian bytes of a number. -/
def beBytes (len n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := len) fun i => UInt8.ofNat (n >>> (8 * (len - 1 - i.val)))⟩

/-- The number that big-endian bytes write. -/
def beNat (bytes : ByteArray) : Nat := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- A byte vector in hexadecimal. -/
def hexVec {n : Nat} (v : Vector UInt8 n) : String := hex ⟨v.toArray⟩

/-- The words of an answer, separated by spaces. -/
def words (answer : String) : List String := answer.splitOn " "

/-- A point in the oracle's form: `inf`, or the two coordinates. -/
def showPoint (p : Option (Nat × Nat)) : String :=
  match p with
  | none => "inf"
  | some (x, y) => s!"{x},{y}"

/-- The bytes with one bit flipped, the bit that `pick` names; empty bytes stay empty. -/
def flipBit (bytes : ByteArray) (pick : Nat) : ByteArray :=
  if bytes.size = 0 then bytes
  else
    let bit := pick % (8 * bytes.size)
    bytes.set! (bit / 8) (bytes[bit / 8]! ^^^ (1 <<< UInt8.ofNat (bit % 8)))

/-- A vector with one bit flipped. -/
def flipVec {n : Nat} (v : Vector UInt8 n) (pick : Nat) : Vector UInt8 n :=
  if h : n = 0 then v
  else
    let bit := pick % (8 * n)
    have : bit / 8 < n := by
      have := Nat.mod_lt pick (show 8 * n > 0 by omega)
      omega
    v.set (bit / 8) (v[bit / 8] ^^^ (1 <<< UInt8.ofNat (bit % 8)))

end CurvesProperty

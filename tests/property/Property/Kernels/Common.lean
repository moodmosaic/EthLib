import Hedgehog
import Support

/-!
# What the properties of the kernels share

Arithmetic on `Nat` that EthLib did not compute, and generators biased to the edges of a limb.
-/

open Hedgehog Support

namespace KernelsProperty

/-- `a ^ e mod m` on `Nat`, by squaring. -/
def modPow (m a e : Nat) : Nat := Id.run do
  let mut (result, base, e) := (1 % m, a % m, e)
  while e > 0 do
    if e % 2 = 1 then result := result * base % m
    base := base * base % m
    e := e / 2
  return result

/-- The inverse of `a` mod `m` when the two are coprime, by the extended Euclidean algorithm. -/
def modInv (m a : Nat) : Nat := Id.run do
  let mut (r0, r1) : Int × Int := (m, a % m)
  let mut (t0, t1) : Int × Int := (0, 1)
  while r1 != 0 do
    let q := r0 / r1
    (r0, r1) := (r1, r0 - q * r1)
    (t0, t1) := (t1, t0 - q * t1)
  return (t0 % m).toNat

/-- Whether `n` passes the Miller-Rabin test to the first twelve prime bases. -/
def probablyPrime (n : Nat) : Bool :=
  let bases := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
  if n < 2 then false
  else if bases.contains n then true
  else if bases.any (n % · == 0) then false
  else Id.run do
    let mut (d, r) := (n - 1, 0)
    while d % 2 == 0 do
      (d, r) := (d / 2, r + 1)
    for a in bases do
      let mut x := modPow n a d
      if x == 1 || x == n - 1 then continue
      let mut witness := true
      for _ in [1:r] do
        x := x * x % n
        if x == n - 1 then
          witness := false
          break
      if witness then return false
    return true

/-- One limb of 32 bits: all zeros, all ones, one bit, or any value. -/
def genLimb : Gen Nat :=
  Gen.frequency [(3, pure 0), (3, pure (2 ^ 32 - 1)), (1, pure 1), (1, pure (2 ^ 31)),
    (1, pure (2 ^ 32 - 2)), (3, Gen.nat (.constant 0 (2 ^ 32 - 1)))]

/-- A number of `n` limbs, each drawn apart, so that runs of all-ones limbs are common. -/
def genLimbs (n : Nat) : Gen Nat :=
  (fun limbs => limbs.foldl (fun acc limb => acc * 2 ^ 32 + limb) 0) <$>
    Gen.list (.singleton n) genLimb

/-- A number within three of a centre, and below `bound`. -/
def genAround (centre bound : Nat) : Gen Nat :=
  (fun d : Int => ((centre : Int) + d).toNat % bound) <$> Gen.int (.linearFrom 0 (-3) 3)

/-- A number below `2 ^ bits`: near `0`, `m / 2`, `m` and `2 ^ bits`, limb patterns, or any. -/
def genNear (m bits : Nat) : Gen Nat :=
  let bound := 2 ^ bits
  Gen.frequency [
    (3, genAround 0 bound), (3, genAround m bound), (1, genAround (m / 2) bound),
    (1, genAround (bound - 1) bound), (2, Gen.nat (.exponential 0 (bound - 1))),
    (2, (· % bound) <$> genLimbs ((bits + 31) / 32)),
    (4, Gen.nat (.constant 0 (bound - 1)))]

/-- The `len` big-endian bytes of a number, its higher bytes dropped. -/
def beBytes (len n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := len) fun i => UInt8.ofNat (n >>> (8 * (len - 1 - i.val)))⟩

/-- The number that big-endian bytes write. -/
def beNat (bytes : ByteArray) : Nat := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The words of an answer, separated by spaces. -/
def words (answer : String) : List String := answer.splitOn " "

/-- The numbers of an answer, separated by spaces. -/
def numbers (answer : String) : List Nat := (words answer).filterMap String.toNat?

/-- Numbers as the words of a command. -/
def showNats (xs : List Nat) : String := " ".intercalate (xs.map toString)

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

end KernelsProperty

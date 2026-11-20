import Property.Curves.Common
import EthLib.Cryptography.Secp256k1
import EthLib.Cryptography.Bls

/-!
# The arithmetic kernels against arithmetic on `Nat`

Montgomery limbs, the extended Euclidean inverse, and the Jacobian formulas.

The Jacobian formulas run on curves over small primes.

There equal and opposite points, and points of order two, turn up in every few cases.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.Kernels

/-- Montgomery limbs of the base field of secp256k1 are the integers mod `p`. -/
def montgomery : Property IO := pureIO do
  let p := Secp256k1.Fp.modulus
  let (a, b) ← forAll (Gen.zip (genNear p) (genNear p))
  let (x, y) : Secp256k1.Fp.Montgomery × Secp256k1.Fp.Montgomery :=
    (Montgomery.ofNat a, Montgomery.ofNat b)
  classify "a is p or more, so it is reduced" (a ≥ p)
  classify "a is zero mod p" (a % p == 0)
  classify "a + b is p or more" (a % p + b % p ≥ p)
  classify "a is below b, so the difference borrows" (a % p < b % p)
  x.toNat === a % p
  (x + y).toNat === (a + b) % p
  (x - y).toNat === (a % p + p - b % p) % p
  (x * y).toNat === a * b % p
  (-x).toNat === (p - a % p) % p
  (Montgomery.pow x b).toNat === modPow p a b
  (Montgomery.inv x).toNat === modPow p a (p - 2)
  (Montgomery.toFin x).val === a % p
  (Montgomery.ofFin (M := Secp256k1.Fp.params) (Fin.ofNat _ a)).toNat === a % p
  beNat (Montgomery.toBytesBE x) === a % p
  ensure ((x == y) == (a % p == b % p)) "equality of forms is not equality mod p"

/-- Bytes read at an offset are the number of the 32 bytes from there, with zeros past the end.

The read gives nothing for a number of `p` or more. -/
def montgomeryBytes : Property IO := pureIO do
  let p := Secp256k1.Fp.modulus
  let a ← forAll (genNear p)
  -- The number is whole in three cases of four; a buffer that ends early reads zeros there.
  let (before, cut) ← forAll (Gen.zip (Gen.nat (.linear 0 5))
    (Gen.frequency [(3, Gen.nat (.constant 32 34)), (1, Gen.nat (.constant 0 31))]))
  let bytes := (ByteArray.mk (Array.replicate before 0xff) ++ beBytes 32 a).extract 0 (before + cut)
  let read : Option Secp256k1.Fp.Montgomery := Montgomery.ofBytesBE bytes before
  let value := beNat (bytes.extract before (before + 32)) * 256 ^ (32 - min cut 32)
  classify "read: a number below p" (value < p)
  classify "refused: exactly p" (value == p)
  classify "refused: above p" (value > p)
  classify "the buffer ends before the 32 bytes" (cut < 32)
  read.map (·.toNat) === (if value < p then some value else none)

/-- The extended Euclidean coefficient times `a` is the gcd, mod any modulus. -/
def inverse : Property IO := pureIO do
  let m ← forAll (Gen.frequency [(3, Gen.nat (.linear 1 200)), (2, Gen.nat (.exponential 1
      (2 ^ 256))),
    (1, pure Secp256k1.Fn.modulus), (1, pure Bls.Fp.modulus)])
  let a ← forAll (Gen.frequency [(1, Gen.nat (.linear 0 4)), (3, Gen.nat (.exponential 0
      (2 ^ 260)))])
  if h : m = 0 then discard else
    have : NeZero m := ⟨h⟩
    let x : Fin m := Fin.ofNat m a
    classify "coprime, so an inverse" (Nat.gcd x.val m == 1)
    classify "not coprime, so no inverse" (Nat.gcd x.val m != 1)
    classify "zero" (x.val == 0)
    classify "the modulus is 1" (m == 1)
    let inv := Fin.inverse x
    (inv.val * x.val) % m === Nat.gcd x.val m % m

/-- A point of a small curve: none is the point at infinity. -/
abbrev Affine := Option (Nat × Nat)

/-- The group law of SEC 1 v2 section 2.2.1 on integers mod a prime `q`. -/
def modelAdd (q a : Nat) (p1 p2 : Affine) : Affine :=
  match p1, p2 with
  | none, other => other
  | other, none => other
  | some (x1, y1), some (x2, y2) =>
    if x1 == x2 && (y1 + y2) % q == 0 then none
    else
      let slope := if x1 == x2 then (3 * x1 * x1 + a) * modPow q (2 * y1) (q - 2) % q
        else (y2 + q - y1) * modPow q (x2 + q - x1) (q - 2) % q
      let x3 := (slope * slope + 2 * q - x1 - x2) % q
      some (x3, (slope * (x1 + q - x3) + q - y1) % q)

/-- `k P` by adding `P` to itself; the scalars of a small curve are small. -/
def modelMul (q a k : Nat) (pt : Affine) : Affine :=
  (List.range k).foldl (fun acc _ => modelAdd q a acc pt) none

/-- The points of `y^2 = x^3 + a x + b` mod `q`, by trying every pair. -/
def curvePoints (q a b : Nat) : List (Nat × Nat) :=
  (List.range q).flatMap fun x => (List.range q).filterMap fun y =>
    if y * y % q == (x * x * x + a * x + b) % q then some (x, y) else none

/-- The Jacobian formulas agree with the affine group law, on a curve over `q`. -/
def jacobianOn (q : Nat) [NeZero q] : Property IO := pureIO do
  -- A singular curve has no group law, and a curve needs a point besides `O`.
  let (a, b) ← forAll (Gen.filter (fun (a, b) => (4 * a * a * a + 27 * b * b) % q != 0 &&
    !(curvePoints q a b).isEmpty) (Gen.zip (Gen.nat (.constant 0 (q - 1)))
      (Gen.nat (.constant 0 (q - 1)))))
  let points := curvePoints q a b
  let pick : Gen Affine := Gen.frequency [(1, pure none), (8, some <$> Gen.element points)]
  let (p1, p2) ← forAll (Gen.zip pick pick)
  let same ← forAll (Gen.element [0, 0, 1, 2])
  let p2 := match same, p1 with
    | 1, _ => p1
    | 2, some (x, y) => some (x, (q - y) % q)
    | _, _ => p2
  let (k, l) ← forAll (Gen.zip (Gen.nat (.linear 0 300)) (Gen.nat (.linear 0 300)))
  let (z1, z2) ← forAll (Gen.zip (Gen.nat (.constant 1 (q - 1))) (Gen.nat (.constant 1 (q - 1))))
  let fa : Fin q := Fin.ofNat q a
  classify "P = Q, a doubling" (p1 == p2 && p1.isSome)
  classify "P = -Q, the point at infinity" (p1.isSome && modelAdd q a p1 p2 == none)
  classify "P is at infinity" p1.isNone
  classify "Q is at infinity" p2.isNone
  classify "P has order two" (p1.any fun (_, y) => y == 0)
  classify "a = 0" (a == 0)
  classify "the scalar is zero" (k == 0)
  -- The form `(x z^2, y z^3, z)` of a point, for any `z` but zero.
  let form (pt : Affine) (z : Nat) : Jacobian q :=
    match pt with
    | none => ⟨Fin.ofNat q (z * 3), Fin.ofNat q z, 0⟩
    | some (x, y) => ⟨Fin.ofNat q (x * z * z), Fin.ofNat q (y * z * z * z), Fin.ofNat q z⟩
  let back (pt : Jacobian q) : Affine := pt.toAffine.map fun (x, y) => (x.val, y.val)
  for (j1, j2) in [(form p1 1, form p2 1), (form p1 z1, form p2 1), (form p1 1, form p2 z2),
      (form p1 z1, form p2 z2)] do
    back j1 === p1
    back (Jacobian.add fa j1 j2) === modelAdd q a p1 p2
    back (Jacobian.double fa j1) === modelAdd q a p1 p1
    back (Jacobian.mulBits fa 9 k j1) === modelMul q a k p1
    back (Jacobian.mulAdd fa 9 k j1 l j2) ===
      modelAdd q a (modelMul q a k p1) (modelMul q a l p2)

end CurvesProperty.Kernels

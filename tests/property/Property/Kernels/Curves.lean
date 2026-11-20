import Property.Kernels.Common
import EthLib.Cryptography.Jacobian
import EthLib.Cryptography.Secp256k1
import EthLib.Cryptography.Secp256r1

/-!
# The Jacobian formulas on every kind of curve

`Cryptography/Jacobian.lean` is written once for any field and any coefficient `a`.

Here the curve is generated over a small prime, so that the rare cases are common.

They are equal points, opposite points, the point at infinity and points of order two.

The answer is the affine group law of SEC 1 v2 section 2.2.1 on `Nat`.

The curves of Ethereum then run at the scalars at the edges of their order.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace KernelsProperty.Curves

/-- A point of a curve over a small prime: none is the point at infinity. -/
abbrev Affine := Option (Nat × Nat)

/-- The group law of SEC 1 v2 section 2.2.1, on integers mod a prime `q`. -/
def affineAdd (q a : Nat) (p1 p2 : Affine) : Affine :=
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

/-- `k P` by adding `P` to itself `k` times. -/
def affineMul (q a k : Nat) (pt : Affine) : Affine :=
  (List.range k).foldl (fun acc _ => affineAdd q a acc pt) none

/-- The order of a point: the least positive `k` with `k P` at infinity. -/
def orderOf (q a : Nat) (pt : Affine) : Nat := Id.run do
  let mut acc := pt
  for k in [1:2 * q + 3] do
    if acc.isNone then return k
    acc := affineAdd q a acc pt
  return 0

/-- The points of `y^2 = x^3 + a x + b` over the integers mod `q`. -/
def pointsOf (q a b : Nat) : List (Nat × Nat) :=
  (List.range q).flatMap fun x => (List.range q).filterMap fun y =>
    if y * y % q == (x * x * x + a * x + b) % q then some (x, y) else none

/-- A curve over a small prime: the prime, `a`, `b`, and its points. -/
structure Curve where
  q : Nat
  a : Nat
  b : Nat
  deriving Repr

/-- A curve that is not singular, with `a = 0`, `a = -3` or any `a`. -/
def genCurve : Gen Curve := do
  let q ← Gen.element [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 97, 251]
  let a ← Gen.frequency [(2, pure 0), (2, pure (q - 3)), (3, Gen.nat (.constant 0 (q - 1)))]
  let b ← Gen.nat (.constant 0 (q - 1))
  -- At most two values of `b` make the curve singular for one `a`, so one of three is fine.
  let fine := [b, (b + 1) % q, (b + 2) % q].find? fun b => (4 * a ^ 3 + 27 * b ^ 2) % q != 0
  pure ⟨q, a, fine.getD 1⟩

/-- `Jacobian.add`, `double`, `mulBits`, `mulAdd` and `toAffine` are the affine group law. -/
def jacobian : Property IO := pureIO do
  let curve ← forAll genCurve
  let ⟨q, a, b⟩ := curve
  let points := pointsOf q a b
  -- The points of order two, with `y = 0`, are few: they get a weight of their own.
  let halves := points.filter fun (_, y) => y == 0
  let pick : Gen Affine :=
    if points.isEmpty then pure none
    else Gen.frequency ([(1, pure none), (7, some <$> Gen.element points)] ++
      (if halves.isEmpty then [] else [(2, some <$> Gen.element halves)]))
  let p1 ← forAll pick
  let negated : Affine := p1.map fun (x, y) => (x, (q - y) % q)
  let p2 ← forAll (Gen.frequency [(3, pick), (1, pure p1), (1, pure negated)])
  let (z1, z2) ← forAll (Gen.zip (Gen.nat (.constant 1 (q - 1)))
    (Gen.frequency [(1, pure 1), (2, Gen.nat (.constant 1 (q - 1)))]))
  let (junkX, junkY) ← forAll (Gen.zip (Gen.nat (.constant 0 (q - 1)))
    (Gen.nat (.constant 0 (q - 1))))
  let order := orderOf q a p1
  let fuel ← forAll (Gen.nat (.constant 0 10))
  let k ← forAll (Gen.frequency [
    (4, (fun d => (order + d) - 1) <$> Gen.nat (.constant 0 2)), (2, Gen.nat (.constant 0 2)),
    (1, pure (2 ^ fuel - 1)), (3, Gen.nat (.constant 0 (2 ^ fuel)))])
  let l ← forAll (Gen.nat (.constant 0 (2 ^ fuel - 1)))
  if h : q = 0 then discard else
  have : NeZero q := ⟨h⟩
  -- A point in Jacobian coordinates with the given `Z`; any `X` and `Y` at infinity.
  let lift (pt : Affine) (z : Nat) : Jacobian q :=
    match pt with
    | none => ⟨Fin.ofNat q junkX, Fin.ofNat q junkY, 0⟩
    | some (x, y) => ⟨Fin.ofNat q (x * z * z), Fin.ofNat q (y * z * z * z), Fin.ofNat q z⟩
  let lower (pt : Jacobian q) : Affine := pt.toAffine.map fun (x, y) => (x.val, y.val)
  let fa : Fin q := Fin.ofNat q a
  let (j1, j2) := (lift p1 z1, lift p2 z2)
  classify "a = 0" (a == 0)
  classify "a = -3" (a + 3 == q)
  classify "P is at infinity" p1.isNone
  classify "Q is at infinity" p2.isNone
  classify "P = Q, so the sum is a doubling" (p1 == p2 && p1.isSome)
  classify "P = -Q, so the sum is at infinity" (p1.isSome && p2 == negated)
  classify "P has order two" (p1.any fun (_, y) => y == 0)
  classify "Q has Z = 1" (z2 == 1 && p2.isSome)
  classify "the scalar is the order of P" (k == order)
  classify "the scalar is zero" (k == 0)
  classify "the scalar does not fit the fuel" (k ≥ 2 ^ fuel)
  lower j1 === p1
  lower (Jacobian.add fa j1 j2) === affineAdd q a p1 p2
  lower (Jacobian.double fa j1) === affineAdd q a p1 p1
  -- The text asks for a scalar below `2 ^ fuel`; a larger one loses its higher bits.
  lower (Jacobian.mulBits fa fuel k j1) === affineMul q a (k % 2 ^ fuel) p1
  lower (Jacobian.mulAdd fa fuel (k % 2 ^ fuel) j1 l j2) ===
    affineAdd q a (affineMul q a (k % 2 ^ fuel) p1) (affineMul q a l p2)
  lower (Jacobian.ofAffine (Fin.ofNat q junkX) (Fin.ofNat q junkY)) === some (junkX, junkY)
  lower (Jacobian.infinity : Jacobian q) === none

/-- Fails by design: `mulBits` gives `k P` also for a scalar of `2 ^ fuel` or more.

`Jacobian.mulBits` asks for `k < 2 ^ fuel`, and this property shows that the bound is needed.

A larger scalar loses its higher bits, as the property above pins. -/
def beyondFuel : Property IO := pureIO do
  let curve ← forAll genCurve
  let ⟨q, a, b⟩ := curve
  let points := pointsOf q a b
  let fuel ← forAll (Gen.nat (.constant 0 6))
  let k ← forAll (Gen.nat (.constant 0 200))
  if h : q = 0 then discard else
  have : NeZero q := ⟨h⟩
  let (x, y) ← forAll (if points.isEmpty then Gen.discard else Gen.element points)
  let pt : Jacobian q := Jacobian.ofAffine (Fin.ofNat q x) (Fin.ofNat q y)
  (Jacobian.mulBits (Fin.ofNat q a) fuel k pt).toAffine.map (fun (x, y) => (x.val, y.val)) ===
    affineMul q a k (some (x, y))

/-- A scalar at the edges of a group order `n`, of the field and of 256 bits. -/
def genScalar (n : Nat) : Gen Nat :=
  Gen.frequency [
    (3, Gen.element [0, 1, 2, n - 1, n, n + 1, 2 ^ 256 - 1, 2 ^ 255, n / 2, n / 2 + 1]),
    (1, genAround n (2 ^ 256)), (1, Gen.nat (.linear 0 40)), (2, genNatBits 256)]

/-- A point in the words of the oracle. -/
def showPoint (pt : Option (Nat × Nat)) : String :=
  match pt with
  | none => "inf"
  | some (x, y) => s!"{x},{y}"

/-- Scalar multiples of the generators of secp256k1 and P-256, at the edges of the order.

The first runs on Montgomery limbs with `a = 0`, the second on `Fin` with `a = -3`. -/
def generators (oracle : Oracle) : Property IO := propertyM do
  let k ← forAll (genScalar Secp256k1.Fn.modulus)
  let l ← forAll (genScalar Secp256r1.Fn.modulus)
  let opposite ← forAll Gen.bool
  pure do
    classify "k1: the scalar is 0 mod n" (k % Secp256k1.Fn.modulus == 0)
    classify "k1: the scalar is n - 1 or n + 1" (k + 1 == Secp256k1.Fn.modulus ||
      k == Secp256k1.Fn.modulus + 1)
    classify "k1: the scalar is above n" (k > Secp256k1.Fn.modulus)
    classify "r1: the scalar is 0 mod n" (l % Secp256r1.Fn.modulus == 0)
    classify "r1: the scalar is above n" (l > Secp256r1.Fn.modulus)
    let k1 : Option (Nat × Nat) := match Secp256k1.Point.mulBits 256 k .generator with
      | .infinity => none
      | .affine x y => some (x.val, y.val)
    showPoint k1 === (← oracle.ask ["mulg", "k1", toString k])
    let r1 : Option (Nat × Nat) := match Secp256r1.Point.mulBits 256 l .generator with
      | .infinity => none
      | .affine x y => some (x.val, y.val)
    showPoint r1 === (← oracle.ask ["mulg", "r1", toString l])
    -- `k G + l G` with one chain of doublings is `(k + l) G`.
    let n := Secp256k1.Fn.modulus
    let l := if opposite then n - k % n else l
    let both := Secp256k1.Point.mulAdd (Fin.ofNat n k) .generator (Fin.ofNat n l) .generator
    let sum : Option (Nat × Nat) := match both with
      | .infinity => none
      | .affine x y => some (x.val, y.val)
    classify "k1: the two products cancel" sum.isNone
    showPoint sum === (← oracle.ask ["mulg", "k1", toString ((k % n + l % n) % n)])

/-- The constants of secp256k1 and of P-256 are those of py_ecc and of OpenSSL. -/
def constants (oracle : Oracle) : Property IO := propertyM do
  pure do
    let k1 := numbers (← oracle.ask ["curve", "k1"])
    let (gx, gy) : Nat × Nat := match Secp256k1.Point.generator with
      | .affine x y => (x.val, y.val)
      | .infinity => (0, 0)
    [Secp256k1.Fp.modulus, Secp256k1.Fn.modulus, 0, Secp256k1.b.val, gx, gy] === k1
    let r1 := numbers (← oracle.ask ["curve", "r1"])
    let (hx, hy) : Nat × Nat := match Secp256r1.Point.generator with
      | .affine x y => (x.val, y.val)
      | .infinity => (0, 0)
    [hx, hy] === r1
    -- SEC 2 v2 section 2.4.2: the prime, `a = -3`, and `b` as FIPS 186-4 D.1.2.3 prints it.
    Secp256r1.Fp.modulus === 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
    Secp256r1.a.val + 3 === Secp256r1.Fp.modulus
    ensure (Secp256r1.Point.generator.isOnCurve) "the generator of P-256 is off the curve"
    ensure (Secp256k1.Point.generator.isOnCurve) "the generator of secp256k1 is off the curve"
    Secp256k1.Fp.modulus === 2 ^ 256 - 2 ^ 32 - 977

end KernelsProperty.Curves

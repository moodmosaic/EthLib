import Property.Curves.Common
import EthLib.Cryptography.AltBn128

/-!
# alt_bn128 against py_ecc and a model of the group law

EIP-196 gives the curve and EIP-197 the pairing check.

The points are multiples of the generators, often equal or opposite, and the point at infinity.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.Bn

open AltBn128

def r : Nat := Fr.modulus
def p : Nat := Fp.modulus

def render : Point → String
  | .infinity => "inf"
  | .affine x y => s!"{x.val},{y.val}"

def render2 : Point2 → String
  | .infinity => "inf"
  | .affine x y => s!"{x.c0.val},{x.c1.val},{y.c0.val},{y.c1.val}"

def g1 (k : Nat) : Point := Point.mulBits 256 k .generator
def g2 (k : Nat) : Point2 := Point2.mulBits 256 k .generator

/-- A scalar at the edges of `[0, r]` or anywhere below `2 ^ 256`. -/
def genK : Gen Nat := genNear r

/-- Two scalars, the second often equal or opposite to the first, mod `r`. -/
def genPair : Gen (Nat × Nat) := do
  let k ← genK
  let m ← Gen.frequency [(2, pure k), (2, pure ((r - k % r) % r)), (1, pure 0), (4, genK)]
  pure (k, m)

/-- The classes of a sum `k G + m G` and of a wide scalar, for the labels of a group law. -/
def classes (k m wide : Nat) : PropertyM Unit := do
  classify "P + Q with P = Q, a doubling" (k % r == m % r && k % r != 0)
  classify "P + Q with P = -Q, the point at infinity" ((k + m) % r == 0 && k % r != 0)
  classify "P + Q with two other points" (k % r != m % r && (k + m) % r != 0 && k % r != 0 &&
    m % r != 0)
  classify "P is at infinity" (k % r == 0)
  classify "Q is at infinity" (m % r == 0)
  classify "the scalar is 1" (k == 1)
  classify "the scalar is r - 1" (k + 1 == r)
  classify "the scalar is r" (k == r || wide == r)
  classify "the scalar is above r" (k > r || wide > r)
  classify "the scalar is zero" (k == 0 || wide == 0)

/-- The sum and the multiple on `G_1` are those of SEC 1 v2 section 2.2.1 on integers. -/
def group1 (oracle : Oracle) : Property IO := propertyM do
  let (k, m) ← forAll genPair
  let wide ← forAll genK
  classes k m wide
  pure do
    let (pk, pm) := (g1 k, g1 m)
    render pk === (← oracle.ask ["mul", "bn", toString k, "1,2"])
    render (pk + pm) === (← oracle.ask ["add", "bn", render pk, render pm])
    render (Point.mulBits 256 wide pm) === (← oracle.ask ["mul", "bn", toString wide, render pm])
    ensure (pk.isOnCurve && (pk + pm).isOnCurve) "a point left the curve"
    ensure (pk + pk.neg == .infinity) "P + (-P) is not O"

/-- The sum and the multiple on `G_2` are py_ecc's. -/
def group2 (oracle : Oracle) : Property IO := propertyM do
  let (k, m) ← forAll genPair
  let wide ← forAll genK
  classes k m wide
  pure do
    let g := render2 Point2.generator
    let (pk, pm) := (g2 k, g2 m)
    render2 pk === (← oracle.ask ["bng2mul", toString k, g])
    render2 (pk + pm) === (← oracle.ask ["bng2add", render2 pk, render2 pm])
    render2 (Point2.mulBits 256 wide pm) === (← oracle.ask ["bng2mul", toString wide, render2 pm])
    ensure (pk.isOnCurve && (pk + pm).isOnCurve) "a point left the twist"

/-- The sum and the multiple of points of the twist outside `G_2` are py_ecc's.

A multiple of the generator never leaves the subgroup, so these points come from the oracle.

The multiple reads the low `fuel` bits of its scalar, for any fuel. -/
def twist (oracle : Oracle) (special : Specials) : Property IO := propertyM do
  let pick := Gen.element special.bnTwist
  let (a, b) ← forAll (Gen.zip pick pick)
  let (k, m) ← forAll (Gen.zip (Gen.frequency [(1, pure 0), (1, pure 1), (1, pure r),
    (2, genK)]) (Gen.nat (.constant 0 9)))
  let same ← forAll (Gen.element [0, 0, 1, 2, 3])
  let fuel ← forAll (Gen.frequency [(2, pure 256), (1, Gen.element [0, 1, 8, 255, 257])])
  pure do
    let point (c : List Nat) : Point2 :=
      .affine ⟨Fin.ofNat _ (c.getD 0 0), Fin.ofNat _ (c.getD 1 0)⟩
        ⟨Fin.ofNat _ (c.getD 2 0), Fin.ofNat _ (c.getD 3 0)⟩
    -- A small multiple of a point stays outside the subgroup, and gives equal abscissae.
    let pa := Point2.mulBits 8 (m + 1) (point a)
    let negative : Point2 := match pa with
      | .affine x y => .affine x (Fp2.neg y)
      | .infinity => .infinity
    let pb := match same with
      | 1 => pa
      | 2 => negative
      | 3 => .infinity
      | _ => point b
    ensure (pa.isOnCurve && pb.isOnCurve) "a point is off the twist"
    classify "P + Q with P = Q, a doubling" (pa == pb)
    classify "P + Q with P = -Q, the point at infinity" (pb == negative)
    classify "Q is at infinity" (pb == .infinity)
    classify "P + Q with two other points" (same == 0 && a != b)
    classify "the scalar is r, and the multiple is not the point at infinity" (k == r)
    classify "the scalar does not fit the fuel" (k ≥ 2 ^ fuel)
    classify "no fuel" (fuel == 0)
    render2 (pa + pb) === (← oracle.ask ["bng2add", render2 pa, render2 pb])
    render2 (Point2.mulBits fuel k pa) === (← oracle.ask ["bng2mul", toString (k % 2 ^ fuel),
      render2 pa])
    ensure ((pa + pb).isOnCurve) "the sum left the twist"
    -- The order of the point does not divide `r`: it is outside `G_2`.
    ensure (Point2.mulBits 256 r pa != .infinity) "a point of the oracle is in the subgroup"

/-- The pairing is py_ecc's, coefficient by coefficient. -/
def pairingValue (oracle : Oracle) : Property IO := propertyM do
  let (a, b) ← forAll (Gen.zip (genScalar r) (genScalar r))
  pure do
    let got := " ".intercalate ((pairing (g1 a) (g2 b)).toList.map fun c => toString c.val)
    got === (← oracle.ask ["bnpairing", render (g1 a), render2 (g2 b)])

/-- Pairs whose product of pairings is one, then one of them changed or dropped. -/
def genPairs : Gen (List (Nat × Nat)) := do
  let (a, b) ← Gen.zip (genScalar r) (genScalar r)
  let balanced := [(a, b), ((r - a * b % r) % r, 1)]
  Gen.frequency [
    (3, pure balanced),
    (1, pure []),
    (1, pure [(a, b)]),
    (1, pure ((0, b) :: balanced)),
    (1, pure ((a, 0) :: balanced)),
    (1, pure [(0, 0)]),
    (1, pure [(a, b), ((a * b + 1) % r, 1)]),
    (1, pure [(a, b), (r - a, b)]),
    (1, pure [(a, b), (a, b), ((r - 2 * a * b % r) % r, 1)]),
    (1, pure [(a, b), (a, r - b), (a, 0)])]

/-- The pairing check is that of EIP-197: the product of the pairings is one. -/
def pairingChecks (oracle : Oracle) : Property IO := propertyM do
  let pairs ← forAll genPairs
  pure do
    let points := pairs.map fun (a, b) => (g1 a, g2 b)
    let expected ← oracle.ask
      ("bnpairingcheck" :: points.flatMap fun (pt, q) => [render pt, render2 q])
    let got := pairingCheck points
    classify "the product is one" got
    classify "the product is not one" (!got)
    classify "no pair" pairs.isEmpty
    classify "one pair" (pairs.length == 1)
    classify "three pairs" (pairs.length == 3)
    classify "a pair with the point at infinity of G1" (pairs.any fun (a, _) => a % r == 0)
    classify "a pair with the point at infinity of G2" (pairs.any fun (_, b) => b % r == 0)
    classify "every pair has a point at infinity" (!pairs.isEmpty &&
      pairs.all fun (a, b) => a % r == 0 || b % r == 0)
    (if got then "1" else "0") === expected

end CurvesProperty.Bn

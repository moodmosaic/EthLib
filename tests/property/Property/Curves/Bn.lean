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

/-- The sum and the multiple on `G_1` are those of SEC 1 v2 section 2.2.1 on integers. -/
def group1 (oracle : Oracle) : Property IO := propertyM do
  let (k, m) ← forAll genPair
  let wide ← forAll genK
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
  pure do
    let g := render2 Point2.generator
    let (pk, pm) := (g2 k, g2 m)
    render2 pk === (← oracle.ask ["bng2mul", toString k, g])
    render2 (pk + pm) === (← oracle.ask ["bng2add", render2 pk, render2 pm])
    render2 (Point2.mulBits 256 wide pm) === (← oracle.ask ["bng2mul", toString wide, render2 pm])
    ensure (pk.isOnCurve && (pk + pm).isOnCurve) "a point left the twist"

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
    (if pairingCheck points then "1" else "0") === expected

end CurvesProperty.Bn

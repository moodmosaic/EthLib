import Property.Curves.Common
import EthLib.Cryptography.Kzg

/-!
# The polynomial helpers of KZG against arithmetic on `Nat`

The helpers of the polynomial commitments specification, which the fast paths mostly bypass:

- Products.
- Division.
- Interpolation.
- The vanishing polynomial.
- The roots of unity.
- The bit reversal.
- The FFT.
- The evaluation in evaluation form.

A polynomial of the model is a list of numbers mod `r`, lowest coefficient first.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.KzgPoly

open Kzg Bls

def r : Nat := Fr.modulus

def toFr (xs : List Nat) : Array Fr := (xs.map Fr.ofNat).toArray
def ofFr (xs : Array Fr) : List Nat := xs.toList.map (·.val)

/-- A coefficient: zero, one, minus one, or any. -/
def genCoeff : Gen Nat :=
  Gen.frequency [(1, pure 0), (1, pure 1), (1, pure (r - 1)), (4, Gen.nat (.constant 0 (r - 1)))]

def genPoly (range : Range Nat) : Gen (List Nat) := Gen.list range genCoeff

/-- Horner's rule on `Nat`. -/
def horner (p : List Nat) (z : Nat) : Nat := p.foldr (fun c acc => (acc * z + c) % r) 0

/-- The sum, as long as the longer of the two. -/
def addModel (a b : List Nat) : List Nat :=
  (List.range (max a.length b.length)).map fun i => (a.getD i 0 + b.getD i 0) % r

/-- `multiply_polynomialcoeff` of the specification: from `[0]`, add `coef * x^power * b`. -/
def mulModel (a b : List Nat) : List Nat :=
  a.zipIdx.foldl (fun acc (coef, power) =>
    addModel acc (List.replicate power 0 ++ b.map (· * coef % r))) [0]

/-- The same polynomial: equal coefficients, up to zeros at the end. -/
def samePoly (a b : List Nat) : Bool :=
  (List.range (max a.length b.length)).all fun i => a.getD i 0 == b.getD i 0

/-- Sums, products and values of polynomials are those of the model. -/
def arithmetic : Property IO := pureIO do
  let (a, b) ← forAll (Gen.zip (genPoly (.linear 0 12)) (genPoly (.linear 0 12)))
  let z ← forAll genCoeff
  ofFr (addPolynomialcoeff (toFr a) (toFr b)) === addModel a b
  (multiplyPolynomialcoeff (toFr a) (toFr b)).toOption.map ofFr === some (mulModel a b)
  (evaluatePolynomialcoeff (toFr a) (Fr.ofNat z)).val === horner a z
  ofFr (computePowers (Fr.ofNat z) a.length) === (List.range a.length).map (modPow r z)

/-- The product of two long polynomials is refused when the sizes sum to more than 8192. -/
def productBound : Property IO := pureIO do
  let (m, n) ← forAll (Gen.zip (Gen.element [0, 1, 4095, 4096, 4097, 8191, 8192])
    (Gen.element [0, 1, 4095, 4096, 4097]))
  let a := Array.replicate m Fr.zero
  let b := Array.replicate n Fr.one
  (multiplyPolynomialcoeff a b).toOption.isSome === decide (m + n ≤ 8192)

/-- Division inverts the product: `(q b + rest) / b = q`, for `rest` shorter than `b`.

An empty divisor, or one that ends in zero, is refused. -/
def division : Property IO := pureIO do
  let (q, b) ← forAll (Gen.zip (genPoly (.linear 1 10)) (genPoly (.linear 0 8)))
  let lead ← forAll (Gen.frequency [(5, Gen.nat (.constant 1 (r - 1))), (1, pure 0)])
  let b := b ++ [lead]
  let rest ← forAll (genPoly (.constant 0 (b.length - 1)))
  let a := addModel (mulModel q b) rest
  -- The product has the length of `q` plus that of `b`, less one, as the division expects.
  let a := a.take (q.length + b.length - 1)
  match dividePolynomialcoeff (toFr a) (toFr b) with
  | .ok out => ensure (lead != 0 && ofFr out == q) s!"the quotient is {ofFr out}"
  | .error _ => lead === 0
  ensure (dividePolynomialcoeff (toFr a) #[]).toOption.isNone "an empty divisor is accepted"
  -- A dividend shorter than the divisor has the empty quotient.
  (dividePolynomialcoeff (toFr (b.take (b.length - 1))) (toFr b)).toOption.map ofFr ===
    (if lead != 0 || b.length == 1 then some [] else some [])

/-- Distinct points, small or anywhere. -/
def genPoints (range : Range Nat) : Gen (List Nat) :=
  List.eraseDups <$> Gen.list range (Gen.frequency [(1, Gen.nat (.linear 0 20)), (2, genCoeff)])

/-- The interpolation through distinct points takes each value at its point.

The vanishing polynomial is monic and zero at each point. -/
def interpolation : Property IO := pureIO do
  let xs ← forAll (genPoints (.linear 0 10))
  let ys ← forAll (Gen.list (.singleton xs.length) genCoeff)
  match interpolatePolynomialcoeff (toFr xs) (toFr ys) with
  | .ok poly =>
    let p := ofFr poly
    xs.map (horner p) === ys
    ensure (p.length ≤ max 1 xs.length) "the interpolation has too high a degree"
  | .error _ => failWith "the interpolation failed"
  ensure (interpolatePolynomialcoeff (toFr xs) (toFr (0 :: ys))).toOption.isNone
    "points and values of two lengths are accepted"
  match vanishingPolynomialcoeff (toFr xs) with
  | .ok poly =>
    let p := ofFr poly
    p.length === xs.length + 1
    p.getLast? === some 1
    xs.map (horner p) === xs.map fun _ => 0
  | .error _ => failWith "the vanishing polynomial failed"

/-- The reversal of the low `bits` bits of a number, by its digits. -/
def reverseModel (n bits : Nat) : Nat :=
  (List.range bits).foldl (fun acc i => 2 * acc + n / 2 ^ i % 2) 0

/-- The bit reversal, its permutation and the roots of unity are those of the specification. -/
def domains : Property IO := pureIO do
  let bits ← forAll (Gen.nat (.constant 0 13))
  let n ← forAll (Gen.nat (.constant 0 (2 ^ bits - 1)))
  BitReversal.reverseBits n (2 ^ bits) === reverseModel n bits
  let small := min bits 8
  let seq := Array.range (2 ^ small)
  (BitReversal.bitReversalPermutation seq).toList ===
    (List.range (2 ^ small)).map (reverseModel · small)
  let order ← forAll (Gen.element [1, 2, 64, 128, 4096, 8192])
  let i ← forAll (Gen.nat (.constant 0 (order - 1)))
  let roots := computeRootsOfUnity order
  roots.size === order
  roots[i]!.val === modPow r 7 ((r - 1) / order * i)
  (rootsOfUnityBrp order)[i]!.val === modPow r 7 ((r - 1) / order * reverseModel i order.log2)
  -- A coset of a cell is a block of 64 points of the bit-reversed domain of 8192.
  let cell ← forAll (Gen.frequency [(4, Gen.nat (.constant 0 127)),
      (1, Gen.element [128, 129, 8192])])
  match cosetForCell cell with
  | .ok coset =>
    ensure (cell < 128) "a cell index of 128 or more has a coset"
    ofFr coset === (List.range 64).map fun j =>
      modPow r 7 ((r - 1) / 8192 * reverseModel (64 * cell + j) 13)
  | .error _ => ensure (cell ≥ 128) "a cell has no coset"

/-- The FFT is the sum it stands for, and the inverse FFT undoes it. -/
def fft : Property IO := pureIO do
  let k ← forAll (Gen.nat (.constant 0 5))
  let n := 2 ^ k
  let vals ← forAll (Gen.list (.singleton n) genCoeff)
  let roots := computeRootsOfUnity n
  let out := fftField (toFr vals) roots
  let w := modPow r 7 ((r - 1) / n)
  ofFr out === (List.range n).map fun i =>
    (vals.zipIdx.foldl (fun acc (v, j) => (acc + v * modPow r w (i * j)) % r) 0)
  ofFr (fftField out roots (inv := true)) === vals

/-- A polynomial in evaluation form has, at any point, the value of its coefficient form.

At a point of the domain the value is the entry there. -/
def evaluationForm : Property IO := pureIO do
  let p ← forAll (genPoly (.linear 0 6))
  let z ← forAll (Gen.frequency [
    (2, (fun j => modPow r 7 ((r - 1) / 4096 * j)) <$> Gen.nat (.constant 0 4095)),
    (1, (fun j => modPow r 7 ((r - 1) / 8192 * j)) <$> Gen.nat (.constant 0 8191)),
    (3, genCoeff)])
  let short ← forAll (Gen.frequency [(8, pure 4096), (1, Gen.element [0, 4095, 4097])])
  let domain := rootsOfUnityBrp 4096
  let values := (domain.map fun d => Fr.ofNat (horner p d.val)).extract 0 short
  let values := values ++ Array.replicate (short - values.size) Fr.zero
  match evaluatePolynomialInEvaluationForm values (Fr.ofNat z) with
  | .ok y =>
    short === 4096
    y.val === horner p z
  | .error _ => ensure (short != 4096) "a polynomial of 4096 values is refused"
  -- The coefficient form of the values is the polynomial.
  if short == 4096 then
    ensure (samePoly (ofFr
        (polynomialEvalToCoeff values)) p) "the inverse FFT gives another polynomial"

/-- The polynomial of a cell takes the cell's values on its coset. -/
def cosets : Property IO := pureIO do
  let cell ← forAll (Gen.nat (.constant 0 127))
  let evals ← forAll (Gen.list (.singleton 64) genCoeff)
  let short ← forAll (Gen.frequency [(8, pure 64), (1, pure 63), (1, pure 65)])
  let .ok coset := cosetForCell cell | failWith "no coset"
  match interpolateCosetEvals coset[0]! ((toFr evals).extract 0 short ++
      Array.replicate (short - 64) Fr.zero) with
  | .ok poly =>
    short === 64
    coset.toList.map (fun x => horner (ofFr poly) x.val) === evals
  | .error _ => ensure (short != 64) "a cell of 64 values is refused"

/-- Packed indices are 8 big-endian bytes each, and a ragged buffer is refused. -/
def indices : Property IO := pureIO do
  let values ← forAll (Gen.list (.linear 0 6) (genNatBits 64))
  let extra ← forAll (Gen.nat (.constant 0 9))
  let bytes := values.foldl (fun acc v => acc ++ beBytes 8 v) ByteArray.empty ++
    ⟨Array.replicate extra 0⟩
  match unpackIndicesBE bytes with
  | .ok out =>
    ensure (extra % 8 == 0) "a ragged buffer is accepted"
    out.toList === values ++ List.replicate (extra / 8) 0
  | .error _ => ensure (extra % 8 != 0) "a whole buffer is refused"

end CurvesProperty.KzgPoly

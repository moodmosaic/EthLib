import Property.Kernels.Common
import EthLib.Cryptography.Bls
import EthLib.Cryptography.AltBn128

/-!
# Extension fields and the value of a pairing

`Fp2`, `Fp6` and `Fp12` of BLS12-381, and `Fp2` and `Fp12` of alt_bn128, against py_ecc.

An element of `Fp12` crosses to the reference as its twelve coefficients of `1, w, ..., w^11`.

For BLS12-381 the tower of EthLib has `i^2 = -1`, `v^3 = 1 + i` and `w^2 = v`.

So `w^6 = 1 + i`, which is the `w` of py_ecc, where `w^12 = 2 w^6 - 2`.

The value of the BLS12-381 pairing is compared here, coefficient by coefficient.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace KernelsProperty.Tower

/-- The modulus of the base field of BLS12-381. -/
abbrev p : Nat := Bls.Fp.modulus

/-- The coefficients of `1, w, ..., w^11` of an element of the tower.

Let `a_k = x_k + y_k i` be the coefficient of `w^k` for `k < 6`, and recall `i = w^6 - 1`.

The term `a_k w^k` is then `(x_k - y_k) w^k + y_k w^(k + 6)`. -/
def coeffs (a : Bls.Fp12) : List Nat :=
  let terms : List Bls.Fp2 := [a.c0.c0, a.c1.c0, a.c0.c1, a.c1.c1, a.c0.c2, a.c1.c2]
  terms.map (fun k => (k.c0.val + p - k.c1.val) % p) ++ terms.map (·.c1.val)

/-- The element of the tower with these twelve coefficients. -/
def ofCoeffs (c : List Nat) : Bls.Fp12 :=
  let term (k : Nat) : Bls.Fp2 := ⟨Bls.Fp.ofNat (c[k]! + c[k + 6]!), Bls.Fp.ofNat c[k + 6]!⟩
  ⟨⟨term 0, term 2, term 4⟩, ⟨term 1, term 3, term 5⟩⟩

/-- Twelve coefficients as one word of a command. -/
def word (c : List Nat) : String := ",".intercalate (c.map toString)

/-- The coefficients of an answer. -/
def unword (answer : String) : TestT IO (List Nat) :=
  match (answer.splitOn ",").mapM String.toNat? with
  | some xs => if xs.length = 12 then pure xs else failWith s!"the oracle answered: {answer}"
  | none => failWith s!"the oracle answered: {answer.take 200}"

/-- A coefficient below a modulus: `0`, `1`, `m - 1`, near them, or any. -/
def genCoeff (m : Nat) : Gen Nat :=
  Gen.frequency [(2, pure 0), (1, pure 1), (1, pure (m - 1)), (1, genAround 0 m),
    (5, Gen.nat (.constant 0 (m - 1)))]

/-- An element of `Fp12` as coefficients: dense, or with only the terms of a subfield or a line.

A sparse element is the common case in a Miller loop, and the easy one to get wrong. -/
def genElement (m : Nat) : Gen (List Nat) :=
  let masked (keep : List Nat) : Gen (List Nat) :=
    (fun c => c.zipIdx.map fun (x, i) => if keep.contains i then x else 0) <$>
      Gen.list (.singleton 12) (Gen.nat (.constant 0 (m - 1)))
  Gen.frequency [
    (5, Gen.list (.singleton 12) (genCoeff m)), (1, pure (List.replicate 12 0)),
    (1, masked [0]), (1, masked [0, 6]), (1, masked [0, 2, 4, 6, 8, 10]),
    (1, masked [0, 2, 3, 6, 8, 9]), (1, masked [1, 7]), (1, masked [11])]

/-- The field operations of `Fp12` of BLS12-381 are those of py_ecc. -/
def blsFp12 (oracle : Oracle) : Property IO := propertyM do
  let (a, b) ← forAll (Gen.zip (genElement p) (genElement p))
  pure do
    let x := ofCoeffs a
    let y := ofCoeffs b
    let ask (op : String) (rest : List String) : TestT IO (List Nat) := do
      unword (← oracle.ask (["f12", "bls", op, word a] ++ rest))
    classify "a is zero" (a.all (· == 0))
    classify "a lies in Fp6" ([1, 3, 5, 7, 9, 11].all fun i => a[i]! == 0)
    coeffs x === a
    coeffs (x * y) === (← ask "mul" [word b])
    coeffs (x * x) === (← ask "mul" [word a])
    coeffs x.square === (← ask "mul" [word a])
    coeffs (x + y) === (a.zip b).map fun (s, t) => (s + t) % p
    coeffs (x - y) === (a.zip b).map fun (s, t) => (s + p - t) % p
    coeffs (-x) === a.map fun s => (p - s) % p
    coeffs x.inverse === (← ask "inv" [])
    coeffs x.frobenius === (← ask "frob" ["1"])
    coeffs x.frobenius.frobenius === (← ask "frob" ["2"])
    coeffs x.conjugate === (← ask "frob" ["6"])
    (x.isOne) === (a == 1 :: List.replicate 11 0)

/-- `Fp2` and `Fp6` of BLS12-381, each as the subfield of `Fp12` that py_ecc computes in. -/
def blsSubfields (oracle : Oracle) : Property IO := propertyM do
  let parts ← forAll (Gen.frequency [
    (1, pure (List.replicate 12 0)), (8, Gen.list (.singleton 12) (genCoeff p))])
  let e ← forAll (Gen.frequency [(1, Gen.nat (.linear 0 5)), (1, genNatBits 64)])
  pure do
    let fp (i : Nat) : Bls.Fp := Bls.Fp.ofNat parts[i]!
    let a2 : Bls.Fp2 := ⟨fp 0, fp 1⟩
    let b2 : Bls.Fp2 := ⟨fp 2, fp 3⟩
    let a6 : Bls.Fp6 := ⟨⟨fp 0, fp 1⟩, ⟨fp 2, fp 3⟩, ⟨fp 4, fp 5⟩⟩
    let b6 : Bls.Fp6 := ⟨⟨fp 6, fp 7⟩, ⟨fp 8, fp 9⟩, ⟨fp 10, fp 11⟩⟩
    let up2 (x : Bls.Fp2) : Bls.Fp12 := ⟨⟨x, Bls.Fp2.zero, Bls.Fp2.zero⟩, Bls.Fp6.zero⟩
    let up6 (x : Bls.Fp6) : Bls.Fp12 := ⟨x, Bls.Fp6.zero⟩
    let ask (op : String) (x : Bls.Fp12) (rest : List String) : TestT IO (List Nat) := do
      unword (← oracle.ask (["f12", "bls", op, word (coeffs x)] ++ rest))
    classify "the Fp2 element is zero" a2.isZero
    classify "the Fp6 element is zero" a6.isZero
    -- `Fp2`.
    coeffs (up2 (a2 * b2)) === (← ask "mul" (up2 a2) [word (coeffs (up2 b2))])
    coeffs (up2 a2.inverse) === (← ask "inv" (up2 a2) [])
    coeffs (up2 a2.conjugate) === (← ask "frob" (up2 a2) ["1"])
    coeffs (up2 (a2.powNat e)) === (← ask "pow" (up2 a2) [toString e])
    coeffs (up2 a2.mulByOnePlusI) ===
      (← ask "mul" (up2 a2) [word (coeffs (up2 ⟨Bls.Fp.one, Bls.Fp.one⟩))])
    -- `Fp6`.
    coeffs (up6 (a6 * b6)) === (← ask "mul" (up6 a6) [word (coeffs (up6 b6))])
    coeffs (up6 a6.inverse) === (← ask "inv" (up6 a6) [])
    coeffs (up6 a6.mulByV) === (← ask "mul" (up6 a6) [word (coeffs (up6 Bls.Fp6.v))])
    -- The constant of the Frobenius map is `(1 + i)^((p - 1) / 6)`.
    coeffs (up2 (Bls.Fp12.frobeniusCoeff (F := Bls.Fp))) ===
      (← ask "pow" (up2 ⟨Bls.Fp.one, Bls.Fp.one⟩) [toString ((p - 1) / 6)])

/-- The final exponentiation and the cyclotomic formulas of BLS12-381.

The final exponentiation is the power by `(p^12 - 1) / r` on any element.

The cyclotomic square and power are the square and the power on the cyclotomic subgroup. -/
def blsFinal (oracle : Oracle) : Property IO := propertyM do
  let a ← forAll (genElement p)
  let e ← forAll (Gen.frequency [(1, Gen.nat (.linear 0 5)), (1, pure Bls.blsX),
    (1, pure ((Bls.blsX + 1) / 3)), (2, genNatBits 64)])
  pure do
    let x := ofCoeffs a
    classify "the element is zero" (a.all (· == 0))
    let ask (op : String) (c : List Nat) (rest : List String) : TestT IO (List Nat) := do
      unword (← oracle.ask (["f12", "bls", op, word c] ++ rest))
    if a.all (· == 0) then
      -- The text says the cyclotomic formula maps zero to zero.
      coeffs x.cyclotomicSquare === a
    else
      coeffs (Bls.finalExponentiation x) === (← ask "final" a [])
      -- The easy part lands in the cyclotomic subgroup.
      let t := x.conjugate * x.inverse
      let m := t.frobenius.frobenius * t
      let c := coeffs m
      c === (← ask "easy" a [])
      coeffs m.cyclotomicSquare === (← ask "mul" c [word c])
      coeffs (m.cyclotomicPow e) === (← ask "pow" c [toString e])

/-- A scalar for a point of prime order `r`: small, near `r`, or any. -/
def genScalar (r : Nat) : Gen Nat :=
  Gen.frequency [(2, Gen.nat (.linear 1 8)), (1, (r - ·) <$> Gen.nat (.linear 1 8)),
    (3, Gen.nat (.constant 1 (r - 1)))]

/-- A point of `G1` and a point of `G2` in the words of a command. -/
def pointWords (P : Bls.G1) (Q : Bls.G2) : List String :=
  let (x, y) := P.toAffine
  let (qx, qy) := Q.toAffine
  [s!"{x.val},{y.val}", s!"{qx.c0.val},{qx.c1.val},{qy.c0.val},{qy.c1.val}"]

/-- The value of the BLS12-381 pairing is the inverse of py_ecc's, coefficient by coefficient.

EthLib conjugates the Miller value because the parameter `x` is negative, as its text says.

py_ecc does not, so the two values are inverse to each other, and a conjugate is an inverse here.

The value is also bilinear: the pairing of `a G1` and `b G2` is that of the generators to `a b`. -/
def blsPairing (oracle : Oracle) : Property IO := propertyM do
  let (a, b) ← forAll (Gen.zip (genScalar Bls.Fr.modulus) (genScalar Bls.Fr.modulus))
  pure do
    let P : Bls.G1 := Bls.G1.generator.mulNat a
    let Q : Bls.G2 := Bls.G2.generator.mulNat b
    let value := Bls.pairing P Q
    let theirs ← unword (← oracle.ask (["blspair"] ++ pointWords P Q))
    coeffs value.conjugate === theirs
    coeffs value.inverse === theirs
    let base := Bls.pairing (Bls.G1.generator : Bls.G1) (Bls.G2.generator : Bls.G2)
    coeffs (base.cyclotomicPow (a * b % Bls.Fr.modulus)) === coeffs value
    -- A point at infinity gives one.
    coeffs (Bls.pairing (Bls.G1.zero : Bls.G1) Q) === 1 :: List.replicate 11 0
    coeffs (Bls.pairing P (Bls.G2.zero : Bls.G2)) === 1 :: List.replicate 11 0

/-- The Miller loop of any parameter `s`, not only of the `|x|` of BLS12-381.

After the final exponentiation it is the Miller function `f_{s,Q}(P)` of py_ecc's affine lines.

The lines of EthLib differ from those by factors that the final exponentiation sends to one. -/
def blsMiller (oracle : Oracle) : Property IO := propertyM do
  let s ← forAll (Gen.frequency [(3, Gen.nat (.linear 1 40)), (1, pure Bls.blsX),
    (1, (2 ^ ·) <$> Gen.nat (.constant 0 63)), (1, (2 ^ · - 1) <$> Gen.nat (.constant 1 64)),
    (2, genNatBits 64)])
  let (a, b) ← forAll (Gen.zip (genScalar Bls.Fr.modulus) (genScalar Bls.Fr.modulus))
  pure do
    if s == 0 then pure () else
    let P : Bls.G1 := Bls.G1.generator.mulNat a
    let Q : Bls.G2 := Bls.G2.generator.mulNat b
    classify "s is the parameter of the curve" (s == Bls.blsX)
    classify "s is a power of two" (s &&& (s - 1) == 0)
    classify "every bit of s is set" (s &&& (s + 1) == 0)
    let value := Bls.finalExponentiation (Bls.millerLoop s Q.toAffine P.toAffine)
    coeffs value === (← unword (← oracle.ask (["blsmiller", toString s] ++ pointWords P Q)))

/-- The modulus of the base field of alt_bn128. -/
abbrev q : Nat := AltBn128.Fp.modulus

/-- An element of `Fp12` of alt_bn128 from its coefficients. -/
def bnOf (c : List Nat) : AltBn128.Fp12 := Vector.ofFn fun k => Fin.ofNat q c[k.val]!

/-- The coefficients of an element of `Fp12` of alt_bn128. -/
def bnCoeffs (a : AltBn128.Fp12) : List Nat := a.toList.map (·.val)

/-- The field operations of `Fp12` and of `Fp2` of alt_bn128 are those of py_ecc. -/
def bnFp12 (oracle : Oracle) : Property IO := propertyM do
  let (a, b) ← forAll (Gen.zip (genElement q) (genElement q))
  let e ← forAll (Gen.frequency [(1, Gen.nat (.linear 0 5)), (2, genNatBits 64)])
  let n ← forAll (Gen.nat (.constant 0 12))
  let c ← forAll (genCoeff q)
  pure do
    let x := bnOf a
    let y := bnOf b
    let ask (op : String) (c : List Nat) (rest : List String) : TestT IO (List Nat) := do
      unword (← oracle.ask (["f12", "bn", op, word c] ++ rest))
    classify "a is zero" (a.all (· == 0))
    bnCoeffs (x * y) === (← ask "mul" a [word b])
    bnCoeffs (x + y) === (a.zip b).map fun (s, t) => (s + t) % q
    bnCoeffs (x - y) === (a.zip b).map fun (s, t) => (s + q - t) % q
    bnCoeffs x.inverse === (← ask "inv" a [])
    bnCoeffs x.frobenius === (← ask "frob" a ["1"])
    bnCoeffs (AltBn128.Fp12.frobeniusPow n x) === (← ask "frob" a [toString n])
    bnCoeffs (AltBn128.Fp12.powBits 64 x e) === (← ask "pow" a [toString e])
    bnCoeffs (AltBn128.Fp12.scale (Fin.ofNat q c) x) === a.map fun s => c * s % q
    -- `Fp2`, as the subfield with `i = w^6 - 9`.
    let a2 : AltBn128.Fp2 := ⟨Fin.ofNat q a[0]!, Fin.ofNat q a[1]!⟩
    let b2 : AltBn128.Fp2 := ⟨Fin.ofNat q b[0]!, Fin.ofNat q b[1]!⟩
    let up (z : AltBn128.Fp2) : List Nat := bnCoeffs (AltBn128.Fp12.ofFp2 z)
    up a2 === (List.range 12).map fun k =>
      if k == 0 then (a[0]! + 9 * q - 9 * a[1]!) % q else if k == 6 then a[1]! else 0
    up (a2 * b2) === (← ask "mul" (up a2) [word (up b2)])
    up a2.inv === (← ask "inv" (up a2) [])
    up a2.conj === (← ask "frob" (up a2) ["1"])
    up (AltBn128.Fp2.powBits 64 a2 e) === (← ask "pow" (up a2) [toString e])

/-- The constants of the curves are those of py_ecc and of OpenSSL. -/
def curveConstants (oracle : Oracle) : Property IO := propertyM do
  pure do
    let bls := numbers (← oracle.ask ["curve", "bls"])
    let g1 : Bls.G1 := Bls.G1.generator
    let g2 : Bls.G2 := Bls.G2.generator
    let b2 : Bls.Fp2 := Bls.G2.bTwist
    [Bls.Fp.modulus, Bls.Fr.modulus, g1.x.val, g1.y.val, g2.x.c0.val, g2.x.c1.val, g2.y.c0.val,
      g2.y.c1.val, 4, b2.c0.val, b2.c1.val] === bls
    ensure (g1.z.val == 1 && g2.z.c0.val == 1 && g2.z.c1.val == 0) "a generator is not affine"
    let bn := numbers (← oracle.ask ["curve", "bn"])
    let (hx, hy) : AltBn128.Fp2 × AltBn128.Fp2 := match AltBn128.Point2.generator with
      | .affine x y => (x, y)
      | .infinity => (⟨0, 0⟩, ⟨0, 0⟩)
    let (gx, gy) : Nat × Nat := match AltBn128.Point.generator with
      | .affine x y => (x.val, y.val)
      | .infinity => (0, 0)
    [AltBn128.Fp.modulus, AltBn128.Fr.modulus, gx, gy, hx.c0.val, hx.c1.val, hy.c0.val,
      hy.c1.val, AltBn128.b.val, AltBn128.b2.c0.val, AltBn128.b2.c1.val,
      AltBn128.ATE_LOOP_COUNT, AltBn128.LOG_ATE_LOOP_COUNT] === bn
    -- The loop count is `6 u + 2`, and the final exponent is `(p^12 - 1) / r`.
    AltBn128.ATE_LOOP_COUNT === 6 * AltBn128.BN_U + 2
    AltBn128.FINAL_EXPONENT === (q ^ 12 - 1) / AltBn128.Fr.modulus
    Bls.finalExpExponent === (p ^ 12 - 1) / Bls.Fr.modulus
    -- The moduli of both curves are the polynomials of their families at the parameter.
    let u := AltBn128.BN_U
    q === 36 * u ^ 4 + 36 * u ^ 3 + 24 * u ^ 2 + 6 * u + 1
    AltBn128.Fr.modulus === 36 * u ^ 4 + 36 * u ^ 3 + 18 * u ^ 2 + 6 * u + 1
    let x := Bls.blsX
    Bls.Fr.modulus === x ^ 4 - x ^ 2 + 1
    p === (x + 1) ^ 2 * (x ^ 4 - x ^ 2 + 1) / 3 - x
    Bls.MapToCurve.H_EFF_G1 === x + 1

end KernelsProperty.Tower

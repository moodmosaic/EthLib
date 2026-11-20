import Property.Kernels.Common
import EthLib.Cryptography.Montgomery.Fin
import EthLib.Cryptography.Secp256k1.Field
import EthLib.Cryptography.Secp256r1.Curve
import EthLib.Cryptography.AltBn128.Curve
import EthLib.Cryptography.Bls.Fp
import EthLib.Cryptography.Bls.Fr

/-!
# Montgomery arithmetic at every modulus

`Cryptography/Montgomery.lean` is written once for every odd modulus below `2 ^ (32 n)`.

EthLib uses it at three moduli: the field of secp256k1, and `Fr` and `Fp` of BLS12-381.

Here the modulus is generated: any odd number of eight or of twelve limbs.

The answer is arithmetic on `Nat`.
-/

open Hedgehog Support EthLib EthLib.Cryptography
open EthLib.Cryptography.Montgomery (Words Limbs Modulus)

namespace KernelsProperty.Mont

/-- `-p⁻¹ mod 2 ^ 32` for an odd `p`, by Newton's iteration, which doubles the bits each step. -/
def negInv32 (p : Nat) : Nat :=
  let inverse := (List.range 5).foldl
    (fun x _ => x * (2 ^ 32 + 2 - p * x % 2 ^ 32) % 2 ^ 32) 1
  (2 ^ 32 - inverse) % 2 ^ 32

/-- The Montgomery constants of an odd `p` below `2 ^ (32 n)`, computed on `Nat`.

Each proof of the structure is a check at run time, so a wrong constant gives nothing. -/
@[nospecialize, noinline]
def mkModulus (n : Nat) [Words n] [Limbs n] (p : Nat) : Option (Modulus n) :=
  let pLimbs : Limbs.T n := Limbs.ofNat p
  let pinv := UInt64.ofNat (negInv32 p)
  let r1 : Limbs.T n := Limbs.ofNat (2 ^ (32 * n) % p)
  let r2 : Limbs.T n := Limbs.ofNat (2 ^ (32 * n) * 2 ^ (32 * n) % p)
  let pm2 : Limbs.T n := Limbs.ofNat (p - 2)
  if h1 : Limbs.val pLimbs = p then
    if h2 : (p * pinv.toNat + 1) % 2 ^ 32 = 0 then
      if h3 : Limbs.val r1 = 2 ^ (32 * n) % p then
        if h4 : Limbs.val r2 = 2 ^ (32 * n) * 2 ^ (32 * n) % p then
          if h5 : Limbs.val pm2 = p - 2 then
            some { p, pLimbs, pinv, r1, r2, pm2, pLimbs_spec := h1, pinv_spec := h2,
                   r1_spec := h3, r2_spec := h4, pm2_spec := h5 }
          else none
        else none
      else none
    else none
  else none

/-- The moduli of the curves of Ethereum that fit eight limbs. -/
def named8 : List Nat :=
  [Secp256k1.Fp.modulus, Secp256k1.Fn.modulus, Secp256r1.Fp.modulus, Secp256r1.Fn.modulus,
    AltBn128.Fp.modulus, AltBn128.Fr.modulus, Bls.Fr.modulus, 2 ^ 255 - 19, 2 ^ 256 - 189]

/-- Moduli of twelve limbs: `Fp` of BLS12-381, the field and the order of P-384, and others. -/
def named12 : List Nat :=
  [Bls.Fp.modulus, 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1,
    2 ^ 384 - 0x389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d,
    2 ^ 384 - 317, 2 ^ 383 - 187, 2 ^ 383 + 1]

/-- An odd modulus below `R = 2 ^ (32 n)`.

It is a named one, one just below `R`, one on either side of `R / 2`, a tiny one, or any. -/
def genModulus (n : Nat) (named : List Nat) : Gen Nat :=
  let R := 2 ^ (32 * n)
  let odd (x : Nat) := if x % R % 2 = 0 then x % R + 1 else x % R
  -- A distance from an edge that keeps the modulus on its side of `R / 2`, also for one limb.
  let near := Gen.nat (.exponential 0 (min (2 ^ 40) (R / 4 - 1)))
  Gen.frequency [
    (4, Gen.element named),
    (2, (fun d => R - 1 - 2 * d) <$> near),
    (2, (fun d => R / 2 + 1 + 2 * d) <$> near),
    (2, (fun d => R / 2 - 1 - 2 * d) <$> near),
    (2, (fun k => 2 * k + 1) <$> Gen.nat (.exponential 0 (R / 2 - 1))),
    (2, odd <$> genLimbs n),
    (1, (fun k => 2 * k + 1) <$> Gen.nat (.linear 0 50)),
    (3, (fun k => 2 * k + 1) <$> Gen.nat (.constant 0 (R / 2 - 1)))]

/-- The model: the modulus and the integer below it that the accumulator stands for. -/
structure Field where
  p : Nat
  acc : Nat
  deriving Repr

/-- What the accumulator can be asked. -/
inductive Op where
  | mul (x : Nat)
  | sqr
  | add (x : Nat)
  | sub (x : Nat)
  | subFrom (x : Nat)
  | neg
  | inv
  | pow (e : Nat)
  | powLimbs (e : Nat)
  /-- Out of Montgomery form and in again. -/
  | trip
  /-- To bytes, and read back behind `before` other bytes. -/
  | bytes (before : Nat)
  /-- To `Fin p` and back. -/
  | fin
  deriving Repr, BEq

/-- The Montgomery form of an integer: `x R mod p`. -/
def form (n p x : Nat) : Nat := x % p * (2 ^ (32 * n) % p) % p

/-- The integer whose Montgomery form is `f mod p`. -/
def ofForm (n p f : Nat) : Nat := f % p * modInv p (2 ^ (32 * n) % p) % p

/-- What the rows of the CIOS product do on two forms.

The first answer is whether the state after the last row is `p` or more.

The final subtraction then fires.

The second is whether the state after some row is `R` or more, so that a word lies above it. -/
def ciosBranches (n p a b : Nat) : Bool × Bool :=
  let R := 2 ^ (32 * n)
  let (t, above) := (List.range n).foldl (fun (t, above) i =>
    let s := t + a * (b / 2 ^ (32 * i) % 2 ^ 32)
    let m := s % 2 ^ 32 * negInv32 p % 2 ^ 32
    let t := (s + m * p) / 2 ^ 32
    (t, above || t ≥ R)) (0, false)
  (t ≥ p, above)

/-- A form `b` for which the product with the form `a` ends at `p` or more, if one is found.

The rows add `m p` with `m = a b (-p⁻¹) mod R`, and end at `(a b + m p) / R`.

That is `p` or more exactly when `m ≥ R - a b / p`, so `m` is aimed just below `R`.

With `a = 2^k a'`, `m` is a multiple of `2^k`, and `b` is solved from `m = R - 2^k (1 + d)`.

Each candidate is checked on the rows themselves, so a miss costs only a draw. -/
def firingForm (n p a start : Nat) : Option Nat :=
  if a == 0 then none else
  let R := 2 ^ (32 * n)
  let k := (List.range (32 * n)).find? (fun i => a / 2 ^ i % 2 == 1) |>.getD 0
  let R' := R / 2 ^ k
  let negInv := (R' - modInv R' (p % R')) % R'
  let unit := modInv R' (a / 2 ^ k * negInv % R')
  (List.range 96).findSome? fun i =>
    let d := start + i
    let b := (R' + R' - 1 - d % R') % R' * unit % R'
    if b < p && (ciosBranches n p a b).1 then some b else none

/-- An operand: by its integer, or by its Montgomery form, which is what the limbs hold.

Some forms are chosen against the form of the accumulator, so that a sum lands on `p` or `R`. -/
def genOperand (n : Nat) (s : Field) : Gen Nat :=
  let R := 2 ^ (32 * n)
  let mine := form n s.p s.acc
  Gen.frequency [
    (2, genAround 0 R), (2, genAround s.p R), (1, pure s.acc),
    (3, ofForm n s.p <$> genLimbs n),
    (2, (fun d => ofForm n s.p (s.p - 1 - d % s.p)) <$> Gen.nat (.exponential 0 (s.p - 1))),
    -- The two forms sum to `p - 1`, `p` or `p + 1`: the reduction of a sum is at its edge.
    (2, (fun d => ofForm n s.p (2 * s.p + d - 1 - mine)) <$> Gen.nat (.constant 0 2)),
    -- The two forms are equal or one apart: the borrow of a difference is at its edge.
    (2, (fun d => ofForm n s.p (mine + s.p + d - 1)) <$> Gen.nat (.constant 0 2)),
    (3, Gen.nat (.constant 0 (R - 1)))]

/-- The accumulator against arithmetic on `Nat` mod `p`. -/
def model (n : Nat) (genP : Gen Nat) : Model Field Op where
  initState := do
    let p ← genP
    let acc ← genNear p (32 * n)
    pure ⟨p, acc % p⟩
  transitions s :=
    let operand := genOperand n s
    -- An operand whose product with the accumulator makes the final subtraction fire.
    let firing := (fun (d, other) =>
      match firingForm n s.p (form n s.p s.acc) d with
      | some b => ofForm n s.p b
      | none => other) <$> Gen.zip (Gen.nat (.constant 0 200)) operand
    Gen.frequency [
      (3, Op.mul <$> operand), (3, Op.mul <$> firing), (2, pure .sqr),
      (4, Op.add <$> operand), (4, Op.sub <$> operand),
      (2, Op.subFrom <$> operand), (1, pure .neg), (1, pure .inv),
      (1, Op.pow <$> Gen.frequency [(1, Gen.nat (.linear 0 5)), (1, genNear s.p (32 * n))]),
      (1, Op.powLimbs <$> Gen.frequency [(1, Gen.nat (.linear 0 5)), (2, genLimbs n),
        (1, genNear s.p (32 * n))]),
      (1, pure .trip), (1, Op.bytes <$> Gen.nat (.linear 0 5)), (1, pure .fin)]
  apply s
    | .mul x => { s with acc := s.acc * x % s.p }
    | .sqr => { s with acc := s.acc * s.acc % s.p }
    | .add x => { s with acc := (s.acc + x) % s.p }
    | .sub x => { s with acc := (s.acc + s.p - x % s.p) % s.p }
    | .subFrom x => { s with acc := (x % s.p + s.p - s.acc) % s.p }
    | .neg => { s with acc := (s.p - s.acc) % s.p }
    | .inv => { s with acc := modPow s.p s.acc (s.p - 2) }
    | .pow e => { s with acc := modPow s.p s.acc e }
    | .powLimbs e => { s with acc := modPow s.p s.acc (e % 2 ^ (32 * n)) }
    | .trip | .bytes _ | .fin => s

/-- The system: a modulus and an element in its Montgomery form. -/
structure Sut (n : Nat) [Words n] [Limbs n] where
  M : Modulus n
  x : Montgomery M

/-- The accumulator in Montgomery limbs, at the modulus that `pick` gives for the model's `p`. -/
@[nospecialize, noinline]
def machine (n : Nat) [Words n] [Limbs n] (genP : Gen Nat) (pick : Nat → Option (Modulus n)) :
    StateMachine Field Op (Sut n) IO where
  toModel := model n genP
  initSut s :=
    match pick s.p with
    | some M => pure ⟨M, Montgomery.ofNat s.acc⟩
    | none => throw (IO.userError s!"no Montgomery constants for {s.p}")
  applySut sut before _ t := do
    let ⟨M, x⟩ := sut
    let p := before.p
    let R := 2 ^ (32 * n)
    let mine := form n p before.acc
    classify "2 p > R" (2 * p > R)
    classify "p is prime" (probablyPrime p)
    let next : Montgomery M ← match t with
      | .mul y => do
        let (fired, above) := ciosBranches n p mine (form n p y)
        classify "mul: the final subtraction fired" fired
        classify "mul: the final subtraction did not fire" (!fired)
        classify "mul: a row left a word above the limbs" above
        pure (x * Montgomery.ofNat y)
      | .sqr => do
        let (fired, above) := ciosBranches n p mine mine
        classify "sqr: the final subtraction fired" fired
        classify "sqr: a row left a word above the limbs" above
        (Montgomery.pow x 2).toNat === (x * x).toNat
        pure (x * x)
      | .add y => do
        let sum := mine + form n p y
        classify "add: the sum of the forms is p or more" (sum ≥ p)
        classify "add: the sum of the forms is exactly p" (sum == p)
        classify "add: the sum of the forms is below p" (sum < p)
        classify "add: the sum of the forms is R or more" (sum ≥ R)
        pure (x + Montgomery.ofNat y)
      | .sub y => do
        classify "sub: the difference of the forms borrows" (mine < form n p y)
        classify "sub: the forms are equal" (mine == form n p y)
        pure (x - Montgomery.ofNat y)
      | .subFrom y => do
        classify "sub: the difference of the forms borrows" (form n p y < mine)
        pure (Montgomery.ofNat y - x)
      | .neg => do
        classify "neg: of zero" (before.acc == 0)
        pure (-x)
      | .inv => do
        classify "inv: of zero" (before.acc == 0)
        classify "inv: of an element with no inverse" (Nat.gcd before.acc p != 1)
        let y := Montgomery.inv x
        if probablyPrime p && before.acc != 0 then (x * y).toNat === 1 % p
        pure y
      | .pow e => pure (Montgomery.pow x e)
      | .powLimbs e => pure (Montgomery.powLimbs x (Limbs.ofNat e))
      | .trip => pure (Montgomery.ofNat x.toNat)
      | .bytes k => do
        let bytes := ByteArray.mk (Array.replicate k 0xff) ++ Montgomery.toBytesBE x
        beNat (Montgomery.toBytesBE x) === before.acc
        match Montgomery.ofBytesBE (M := M) bytes k with
        | some y => pure y
        | none => failWith "the bytes of an element do not read back"
      | .fin => pure (Montgomery.ofFin (Montgomery.toFin x))
    pure ⟨M, next⟩
  invariants sut s := do
    sut.x.toNat === s.acc
    -- The limbs hold the one form below `p`.
    Limbs.val sut.x.limbs === form n s.p s.acc
    ensure ((sut.x == Montgomery.ofNat s.acc)) "the form is not the form of the integer"

/-- Minimum shares of the rare branches of a machine, for runs of 500 sequences or more.

A word above the limbs needs `2 p > R`, so only a wide modulus is asked for it. -/
def covered (cases : Nat) (wide : Bool) (p : Property IO) : Property IO :=
  withMinimums cases ([
    (15, "mul: the final subtraction fired"), (20, "mul: the final subtraction did not fire"),
    (15, "add: the sum of the forms is p or more"), (2, "add: the sum of the forms is exactly p"),
    (20, "sub: the difference of the forms borrows")] ++
    (if wide then [(5, "mul: a row left a word above the limbs")] else [])) p

/-- Bytes at an offset read as the number of the `4 n` bytes from there, below `p` only.

Bytes past the end read as zero. -/
@[nospecialize, noinline]
def bytes (n : Nat) [Words n] [Limbs n] (genP : Gen Nat) : Property IO := pureIO do
  let p ← forAll genP
  let a ← forAll (Gen.frequency [(3, genAround p (2 ^ (32 * n))), (2, genNear p (32 * n))])
  let (before, cut) ← forAll (Gen.zip (Gen.nat (.linear 0 5)) (Gen.frequency [
    (2, pure (4 * n)), (1, Gen.nat (.constant 0 (4 * n + 2)))]))
  let some M := mkModulus n p | failWith "no Montgomery constants"
  let bytes := (ByteArray.mk (Array.replicate before 0xff) ++ beBytes (4 * n) a).extract 0
    (before + cut)
  let value := beNat (bytes.extract before (before + 4 * n)) * 256 ^ (4 * n - min cut (4 * n))
  classify "the number is below p" (value < p)
  classify "the number is p" (value == p)
  classify "the number is above p" (value > p)
  classify "the bytes end early" (cut < 4 * n)
  let read : Option (Montgomery M) := Montgomery.ofBytesBE bytes before
  read.map (·.toNat) === (if value < p then some value else none)

/-- The words of `n` limbs, for an `n` known at run time. -/
@[instance_reducible] def wordsOf : (n : Nat) → Words n
  | 0 => inferInstance
  | n + 1 => @Montgomery.instWordsSucc n (wordsOf n)

/-- The CIOS product on words of any count from 1 to 16 is `a b R⁻¹ mod p`, for `a < p`. -/
def wordsProduct : Property IO := pureIO do
  let n ← forAll (Gen.nat (.constant 1 16))
  let R := 2 ^ (32 * n)
  let p ← forAll (genModulus n [R - 1, R / 2 + 1, R / 2 - 1, 1, 3])
  let a ← forAll ((· % p) <$> genNear p (32 * n))
  let b ← forAll (Gen.frequency [(2, genNear p (32 * n)), (1, (fun (d, other) =>
    (firingForm n p a d).getD other) <$> Gen.zip (Gen.nat (.constant 0 200)) (genNear p (32 * n)))])
  have : Words n := wordsOf n
  let digits (x : Nat) : Nat → UInt64 := Montgomery.Limbs.digit x
  let out : Words.W n := Montgomery.mulWords (n := n) (digits p) (UInt64.ofNat (negInv32 p))
    (digits a) (digits b) id
  let (fired, above) := ciosBranches n p a b
  classify "the final subtraction fired" fired
  classify "a row left a word above the limbs" above
  classify "b is p or more" (b ≥ p)
  label s!"{n} limbs"
  Montgomery.num n (Words.word out) 0 === a * b % p * modInv p (R % p) % p

/-- The product in two parts, split at any row, is the whole product when `2 p ≤ R`.

`Montgomery.mulLow` says so: the limbs that join the parts hold the whole state only then.

Above `R / 2` the property only counts how often the two differ. -/
@[nospecialize, noinline]
def split (n : Nat) [Words n] [Limbs n] (genP : Gen Nat) : Property IO := pureIO do
  let R := 2 ^ (32 * n)
  let p ← forAll genP
  let k ← forAll (Gen.nat (.constant 0 n))
  let a ← forAll ((· % p) <$> genNear p (32 * n))
  let b ← forAll (Gen.frequency [(2, genNear p (32 * n)), (1, (fun (d, other) =>
    (firingForm n p a d).getD other) <$> Gen.zip (Gen.nat (.constant 0 200)) (genNear p (32 * n)))])
  have : Words k := wordsOf k
  have : Words (n - k) := wordsOf (n - k)
  let digits (x : Nat) : Nat → UInt64 := Montgomery.Limbs.digit x
  let pinv := UInt64.ofNat (negInv32 p)
  let lo : Limbs.T n := Montgomery.mulLow (n := n) k (digits p) pinv (digits a) (digits b)
  let whole : Limbs.T n := Montgomery.mulHigh (n := n) (n - k) (digits p) pinv (digits a)
    (digits b) k lo Limbs.pack
  let want := a * b % p * modInv p (R % p) % p
  label s!"split at row {k}"
  classify "the final subtraction fired" (ciosBranches n p a b).1
  if 2 * p ≤ R then
    label "2 p ≤ R"
    Limbs.val whole === want
  else
    classify "2 p > R: the parts give the product" (Limbs.val whole == want)
    classify "2 p > R: the parts give another number" (Limbs.val whole != want)

/-- Fails by design: the product in two parts is the whole product also when `2 p > R`.

`Montgomery.mulLow` states the condition `2 p ≤ R`, and this property shows that it is needed.

Above `R / 2` a row can leave a word above the limbs, and the limbs that join the parts drop it.

EthLib splits the product only for `Fp` of BLS12-381, where `2 p < R`. -/
@[nospecialize, noinline]
def splitAbove (n : Nat) [Words n] [Limbs n] : Property IO := pureIO do
  let R := 2 ^ (32 * n)
  let p ← forAll ((fun d => R - 1 - 2 * d) <$> Gen.nat (.exponential 0 (R / 4 - 1)))
  let k ← forAll (Gen.nat (.constant 0 n))
  let a ← forAll ((p - 1 - ·) <$> Gen.nat (.exponential 0 (p - 1)))
  let b ← forAll ((p - 1 - ·) <$> Gen.nat (.exponential 0 (p - 1)))
  have : Words k := wordsOf k
  have : Words (n - k) := wordsOf (n - k)
  let digits (x : Nat) : Nat → UInt64 := Montgomery.Limbs.digit x
  let pinv := UInt64.ofNat (negInv32 p)
  let lo : Limbs.T n := Montgomery.mulLow (n := n) k (digits p) pinv (digits a) (digits b)
  let whole : Limbs.T n := Montgomery.mulHigh (n := n) (n - k) (digits p) pinv (digits a)
    (digits b) k lo Limbs.pack
  Limbs.val whole === a * b % p * modInv p (R % p) % p

end KernelsProperty.Mont

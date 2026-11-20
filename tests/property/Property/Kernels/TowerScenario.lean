import Property.Kernels.Tower

/-!
# An accumulator in `Fp12`, as commands

A running element of `Fp12` goes through products, inverses and Frobenius maps.

Once it lies in the cyclotomic subgroup, it also goes through the cyclotomic formulas.

The oracle, the modulus and the operations of the curve are in the context.

So one set of commands serves BLS12-381 and alt_bn128, and a command holds only its operand.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace KernelsProperty.TowerScenario

open KernelsProperty.Tower

/-- The context: the reference, the curve, and the operations of EthLib on coefficients. -/
structure Field where
  oracle : Oracle
  curve : String
  modulus : Nat
  mul : List Nat → List Nat → List Nat
  inverse : List Nat → List Nat
  frobenius : List Nat → List Nat
  /-- The cyclotomic square and power, on the curves that have them. -/
  cyclotomic : Option ((List Nat → List Nat) × (List Nat → Nat → List Nat))

/-- The operations of BLS12-381. -/
def blsField (oracle : Oracle) : Field where
  oracle := oracle
  curve := "bls"
  modulus := Bls.Fp.modulus
  mul a b := coeffs (ofCoeffs a * ofCoeffs b)
  inverse a := coeffs (ofCoeffs a).inverse
  frobenius a := coeffs (ofCoeffs a).frobenius
  cyclotomic := some (fun a => coeffs (ofCoeffs a).cyclotomicSquare,
    fun a e => coeffs ((ofCoeffs a).cyclotomicPow e))

/-- The operations of alt_bn128, which has no cyclotomic formulas. -/
def bnField (oracle : Oracle) : Field where
  oracle := oracle
  curve := "bn"
  modulus := AltBn128.Fp.modulus
  mul a b := bnCoeffs (bnOf a * bnOf b)
  inverse a := bnCoeffs (bnOf a).inverse
  frobenius a := bnCoeffs (bnOf a).frobenius
  cyclotomic := none

/-- The model: the coefficients of the accumulator, and whether it is known to be cyclotomic. -/
structure Acc where
  value : List Nat
  cyclotomic : Bool
  deriving Repr

/-- Ask the reference for an operation on the accumulator. -/
def Field.ask (f : Field) (op : String) (a : List Nat) (rest : List String := []) :
    TestT IO (List Nat) := do
  unword (← f.oracle.ask (["f12", f.curve, op, word a] ++ rest))

/-- Multiply by an operand. -/
structure Mul where
  operand : List Nat

/-- The coefficients of one. -/
def one : List Nat := 1 :: List.replicate 11 0

instance : Command Mul Acc Field IO where
  apply f c s := do
    let want ← f.ask "mul" s.value [word c.operand]
    f.mul s.value c.operand === want
    pure ⟨want, s.cyclotomic && c.operand == one⟩
  label c := s!"MUL({word c.operand})"
  build f := Mul.mk <$> genElement f.modulus
  next _ c s := { s with cyclotomic := s.cyclotomic && c.operand == one }
  -- In the cyclotomic subgroup, half of the operands are one, which keeps the element there.
  buildIn f s :=
    if s.cyclotomic then Gen.frequency [(1, pure ⟨one⟩), (1, Mul.mk <$> genElement f.modulus)]
    else Mul.mk <$> genElement f.modulus

/-- Square. -/
structure Square where

instance : Command Square Acc Field IO where
  apply f _ s := do
    let want ← f.ask "mul" s.value [word s.value]
    f.mul s.value s.value === want
    pure { s with value := want }
  label _ := "SQUARE"
  build _ := pure {}

/-- Invert; zero stays zero. -/
structure Invert where

instance : Command Invert Acc Field IO where
  apply f _ s := do
    let want ← f.ask "inv" s.value
    classify "an inverse of zero" (s.value.all (· == 0))
    f.inverse s.value === want
    pure { s with value := want }
  label _ := "INVERT"
  build _ := pure {}

/-- The `p`-th power. -/
structure Frobenius where

instance : Command Frobenius Acc Field IO where
  apply f _ s := do
    let want ← f.ask "frob" s.value ["1"]
    f.frobenius s.value === want
    pure { s with value := want }
  label _ := "FROBENIUS"
  build _ := pure {}

/-- The easy part of the final exponentiation: the power by `(p^6 - 1) (p^2 + 1)`.

It is built from the conjugate, which is six Frobenius maps, an inverse and two more maps. -/
structure EasyPart where

instance : Command EasyPart Acc Field IO where
  check _ _ s := !s.cyclotomic
  apply f _ s := do
    let want ← f.ask "easy" s.value
    let conjugate := (List.range 6).foldl (fun a _ => f.frobenius a) s.value
    let t := f.mul conjugate (f.inverse s.value)
    f.mul (f.frobenius (f.frobenius t)) t === want
    label "reached the cyclotomic subgroup"
    pure ⟨want, !s.value.all (· == 0)⟩
  label _ := "EASY_PART"
  build _ := pure {}
  next _ _ s := { s with cyclotomic := true }

/-- The cyclotomic square, which is the square on the cyclotomic subgroup. -/
structure CycloSquare where

instance : Command CycloSquare Acc Field IO where
  check f _ s := s.cyclotomic && f.cyclotomic.isSome
  apply f _ s := do
    let some (square, _) := f.cyclotomic | failWith "the curve has no cyclotomic square"
    let want ← f.ask "mul" s.value [word s.value]
    square s.value === want
    label "a cyclotomic square ran"
    pure { s with value := want }
  label _ := "CYCLO_SQUARE"
  build _ := pure {}

/-- The cyclotomic power. -/
structure CycloPow where
  exponent : Nat

instance : Command CycloPow Acc Field IO where
  check f _ s := s.cyclotomic && f.cyclotomic.isSome
  apply f c s := do
    let some (_, power) := f.cyclotomic | failWith "the curve has no cyclotomic power"
    let want ← f.ask "pow" s.value [toString c.exponent]
    power s.value c.exponent === want
    label "a cyclotomic power ran"
    pure { s with value := want }
  label c := s!"CYCLO_POW({c.exponent})"
  build _ := CycloPow.mk <$> Gen.frequency [(1, Gen.nat (.linear 0 5)), (1, genNatBits 64)]

/-- Any sequence of the operations keeps the accumulator equal to the reference's. -/
def accumulator (mode : Mode) (field : Field) : Property IO :=
  scenarioFrom ((fun value => Acc.mk value false) <$> genElement field.modulus) mode field
    [Command.gen Mul, Command.gen Square, Command.gen Invert, Command.gen Frobenius,
      Command.gen EasyPart, Command.gen EasyPart, Command.gen CycloSquare, Command.gen CycloSquare,
      Command.gen CycloPow]
    (.linear 1 20) fun s => do
      annotate s!"start: {word s.value}"
      pure s

end KernelsProperty.TowerScenario

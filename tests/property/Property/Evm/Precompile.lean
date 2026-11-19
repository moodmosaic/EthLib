import Property.Evm.Program

/-!
# The precompiles beside the reference

The call data is near valid.

A reference library builds a valid input from a few numbers.

Then one rule of the precompile is broken, or the length is changed.

The answer is that of the precompile of the Python execution-specs at the same fork.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution.Evm

namespace EvmProperty

/-- What EthLib answers to a call of a precompile, in the text form of the oracle.

The answer is `none` for an address that is no precompile at the fork, and `halt` for a failure.

Else it is the gas left and the output. -/
def precompileEthLib (fork : Fork) (address : Nat) (data : ByteArray) (gas : Nat) : String :=
  if !Precompiles.isPrecompile fork address then "none"
  else match Precompiles.run fork address data gas with
    | none => "none"
    | some (.error _) => "halt"
    | some (.ok output) =>
      let price := (Precompiles.price fork address data).getD 0
      if gas < price then "halt" else s!"ok {gas - price} {hex output}"

/-- The gas of a call: around the price, since the charge is where an off-by-one sits.

The price is EthLib's, which only places the draw: the reference decides what the gas buys. -/
def gasAround (fork : Fork) (address : Nat) (data : ByteArray) (choice : Nat) : Nat :=
  let price := min ((Precompiles.price fork address data).getD 100000) 3000000
  match choice with
  | 0 => price
  | 1 => price - 1
  | 2 => price + 1
  | 3 => 0
  | _ => price + 100000

/-- The draw of the gas: mostly enough, so the body of the precompile runs. -/
def genGasChoice : Gen Nat := Gen.frequency [(3, pure 0), (2, pure 1), (1, pure 2), (1, pure 3),
  (4, pure 4)]

/-- EthLib and the reference agree on one call. -/
def samePrecompile (oracle : Oracle) (fork : Fork × String) (address : Nat) (data : ByteArray)
    (choice : Nat) : TestT IO Unit := do
  let gas := gasAround fork.1 address data choice
  let answer ← oracle.ask ["pre", fork.2, toString address, toString gas, hex data]
  -- The reference names its error after `halt`, and EthLib's has another name.
  --
  -- Its fixed-width integers overflow on a length near 2^256, where the price is out of reach.
  let want := if answer.startsWith "halt" || answer.startsWith "crash OverflowError" then "halt"
    else answer
  annotate s!"address {address} at {fork.2} with gas {gas} on {hex data}: the reference says \
    {answer}"
  precompileEthLib fork.1 address data gas === want

/-- A recipe of call data: see `oracle/evm_inputs.py`. -/
structure Recipe where
  kind : String
  address : Nat
  a : Nat
  b : Nat
  c : Nat
  mutation : Nat
  cut : Nat
  deriving Repr

/-- The precompiles with a recipe; the slow ones, which pair points, are apart. -/
def fastKinds : List (String × Nat) := [("ecrecover", 1), ("bnadd", 6), ("bnmul", 7),
  ("g1add", 11), ("g1msm", 12), ("g2add", 13), ("g2msm", 14), ("mapfp", 16), ("mapfp2", 17),
  ("p256", 256)]

/-- The precompiles that pair points, which the reference computes slowly. -/
def slowKinds : List (String × Nat) := [("bnpairing", 8), ("blspairing", 15), ("pointeval", 10)]

/-- A number that a scalar or a seed is made of: small, or at an edge of 256 bits. -/
def genSeed : Gen Nat := Gen.frequency [(3, Gen.nat (.linear 0 50)), (2, genNatBits 256)]

/-- A recipe: one time in four valid, else with one of fifteen mutations, and mostly uncut. -/
def genRecipe (kinds : List (String × Nat)) : Gen Recipe := do
  let (kind, address) ← Gen.element kinds
  let (a, b, c) ← Gen.zip genSeed (Gen.zip genSeed genSeed)
  let mutation ← Gen.frequency [(1, pure 0), (3, Gen.nat (.constant 0 14))]
  let cut ← Gen.frequency [(8, pure 0), (2, Gen.nat (.constant 1 5))]
  pure ⟨kind, address, a, b, c, mutation, cut⟩

/-- Fusaka and later have every precompile, and the earlier forks say when each one starts. -/
def genPrecompileFork : Gen (Fork × String) :=
  Gen.frequency [(3, Gen.element (forks.drop 18)), (1, Gen.element forks)]

/-- A precompile answers a near-valid input as the reference does: output, price and failure. -/
def precompileRecipe (oracle : Oracle) (kinds : List (String × Nat)) : Property IO := propertyM do
  let recipe ← forAll (genRecipe kinds)
  let fork ← forAllWith (·.2) genPrecompileFork
  let choice ← forAll genGasChoice
  pure do
    let made ← oracle.ask ["mk", recipe.kind, toString recipe.a, toString recipe.b,
      toString recipe.c, toString recipe.mutation, toString recipe.cut]
    match unhex? made with
    | none => failWith s!"the oracle built no input: {made}"
    | some data => samePrecompile oracle fork recipe.address data choice

/-- A length field of MODEXP: zero, around a word, around the limit of EIP-7823, and huge. -/
def genModexpLength : Gen Nat :=
  Gen.frequency [
    (6, Gen.nat (.linear 0 40)),
    (3, Gen.element [0, 1, 31, 32, 33, 64, 96, 1023, 1024, 1025]),
    (1, Gen.element [2 ^ 32, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 255, 2 ^ 256 - 1])]

/-- Call data of MODEXP: three lengths, then a body that may be shorter or longer than they say. -/
def genModexp : Gen ByteArray := do
  let (baseLen, expLen, modLen) ← Gen.zip genModexpLength (Gen.zip genModexpLength genModexpLength)
  let said := min 200 (baseLen + expLen + modLen)
  let body ← Gen.frequency [
    (4, genBytes (.singleton said)),
    (2, genBytes (.linear 0 (said + 8))),
    (1, (fun n => ⟨(List.replicate n (0 : UInt8)).toArray⟩) <$> Gen.nat (.linear 0 said)),
    (1, (fun n => ⟨(List.replicate n (0xff : UInt8)).toArray⟩) <$> Gen.nat (.linear 0 said))]
  let header := beBytes 32 baseLen ++ beBytes 32 expLen ++ beBytes 32 modLen
  let cut ← Gen.frequency [(8, pure 96), (1, Gen.nat (.constant 0 96))]
  pure ⟨((header.take cut) ++ (if cut = 96 then body.toList else [])).toArray⟩

/-- Call data of BLAKE2F: the rounds, the state, the message, the offsets and the final flag. -/
def genBlake2f : Gen ByteArray := do
  let rounds ← Gen.frequency [(12, Gen.nat (.linear 0 20)), (1, Gen.element [300, 2 ^ 32 - 1])]
  let body ← genBytes (.singleton 208)
  let flag ← Gen.frequency [(4, Gen.element [0, 1]), (1, Gen.element [2, 255, 128])]
  let data := beBytes 4 rounds ++ body.toList ++ [flag]
  let size ← Gen.frequency [(8, pure 213), (1, Gen.element [0, 212, 214, 426])]
  pure ⟨((data ++ data).take size).toArray⟩

/-- Call data with no structure, at any address that is or was to be a precompile. -/
def genRawCall : Gen (Nat × ByteArray) :=
  Gen.zip (Gen.element [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 256, 0, 18, 255,
    257]) (Gen.frequency [
      (3, genBytes (.linear 0 300)),
      (1, (fun n => ⟨(List.replicate n (0 : UInt8)).toArray⟩) <$>
        Gen.element [0, 31, 32, 33, 64, 96, 128, 160, 192, 213, 256, 288, 384, 512])])

/-- The hash precompiles, MODEXP and BLAKE2F answer as the reference does on any bytes.

This is where the padding, the truncation and the gas formula of each fork are. -/
def precompileBytes (oracle : Oracle) : Property IO := propertyM do
  let (address, data) ← forAllWith (fun (a, d) => s!"{a} {hex d}") (Gen.frequency [
    (5, (fun d => (5, d)) <$> genModexp),
    (2, (fun d => (9, d)) <$> genBlake2f),
    (3, genRawCall)])
  let fork ← forAllWith (·.2) (Gen.frequency [(1, genPrecompileFork), (1, Gen.element forks)])
  let choice ← forAll genGasChoice
  pure (samePrecompile oracle fork address data choice)

end EvmProperty

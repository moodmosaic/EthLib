import Property.Kernels.Common
import EthLib.Base
import EthLib.Execution.Fees.BlobBaseFee

/-!
# Forks, chain configurations and blob schedules

`Base/Fork.lean`, `Base/ChainConfig.lean` and the blob schedule of each fork.

The answers come from tables written from the EIPs in `oracle/kernels.py`, and from two models.

A model reads a configuration another way than `activeFork` does.
-/

open Hedgehog Support EthLib EthLib.Base

namespace KernelsProperty.Chain

/-- Every fork, in the order of the type. -/
def forks : List Fork := (List.range (Fork.hegota.ctorIdx + 1)).map Fork.ofNat

/-- Any fork. -/
def genFork : Gen Fork := Gen.element forks

/-- The order of the forks, their names, and the comparison of any two, are the reference's.

The reference lists the names in the order of EIP-7568 and of the meta EIPs after it. -/
def forkOrder (oracle : Oracle) : Property IO := propertyM do
  let (a, b) ← forAll (Gen.zip genFork genFork)
  pure do
    let names := words (← oracle.ask ["forks"])
    forks.map Fork.name === names
    let index (f : Fork) : Nat := (names.findIdx? (· == f.name)).getD names.length
    classify "a < b" (decide (a < b))
    classify "a = b" (a == b)
    classify "a > b" (decide (b < a))
    decide (a < b) === decide (index a < index b)
    decide (a ≤ b) === decide (index a ≤ index b)
    decide (a ≥ b) === decide (index a ≥ index b)
    (compare a b == .lt) === decide (index a < index b)
    (a == b) === (index a == index b)

/-- A name reads back as its fork, and no other text is a name. -/
def forkNames : Property IO := pureIO do
  let fork ← forAll genFork
  Fork.ofName? fork.name === some fork
  let text ← forAll (Gen.frequency [
    (2, Gen.string (.linear 0 6) Gen.lower), (3, Fork.name <$> genFork),
    (1, pure fork.name.toUpper), (1, pure fork.name.capitalize), (1, pure (fork.name ++ " ")),
    (1, pure (" " ++ fork.name)), (1, pure (fork.name.dropEnd 1).toString),
    (1, Gen.element ["shanghai", "cancun", "prague", "osaka", "capella", "deneb", "electra",
      "fulu", "merge", "dao", "DAOFork", "bpo6", "bpo0", ""])])
  let known := forks.find? (·.name == text)
  classify "the text is a name" known.isSome
  Fork.ofName? text === known

/-- A block number and a timestamp: on an activation, one before, one after, or anywhere. -/
def genPoint (config : ChainConfig) : Gen (Nat × Nat) :=
  let blocks := config.activations.filterMap fun
    | (_, .block n) => some n
    | _ => none
  let times := config.activations.filterMap fun
    | (_, .time t) => some t
    | _ => none
  let near (xs : List Nat) (top : Nat) : Gen Nat :=
    Gen.frequency [
      (6, (fun (x, d) => (x + d) - 1) <$> Gen.zip (Gen.element (0 :: xs))
        (Gen.nat (.constant 0 2))),
      (1, Gen.nat (.exponential 0 top)), (1, Gen.nat (.constant 0 top))]
  Gen.zip (near blocks (2 * 15537394)) (near times (2 * 1767747671))

/-- The fork of a named network at a block is the reference's.

The reference walks its own table of the activations, written from the EIPs.

With `before`, the timestamps stay below it. -/
def activeNamed (oracle : Oracle) (network : String) (config : ChainConfig)
    (before : Option Nat := none) : Property IO :=
  propertyM do
    let (number, timestamp) ← forAll ((fun (n, t) =>
      match before with
      | some limit => (n, t % limit)
      | none => (n, t)) <$> genPoint config)
    pure do
      let want ← oracle.ask ["active", network, toString number, toString timestamp]
      let got := (config.activeFork number timestamp).map Fork.name
      let edge := config.activations.any fun
        | (_, .block n) => n == number || n == number + 1
        | (_, .time t) => t == timestamp || t == timestamp + 1
      classify "on an activation or one before it" edge
      classify "a fork by timestamp is active" (config.activations.any fun
        | (f, .time _) => some f == config.activeFork number timestamp
        | _ => false)
      classify "the timestamp is past a fork that the block number is not" (decide
        (number < 15537394 ∧ 1681338455 ≤ timestamp))
      got.getD "none" === want

/-- The constants of a named network are the reference's.

The activations of the forks in `without` are left out of the comparison. -/
def networkConstants (oracle : Oracle) (network : String) (config : ChainConfig)
    (without : List Fork := []) : Property IO := propertyM do
  pure do
    let want ← oracle.ask ["network", network]
    let activation : Activation → String
      | .block n => s!"block:{n}"
      | .time t => s!"time:{t}"
    let rows := (config.activations.filter fun (f, _) => !without.contains f).map fun (f, a) =>
      s!"{f.name}={activation a}"
    s!"{config.chainId.toNat} {(hex ⟨config.depositContractAddress.toArray⟩)} " ++
      " ".intercalate rows === want
    ensure (decide config.Ordered) "the configuration is not ordered"
    ensure (ChainConfig.activationsOrdered config.activations) "a block fork follows a time fork"
    config.blobSchedules.length === 0

/-- An activation: by block or by time, at a small value so that ties are common. -/
def genActivation (top : Nat := 6) : Gen Activation :=
  Gen.frequency [
    (1, Activation.block <$> Gen.nat (.constant 0 top)),
    (1, Activation.time <$> Gen.nat (.constant 0 top))]

/-- A list of forks with activations: in the order of the timeline, or in any order. -/
def genActivations : Gen (List (Fork × Activation)) :=
  let ordered : Gen (List (Fork × Activation)) := do
    let chosen ← Gen.subsequence forks
    let split ← Gen.nat (.constant 0 chosen.length)
    let steps ← Gen.list (.singleton chosen.length) (Gen.nat (.constant 0 2))
    -- Blocks first, then times, each no earlier than the one before.
    let (_, _, out) := (chosen.zip steps).zipIdx.foldl (fun (block, time, out) ((f, d), i) =>
      if i < split then (block + d, time, out ++ [(f, Activation.block (block + d))])
      else (block, time + d, out ++ [(f, Activation.time (time + d))])) (0, 0, [])
    pure out
  Gen.frequency [(1, ordered), (1, Gen.list (.linear 0 8) (Gen.zip genFork genActivation))]

/-- The active fork of any configuration is the latest fork whose activation the block reached.

On a configuration in the order of the timeline it is also the last one reached in the list.

No fork is active before every activation. -/
def activeGenerated : Property IO := pureIO do
  let activations ← forAll genActivations
  let (number, timestamp) ← forAll (Gen.zip (Gen.nat (.constant 0 7)) (Gen.nat (.constant 0 7)))
  let config : ChainConfig :=
    { chainId := 1, depositContractAddress := Vector.replicate 20 0, activations }
  let reached := activations.filter fun (_, a) =>
    match a with
    | .block n => n ≤ number
    | .time t => t ≤ timestamp
  let latest := reached.foldl (fun (best : Option Fork) (f, _) =>
    match best with
    | none => some f
    | some g => if g.ctorIdx < f.ctorIdx then some f else some g) none
  let got := config.activeFork number timestamp
  classify "the configuration is ordered" (decide config.Ordered)
  classify "no fork is active" got.isNone
  classify "two reached forks share an activation" (reached.any fun (f, a) =>
    reached.any fun (g, b) => f != g && a == b)
  classify "a fork is never reached" (reached.length < activations.length)
  got === latest
  if decide config.Ordered then got === (reached.getLast?.map Prod.fst)
  -- `Ordered` and `activationsOrdered`, each against its sentence.
  let pairs := activations.zipIdx.flatMap fun (x, i) =>
    (activations.drop (i + 1)).map fun y => (x, y)
  let le : Activation → Activation → Bool
    | .block m, .block n => m ≤ n
    | .block _, .time _ => true
    | .time _, .block _ => false
    | .time s, .time t => s ≤ t
  decide config.Ordered === pairs.all fun (x, y) => x.1.ctorIdx < y.1.ctorIdx && le x.2 y.2
  ChainConfig.activationsOrdered activations ===
    !(activations.any fun (f, a) => activations.any fun (g, b) =>
      (a matches .time _) && (b matches .block _) && f.ctorIdx < g.ctorIdx)

/-- A blob schedule with small numbers. -/
def genSchedule : Gen BlobSchedule := do
  let target ← Gen.nat (.constant 0 9)
  let more ← Gen.nat (.constant 0 9)
  let fraction ← Gen.nat (.constant 1 9)
  if h : target ≤ target + more ∧ 0 < target + more + 1 ∧ 0 < fraction then
    pure { target, max := target + more + 1, baseFeeUpdateFraction := fraction,
           target_le_max := by omega, max_pos := h.2.1, baseFeeUpdateFraction_pos := h.2.2 }
  else Gen.discard

/-- The blob schedule of a chain at a block is the last one in its list that the block reached.

Without one, it is the schedule of the fork. -/
def blobScheduleAt : Property IO := pureIO do
  let schedules ← forAll (Gen.list (.linear 0 6) (Gen.zip (genActivation 3) genSchedule))
  let (number, timestamp) ← forAll (Gen.zip (Gen.nat (.constant 0 7)) (Gen.nat (.constant 0 7)))
  let fork ← forAll (Gen.element (forks.filter (Fork.dencun ≤ ·)))
  let config : ChainConfig := { chainId := 1, depositContractAddress := Vector.replicate 20 0,
                                activations := [], blobSchedules := schedules }
  let want := schedules.foldl (fun (best : Option BlobSchedule) (a, s) =>
    let reached : Bool := match a with
      | .block n => n ≤ number
      | .time t => t ≤ timestamp
    if reached then some s else best) none
  classify "the chain sets a schedule" want.isSome
  classify "the chain sets none" want.isNone
  classify "two reached schedules share an activation" (schedules.zipIdx.any fun ((a, _), i) =>
    a.reached number timestamp && schedules.zipIdx.any fun ((b, _), j) => i != j && a == b)
  config.blobScheduleAt number timestamp === want
  if h : Fork.dencun ≤ fork then
    Execution.Fees.BlobBaseFee.chainBlobSchedule config fork number timestamp h ===
      want.getD (Execution.Fees.BlobBaseFee.blobSchedule fork h)

/-- The blob schedule of every fork from Dencun on is the reference's.

The reference holds the values of EIP-4844, EIP-7691, EIP-8134 and EIP-8135. -/
def blobSchedules (oracle : Oracle) : Property IO := propertyM do
  let fork ← forAll genFork
  pure do
    let want ← oracle.ask ["blob", fork.name]
    classify "before Dencun" (decide (fork < .dencun))
    if h : Fork.dencun ≤ fork then
      let s := Execution.Fees.BlobBaseFee.blobSchedule fork h
      s!"{s.target} {s.max} {s.baseFeeUpdateFraction}" === want
    else want === "none"

end KernelsProperty.Chain

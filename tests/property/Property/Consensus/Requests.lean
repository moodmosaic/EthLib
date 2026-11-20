import Property.Consensus.Operations

/-!
# Requests that need a large registry

A consolidation is queued only when one condition holds.

The churn left for consolidations must exceed one minimal activation balance.

On the registries of `genOperationState` it never does.

There the balance churn is at its floor, and the churn of activations and exits takes all of it.

So `process_consolidation_request` passed there.

But there it tested only its refusals and the switch to compounding credentials.

Here the registry holds validators of 2048 ETH, enough of them for the churn to leave room.

Each property asks, with `cover`, that its call changes the state in a share of the cases.

So a generator that no longer reaches the rule fails the run.
-/

open Hedgehog Support EthLib EthLib.Consensus

namespace ConsensusProperty

/-- A validator that may be the target of a consolidation: compounding, of 2048 ETH or near. -/
def genLargeValidator : Gen String := do
  let seed ← Gen.nat (.linear 0 5)
  let effective ← Gen.frequency [(5, pure 2048), (1, Gen.nat (.linear 1900 2048))]
  let extra ← Gen.frequency [(3, pure 0), (1, Gen.nat (.linear 0 (3 * increment)))]
  pure s!"v=2,{seed},{effective * increment},{effective * increment + extra},\
0,0,0,{far},{far},7,7,0"

/-- A validator that may be the source: credentials of an address, of 32 ETH or near. -/
def genSourceValidator : Gen String := do
  let prefix_ ← Gen.frequency [(3, pure 1), (2, pure 2), (1, pure 0)]
  let seed ← Gen.nat (.linear 0 5)
  let effective ← Gen.frequency [(4, pure 32), (1, Gen.nat (.linear 16 64))]
  let extra ← Gen.frequency [(3, pure 0), (1, Gen.nat (.linear 0 (3 * increment)))]
  pure s!"v={prefix_},{seed},{effective * increment},{effective * increment + extra},\
0,0,0,{far},{far},7,7,0"

/-- A state whose churn leaves room for consolidations: six large validators or more. -/
def genLargeState : Gen (List String) :=
  genStateOf genLateSlot do
    let large ← Gen.list (.constant 6 10) genLargeValidator
    let rest ← Gen.list (.constant 2 8)
      (Gen.frequency [(5, genSourceValidator), (1, genSettledValidator), (1, genValidator)])
    Gen.shuffle (large ++ rest)

/-- The address of the source's credentials mostly, and two validators of the registry. -/
def genConsolidation (same : Bool) : Gen (List String) := do
  let address ← Gen.frequency [(8, pure 9), (1, Gen.nat (.linear 0 5))]
  let source ← Gen.nat (.constant 0 15)
  let target ← if same then pure source else Gen.nat (.constant 0 15)
  pure [s!"{address},{source},{target}"]

/-- The property with a minimum of cases in which its call changes the state.

A class named twice keeps the greater minimum.

So naming it here with nothing counted adds the minimum to the class that the comparison counts. -/
def changing (minimum : Nat) (p : Property IO) : Property IO :=
  { p with test := (fun test => do
      cover minimum "the state changed" false
      test) <$> p.test }

/-- A call of `operations` under another name, on these states.

It must change the state in a minimum of cases. -/
def requestProperty (oracle : Oracle) (name call : String) (arguments : Gen (List String))
    (minimum : Nat) : List (String × Property IO) :=
  match operations.find? (·.name = call) with
  | none => []
  | some found =>
    let words :=
      (fun state arguments => state ++ ["|"] ++ arguments) <$> genLargeState <*> arguments
    [(name, changing minimum (agrees oracle found.forks found.name words found.run))]

/-- The requests on a large registry. -/
def requestProperties (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  (requestProperty oracle "a consolidation of one validator into another"
      "process_consolidation_request" (genConsolidation false) 8 ++
    requestProperty oracle "a switch to compounding credentials"
      "process_consolidation_request" (genConsolidation true) 4 ++
    requestProperty oracle "a withdrawal request on a large registry"
      "process_withdrawal_request" ((operations.find? (·.name = "process_withdrawal_request")).map
        (·.arguments) |>.getD (pure [])) 15).map
    fun (name, p) => (name, (p.withCoverFrom 300).withTests cases)

end ConsensusProperty

import Property.ForkChoice.Store
import EthLib.Consensus.ForkChoice.FastConfirmation

/-!
# The fast confirmation rule as a state machine, against consensus-specs

The store, its blocks and its votes are those of `Property/ForkChoice/Store.lean`.

That machine compares the store after every command, and this one runs on top of it.

It adds the store of the fast confirmation rule, which no earlier driver ran.

A step is a command of the fork choice, a run of the rule, or slots that each end with a run.

After every step the driver compares what the rule tracks and what it decides on the way.

That is the confirmed block, the observed checkpoints, the two heads, and the safety thresholds.

EthLib's rule differs from the pinned consensus-specs in three ways that its CHANGELOG states.

The oracle applies the same three changes to consensus-specs, see `protocols_forkchoice.py`.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz
open ForkChoiceProperty (P C Shape Cmd rootHex8 slotMs)

namespace ConfirmationProperty

/-- A step of the machine. -/
inductive Step where
  /-- A command of the fork choice. -/
  | base (cmd : Cmd)
  /-- A run of the rule, at whatever time it is. -/
  | confirm
  /-- Slots one after another, each with a block on the tip and its votes, then a run of the rule.

  The rule moves the confirmed block only when votes arrive slot after slot. -/
  | grow (parent count lateMs : Nat)
  /-- Empty slots one after another, each with a run of the rule at its start. -/
  | idle (count : Nat)
  /-- What a node keeps of a block confirmed before a restart. -/
  | restart (index : Nat)
  deriving Repr

/-- The shape of the run, and how often the rule ran. -/
structure Run where
  /-- The clock and the blocks of the fork choice machine. -/
  shape : Shape
  /-- The slot of the last run of the rule, if it ran. -/
  confirmedAt : Option Nat
  deriving Repr

/-- The commands that a step stands for, each with whether the rule runs after it. -/
def Step.commands (shape : Shape) : Step → List (Cmd × Bool)
  | .base cmd => [(cmd, false)]
  | .confirm | .restart _ => []
  | .grow parent count lateMs =>
    (List.range count).map fun i =>
      (.chain (if i = 0 then parent else shape.slots.size + i - 1) 1 0 lateMs, true)
  | .idle count =>
    (List.range count).map fun i =>
      (.tick (if i = 0 then slotMs - shape.timeMs % slotMs else slotMs), true)

/-- The run after a step. -/
def Run.step (run : Run) (step : Step) : Run :=
  let shape := (step.commands run.shape).foldl (fun s (cmd, _) => s.step cmd) run.shape
  let ran := match step with
    | .base _ | .restart _ => false
    | _ => true
  { shape, confirmedAt := if ran then some shape.now else run.confirmedAt }

/-- Whether a step names only blocks that exist. -/
def Run.allows (run : Run) : Step → Bool
  | .base cmd => run.shape.allows cmd
  | .confirm | .idle _ => true
  | .grow parent count lateMs => parent < run.shape.slots.size && 0 < count && lateMs < slotMs
  | .restart index => index < run.shape.slots.size

/-- A step: mostly slots that grow the chain and run the rule, as a node does. -/
def genStep (run : Run) : Gen Step :=
  let tip := run.shape.slots.size - 1
  Gen.frequency [
    (5, Step.base <$> ForkChoiceProperty.genCmd run.shape),
    (6, do
      let parent ← Gen.frequency [(6, pure tip), (1, ForkChoiceProperty.genIndex run.shape)]
      let count ← Gen.frequency [(3, Gen.nat (.linear 1 12)), (1, Gen.nat (.linear 1 30))]
      Step.grow parent count <$> Gen.element [0, 100, 1999]),
    (2, pure Step.confirm),
    (1, Step.idle <$> Gen.nat (.linear 1 10)),
    (1, Step.restart <$> ForkChoiceProperty.genIndex run.shape)]

/-- A checkpoint as the oracle writes it here. -/
def checkpointShort (c : Checkpoint) : String := s!"{c.epoch}:{rootHex8 c.root}"

/-- A value or `e`. -/
def shown {ε α : Type} (show_ : α → String) : Except ε α → String
  | .ok a => show_ a
  | .error _ => "e"

/-- A truth value or `e`. -/
def flag {ε : Type} (test : Except ε Bool) : String :=
  shown (fun b => if b then "t" else "f") test

/-- What the oracle writes of its own fast confirmation store. -/
def view {fork : Fork} (store : Store P fork) (fcr : FastConfirmationStore) : String :=
  let config := C fork
  let headRoot := (·.root) <$> store.getHead config
  let withHead {α : Type} (compute : Root → Except ForkChoiceError α) :
      Except ForkChoiceError α := headRoot >>= compute
  -- The last blocks of the chain of the head, where the rule decides.
  let chain : List Root := match headRoot with
    | .error _ => []
    | .ok head => Id.run do
      let mut roots := []
      let mut root := head
      for _ in [0:5] do
        match store.blocks[root]? with
        | none => break
        | some block =>
          roots := roots ++ [root]
          root := block.parentRoot
      pure roots
  let source := store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint
  let safety := chain.map fun root =>
    let parentKnown := (store.blocks[root]?.map fun block =>
      store.blocks.contains block.parentRoot).getD false
    match source, parentKnown with
    | .ok state, true =>
      ":".intercalate [rootHex8 root,
        shown (fun (w : Gwei) => toString w)
          (withHead fun head => store.computeSafetyThreshold config head root state),
        shown (fun (w : Gwei) => toString w)
          (withHead fun head => store.getAdversarialWeight config head state root),
        flag (withHead fun head =>
          store.isOneConfirmed config head state (store.tallyVotes state) root)]
    | _, _ => s!"{rootHex8 root}:e:e:e"
  let words := [
    s!"c={rootHex8 fcr.confirmedRoot}",
    s!"po={checkpointShort fcr.previousEpochObservedJustifiedCheckpoint}",
    s!"co={checkpointShort fcr.currentEpochObservedJustifiedCheckpoint}",
    s!"pg={checkpointShort fcr.previousEpochGreatestUnrealizedCheckpoint}",
    s!"ph={rootHex8 fcr.previousSlotHead}",
    s!"ch={rootHex8 fcr.currentSlotHead}",
    "nc=" ++ flag (withHead (store.willNoConflictingCheckpointBeJustified config)),
    "tj=" ++ flag (withHead (store.willCurrentTargetBeJustified config)),
    "ts=" ++ shown (fun (w : Gwei) => toString w) (withHead (store.getCurrentTargetScore config)),
    "hs=" ++ shown (fun (w : Gwei) => toString w)
      (withHead (store.computeHonestFfgSupportForCurrentTarget config)),
    "sf=" ++ flag (withHead fun head =>
      store.isConfirmedChainSafe config fcr head fcr.confirmedRoot),
    "bf=" ++ flag (store.blockShouldBeFinalized config fcr.confirmedRoot),
    "st=" ++ ",".intercalate safety]
  let safe := if bellatrix : .bellatrix ≤ fork then
      ["se=" ++ shown rootHex8 (store.getSafeExecutionBlockHash fcr bellatrix)]
    else []
  " ".intercalate (words ++ safe)

/-- EthLib's two stores. -/
structure Sut (fork : Fork) where
  /-- The store of the fork choice, with the oracle. -/
  base : ForkChoiceProperty.Sut fork
  /-- The store of the rule. -/
  fcr : FastConfirmationStore

/-- One line of the oracle. -/
def ask {fork : Fork} (sut : Sut fork) (words : List String) : TestT IO (List String) :=
  evalIO (ForkChoiceProperty.askWords sut.base.oracle words)

/-- Run the rule on both sides, and compare its verdict and what it tracks after. -/
def runRule {fork : Fork} (sut : Sut fork) (atEpochStart : Bool) (long : Bool) :
    TestT IO (Sut fork) := do
  let [status, expected] ← ask sut ["px_confirm"] | failWith "px_confirm: a malformed answer"
  let store := sut.base.store
  let finalized := store.finalizedCheckpoint.root
  match store.onFastConfirmation (C fork) sut.fcr with
  | .error e =>
    label "the rule: refused"
    ensure (status == "error") s!"EthLib refuses a run of the rule that the reference accepts: {e}"
    view store sut.fcr === expected
    pure sut
  | .ok fcr =>
    ensure (status == "ok") "EthLib accepts a run of the rule that the reference refuses"
    let moved := fcr.confirmedRoot ≠ sut.fcr.confirmedRoot
    cover (if long then 12 else 0) "the rule: the confirmed block moved forward"
      (moved && fcr.confirmedRoot ≠ finalized)
    cover (if long then 1 else 0) "the rule: back to the finalized block"
      (moved && fcr.confirmedRoot = finalized)
    classify "the rule: ran at the start of an epoch" atEpochStart
    let observed := fcr.currentEpochObservedJustifiedCheckpoint
    classify "the rule: the observed justified checkpoint moved"
      (observed ≠ sut.fcr.currentEpochObservedJustifiedCheckpoint)
    view store fcr === expected
    pure { sut with fcr }

/-- Run a step on both sides, and compare the stores of the fork choice and of the rule. -/
def applySut {fork : Fork} (long : Bool) (sut : Sut fork) (before after : Run) (step : Step) :
    TestT IO (Sut fork) := do
  let mut sut := sut
  let mut shape := before.shape
  for (cmd, thenRule) in step.commands before.shape do
    shape := shape.step cmd
    sut := { sut with base := ← ForkChoiceProperty.applySut sut.base shape cmd }
    if thenRule then
      -- The model before the step says whether the rule already ran in this slot.
      classify "the rule: twice in one slot" (before.confirmedAt == some shape.now)
      sut ← runRule sut (shape.now % ForkChoiceProperty.epochSlots == 0) long
  match step with
  | .confirm =>
    classify "the rule: twice in one slot" (before.confirmedAt == some after.shape.now)
    sut ← runRule sut (after.shape.now % ForkChoiceProperty.epochSlots == 0) long
  | .restart index =>
    match ← ask sut ["px_restart", toString index] with
    | [rootText, expected] =>
      match (unhex? rootText).map fun bytes => (Vector.ofFn fun i : Fin 32 => bytes[i.val]!) with
      | none => failWith "px_restart: a malformed root"
      | some root =>
        let got := shown rootHex8 (do
          let head ← sut.base.store.getHead (C fork)
          sut.base.store.getRestartResilientConfirmedRoot (C fork) sut.fcr head.root root)
        classify "a restart: keeps the block confirmed before" (got == rootHex8 root)
        got === expected
    | _ => label "a restart: of a block that the store lacks"
  | _ => pure ()
  let [expected] ← ask sut ["px_view"] | failWith "px_view: a malformed answer"
  view sut.base.store sut.fcr === expected
  pure sut

/-- The fast confirmation rule of EthLib agrees with the reference on every sequence of steps. -/
def machine (fork : Fork) (forkName : String) (oracle : Oracle) (long : Bool := true) :
    StateMachine Run Step (Sut fork) IO where
  initState := do
    let shape ← (ForkChoiceProperty.model forkName false).initState
    pure { shape, confirmedAt := none }
  transitions := genStep
  apply := Run.step
  preconditions := Run.allows
  initSut run := do
    let base ← ForkChoiceProperty.initSut fork oracle run.shape
    pure { base, fcr := getFastConfirmationStore base.store }
  applySut := applySut long

end ConfirmationProperty

import Property.ForkChoice.Store
import EthLib.Consensus.ForkChoice.OptimisticSync

/-!
# Optimistic sync as a scenario of commands, against consensus-specs and the guide

A node imports a block before the execution layer has judged its payload.

The execution layer later says that the payload is valid, or invalid with a latest valid hash.

The commands are those events, each a type of its own, drawn in any order in madhouse mode.

Each command type takes the fork as an index, since the state and the context do.

A command names a block that exists: `buildIn` reads the number of blocks, and `next` counts them.

The oracle keeps the optimistic store of consensus-specs and runs its four functions on it.

It moves that store as the prose of `optimistic-sync.md` says, see `protocols_optimistic.py`.

After every command both sides must hold the same optimistic roots and the same blocks.

They must also agree on the latest verified ancestor of every block, and on the head.

The scenario runs from Bellatrix to Fulu.

From Gloas the guide has no text, and EthLib reads it there by a choice of its own.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz
open ForkChoiceProperty (P C rootHex rootHex8 askWords decodeHex)

namespace OptimisticProperty

/-- EthLib's two stores, and the blocks built so far, by index. -/
structure Sut (fork : Fork) where
  /-- The store of the fork choice, of which only the blocks are read here. -/
  store : Store P fork
  /-- The optimistic store. -/
  optimistic : OptimisticStore P fork
  /-- Each block built, and its root. -/
  built : Array (Root × BeaconBlock P fork)

/-- The state of a scenario: what a generator reads, and the stores once they are set up. -/
structure Frame (fork : Fork) where
  /-- The number of blocks built so far, the anchor included. -/
  count : Nat := 1
  /-- The slot of the clock. -/
  clock : Nat := 0
  /-- The stores, absent before the setup. -/
  sut : Option (Sut fork) := none
  deriving Inhabited

/-- The oracle and the name of the fork in consensus-specs. -/
structure Node (fork : Fork) where
  /-- The oracle. -/
  oracle : Oracle
  /-- The name of the fork. -/
  forkName : String
  /-- Whether the run is long enough to ask for the minimums of coverage. -/
  long : Bool

/-- The head of the model: the deepest block that the fork choice holds. -/
def headOf {fork : Fork} (sut : Sut fork) : Root :=
  let held := sut.built.filter fun (root, _) => sut.store.blocks.contains root
  let better (a b : Root × BeaconBlock P fork) : Bool :=
    a.2.slot > b.2.slot || (a.2.slot == b.2.slot && rootHex a.1 > rootHex b.1)
  let best := held.foldl (fun (best : Option (Root × BeaconBlock P fork)) next =>
    match best with
    | some found => if better next found then some next else best
    | none => some next) none
  (best.map (·.1)).getD (Vector.replicate 32 0)

/-- What the oracle writes of its own stores. -/
def view {fork : Fork} (sut : Sut fork) : String :=
  let sorted (roots : List Root) : List String :=
    ((roots.map rootHex).toArray.qsort (· < ·)).toList.map fun text =>
      String.ofList (text.toList.take 8)
  let held := (sut.built.toList.map (·.1)).filter sut.store.blocks.contains
  let heldSorted := (held.toArray.qsort fun a b => rootHex a < rootHex b).toList
  let ancestors := heldSorted.map fun root =>
    match sut.optimistic.latestVerifiedAncestor ⟨root, .pending⟩ with
    | .ok found => s!"{rootHex8 root}:{rootHex8 found}"
    | .error _ => s!"{rootHex8 root}:e"
  let head := sut.optimistic.head.root
  let optimistic := match sut.optimistic.isHeadOptimistic with
    | .ok true => "t"
    | .ok false => "f"
    | .error _ => "e"
  " ".intercalate [
    "o=" ++ ",".intercalate (sorted sut.optimistic.optimisticRoots),
    "k=" ++ ",".intercalate (sorted held),
    "a=" ++ ",".intercalate ancestors,
    s!"h={rootHex8 head}:{optimistic}"]

/-- The stores with the head of the model, compared with the view of the oracle. -/
def settle {fork : Fork} (frame : Frame fork) (sut : Sut fork) (expected : String) :
    TestT IO (Frame fork) := do
  let sut := { sut with optimistic := { sut.optimistic with head := ⟨headOf sut, .pending⟩ } }
  view sut === expected
  pure { frame with sut := some sut }

/-- The stores of a frame, which the setup made. -/
def stores {fork : Fork} (frame : Frame fork) : TestT IO (Sut fork) :=
  match frame.sut with
  | some sut => pure sut
  | none => failWith "the scenario was not set up"

/-- The stores from the anchor that the oracle builds. -/
def setup {fork : Fork} (node : Node fork) (frame : Frame fork) : TestT IO (Frame fork) := do
  let words ← evalIO (askWords node.oracle ["po_init", node.forkName])
  let [stateHex, blockHex, expected] := words | failWith "po_init: a malformed answer"
  match decodeHex (BeaconState P fork) stateHex, decodeHex (BeaconBlock P fork) blockHex with
  | .ok state, .ok block =>
    match getForkchoiceStore (C fork) state block, SszType.hashTreeRoot block with
    | .ok store, .ok root =>
      let optimistic : OptimisticStore P fork :=
        { optimisticRoots := [], head := ⟨root, .pending⟩, blocks := store.blocks }
      settle frame { store, optimistic, built := #[(root, block)] } expected
    | _, _ => failWith "the anchor is refused"
  | _, _ => failWith "EthLib does not read the anchor"

/-- Import a block on a parent, optimistically or with its payload already valid. -/
structure Import (fork : Fork) where
  /-- The index of the parent. -/
  parent : Nat
  /-- The empty slots between the parent and the block. -/
  gap : Nat
  /-- Whether the block carries a payload. -/
  payload : Bool
  /-- Whether the import is optimistic. -/
  optimistic : Bool
  deriving Repr

instance {fork : Fork} : Command (Import fork) (Frame fork) (Node fork) IO where
  -- A shrink may remove the import of the parent, and the command is then skipped.
  check _ c frame := c.parent < frame.count
  apply node c frame := do
    let sut ← stores frame
    let words ← evalIO (askWords node.oracle ["po_import", toString c.parent, toString c.gap,
      if c.payload then "1" else "0", toString frame.clock, if c.optimistic then "1" else "0"])
    let [blockHex, verdict, expected] := words | failWith "po_import: a malformed answer"
    let .ok block := decodeHex (BeaconBlock P fork) blockHex
      | failWith "EthLib does not read the block"
    let .ok root := SszType.hashTreeRoot block | failWith "EthLib does not hash the block"
    let candidate := sut.optimistic.isOptimisticCandidateBlock frame.clock.toUInt64 block
    let got := match candidate with
      | .ok true => "t"
      | .ok false => "f"
      | .error _ => "e"
    got === verdict
    classify "an import: a candidate by its parent's payload" (got == "t" && c.optimistic)
    classify "an import: refused, the clock is too near" (got == "f" && c.optimistic)
    let sut := { sut with built := sut.built.push (root, block) }
    let known := sut.store.blocks.contains block.parentRoot
    let frame := { frame with count := frame.count + 1 }
    if !known || (c.optimistic && got != "t") then settle frame sut expected
    else
      let store := { sut.store with blocks := sut.store.blocks.insert root block }
      let blocks := sut.optimistic.blocks.insert root block
      let optimistic ←
        if c.optimistic then
          pure { sut.optimistic with
            blocks, optimisticRoots := root :: sut.optimistic.optimisticRoots }
        else
          match ({ sut.optimistic with blocks }).onValidPayload root with
          | .ok next => pure next
          | .error e => failWith s!"EthLib refuses a valid payload: {e}"
      settle frame { sut with store, optimistic } expected
  label c := s!"IMPORT(on {c.parent}, gap {c.gap}, payload {c.payload}, optimistic {c.optimistic})"
  build _ := pure ⟨0, 0, true, true⟩
  next _ _ frame := { frame with count := frame.count + 1 }
  buildIn _ frame := do
    let parent ← Gen.frequency [(4, pure (frame.count - 1)),
      (2, Gen.nat (.constant 0 (frame.count - 1)))]
    let gap ← Gen.frequency [(6, pure 0), (1, Gen.nat (.linear 0 3))]
    let payload ← Gen.frequency [(5, pure true), (1, pure false)]
    -- The anchor has no payload, so a first import is optimistic only once the clock is far.
    let verified := if frame.count = 1 && frame.clock < 128 then 4 else 1
    Import.mk parent gap payload <$> Gen.frequency [(5, pure true), (verified, pure false)]

/-- The execution layer finds the payload of a block valid. -/
structure Valid (fork : Fork) where
  /-- The index of the block. -/
  index : Nat
  deriving Repr

instance {fork : Fork} : Command (Valid fork) (Frame fork) (Node fork) IO where
  check _ c frame := c.index < frame.count
  apply node c frame := do
    let sut ← stores frame
    let [_, expected] ← evalIO (askWords node.oracle ["po_valid", toString c.index])
      | failWith "po_valid: a malformed answer"
    let some (root, _) := sut.built[c.index]? | failWith "no such block"
    if !sut.store.blocks.contains root then
      label "valid: of a block that was dropped"
      settle frame sut expected
    else
      match sut.optimistic.onValidPayload root with
      | .error e => failWith s!"EthLib refuses a valid payload: {e}"
      | .ok optimistic =>
        cover (if node.long then 5 else 0) "valid: ancestors left the optimistic set"
          (optimistic.optimisticRoots.length + 1 < sut.optimistic.optimisticRoots.length)
        settle frame { sut with optimistic } expected
  label c := s!"VALID({c.index})"
  build _ := pure ⟨0⟩
  buildIn _ frame :=
    Valid.mk <$> Gen.frequency [(3, pure (frame.count - 1)),
      (2, Gen.nat (.constant 0 (frame.count - 1)))]

/-- The execution layer finds the payload of a block invalid, with a latest valid hash or none.

The kind is 0 for no hash, and a number of ancestors up for the hash of that ancestor.

It is 100 for the hash of the block itself, 101 for a hash of no block, 102 for the zero hash. -/
structure Invalid (fork : Fork) where
  /-- The index of the block. -/
  index : Nat
  /-- The kind of the latest valid hash. -/
  kind : Nat
  deriving Repr

instance {fork : Fork} : Command (Invalid fork) (Frame fork) (Node fork) IO where
  -- The anchor is never invalid: a node starts from a block that it trusts.
  check _ c frame := 0 < c.index && c.index < frame.count
  apply node c frame := do
    let sut ← stores frame
    let words ← evalIO (askWords node.oracle ["po_invalid", toString c.index, toString c.kind])
    let [blockHex, hashText, expected] := words | failWith "po_invalid: a malformed answer"
    let .ok block := decodeHex (BeaconBlock P fork) blockHex
      | failWith "EthLib does not read the block"
    let latest : Option Hash32 :=
      if hashText == "-" then none
      else (unhex? hashText).map fun bytes => Vector.ofFn fun i : Fin 32 => bytes[i.val]!
    match sut.store.onInvalidPayload block latest with
    | .error e => failWith s!"EthLib refuses an invalid payload: {e}"
    | .ok store =>
      let dropped := sut.built.filter fun (root, _) =>
        sut.store.blocks.contains root && !store.blocks.contains root
      -- The first invalid block is the one of the dropped blocks that the others descend from.
      let first := dropped.foldl (fun (best : Option (Root × BeaconBlock P fork)) next =>
        match best with
        | some found => if next.2.slot < found.2.slot then some next else best
        | none => some next) none
      let before := headOf sut
      let optimistic ← match first with
        | none => pure sut.optimistic
        | some (root, _) =>
          match sut.optimistic.onInvalidatedPayload root with
          | .ok next => pure next
          | .error e => failWith s!"EthLib refuses the first invalid block: {e}"
      let after : Sut fork := { sut with store, optimistic }
      cover (if node.long then 10 else 0) "invalid: a branch was invalidated" (dropped.size > 1)
      cover (if node.long then 5 else 0) "invalid: the head moved back" (headOf after != before)
      classify "invalid: nothing dropped" dropped.isEmpty
      settle frame after expected
  label c := s!"INVALID({c.index}, hash {c.kind})"
  build _ := pure ⟨0, 0⟩
  buildIn _ frame := do
    let index ← Gen.frequency [(3, Gen.nat (.constant 0 (frame.count - 1))),
      (2, pure (frame.count - 1))]
    Invalid.mk index <$> Gen.frequency [(2, pure 0), (5, Gen.nat (.linear 1 6)),
      (1, Gen.element [100, 101, 102])]

/-- Move the clock, past the slots that make an import safe without a payload on the parent. -/
structure Tick (fork : Fork) where
  /-- The slots to add. -/
  slots : Nat
  deriving Repr

instance {fork : Fork} : Command (Tick fork) (Frame fork) (Node fork) IO where
  apply _ c frame := pure { frame with clock := frame.clock + c.slots }
  label c := s!"TICK({c.slots})"
  build _ := Tick.mk <$> Gen.element [1, 2, 127, 128, 129, 300]
  next _ c frame := { frame with clock := frame.clock + c.slots }

/-- The optimistic store of EthLib follows consensus-specs and the guide on every sequence. -/
def madhouse (fork : Fork) (forkName : String) (oracle : Oracle) (long : Bool := true) :
    Property IO :=
  let node : Node fork := ⟨oracle, forkName, long⟩
  scenario (σ := Frame fork) .madhouse node [
    Command.gen (Import fork), Command.gen (Import fork), Command.gen (Import fork),
    Command.gen (Import fork), Command.gen (Valid fork), Command.gen (Valid fork),
    Command.gen (Invalid fork), Command.gen (Tick fork)] (.linear 1 120) (setup node)

end OptimisticProperty

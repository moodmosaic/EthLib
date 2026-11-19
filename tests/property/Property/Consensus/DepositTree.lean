import Hedgehog
import Support
import EthLib.Consensus.DepositTree

/-!
# The deposit tree of EIP-4881, as a state machine

The model is the list of the leaves, the count of finalized deposits and whether a finalization
recorded a block.
The oracle computes the deposit root of a list of leaves with a naive Merkle tree of depth 32
and checks a branch as `is_valid_merkle_branch` does.

After every transition the sparse tree must have the root of the model, prove exactly the
deposits that are not finalized, and give a snapshot of the finalized ones.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ConsensusProperty

/-- The model of a deposit tree. -/
structure TreeModel where
  /-- The leaves, each named by a number. -/
  leaves : List Nat
  /-- The count of finalized deposits. -/
  finalized : Nat
  /-- Whether a finalization has recorded a block. -/
  hasBlock : Bool
  /-- Whether the last transition was one that the tree must accept. -/
  accepted : Bool
  deriving Repr

/-- The operations on a deposit tree. -/
inductive TreeStep where
  /-- One more deposit. -/
  | push (leaf : Nat)
  /-- Finalize a count of deposits, with their root or with a wrong one. -/
  | finalize (count : Nat) (rightRoot : Bool) (height : Nat)
  /-- Take a snapshot, write it, read it back and rebuild the tree from it. -/
  | restore
  /-- Ask for the proof of a deposit. -/
  | prove (index : Nat)
  deriving Repr, BEq

/-- The leaf of a number: 32 bytes that differ for different numbers. -/
def leafOf (n : Nat) : Root :=
  Vector.ofFn fun i => if i.val = 0 then UInt8.ofNat (n / 256) else UInt8.ofNat (n + i.val)

/-- Whether a finalization is one that the tree must accept. -/
def finalizeValid (s : TreeModel) (count : Nat) (rightRoot : Bool) : Bool :=
  rightRoot && count ≤ s.leaves.length && s.finalized ≤ count

/-- The model. -/
def treeModel : Model TreeModel TreeStep where
  initState := pure ⟨[], 0, false, true⟩
  transitions s := Gen.frequency [
    (6, TreeStep.push <$> Gen.nat (.linear 0 5000)),
    (3, do
      -- Mostly a valid count: between the finalized deposits and all of them.
      let count ← Gen.frequency [
        (6, Gen.nat (.constant s.finalized (max s.finalized s.leaves.length))),
        (2, Gen.nat (.linear 0 (s.leaves.length + 2)))]
      let rightRoot ← Gen.frequency [(6, pure true), (1, pure false)]
      let height ← Gen.nat (.linear 0 1000)
      pure (.finalize count rightRoot height)),
    (1, pure .restore),
    (3, TreeStep.prove <$> Gen.nat (.linear 0 (s.leaves.length + 1)))]
  apply s
    | .push leaf => { s with leaves := s.leaves ++ [leaf], accepted := true }
    | .finalize count rightRoot _ =>
      if finalizeValid s count rightRoot then
        { s with finalized := count, hasBlock := true, accepted := true }
      else { s with accepted := false }
    | .restore =>
      if s.hasBlock then { s with leaves := s.leaves.take s.finalized, accepted := true }
      else { s with accepted := false }
    | .prove index => { s with accepted := s.finalized ≤ index && index < s.leaves.length }

/-- The deposit root of leaves, by the oracle. -/
def modelRoot (oracle : Oracle) (leaves : List Nat) : TestT IO String :=
  oracle.ask (["pure", "deposit_root"] ++ leaves.map fun n => hex ⟨(leafOf n).toArray⟩)

/-- Hexadecimal of a root. -/
def rootHex (root : Root) : String := hex ⟨root.toArray⟩

/-- The number of bits set in a number. -/
def popCount (n : Nat) : Nat := (List.range 64).countP n.testBit

/-- The state machine: the sparse tree against the list of leaves. -/
def treeMachine (oracle : Oracle) : StateMachine TreeModel TreeStep DepositTree IO where
  toModel := treeModel
  initSut _ := pure DepositTree.new
  applySut tree s step := do
    match step with
    | .push leaf =>
      match tree.pushLeaf (leafOf leaf) with
      | .ok next => pure next
      | .error e => failWith s!"a push is refused: {e}"
    | .finalize count rightRoot height =>
      -- The root of the first `count` leaves, or of nothing where there are too few.
      let wanted ← modelRoot oracle (s.leaves.take count)
      let some rootBytes := unhex? wanted | failWith "the oracle sent no root"
      let root : Root := Vector.ofFn fun i =>
        if rightRoot then rootBytes[i.val]! else rootBytes[i.val]! ^^^ 1
      let data : Eth1Data := ⟨root, UInt64.ofNat count, leafOf height⟩
      match tree.finalize data (UInt64.ofNat height) with
      | .ok next =>
        ensure s.accepted s!"a finalization that must be refused is accepted"
        pure next
      | .error e =>
        ensure (!s.accepted) s!"a valid finalization is refused: {e}"
        pure tree
    | .restore =>
      match tree.getSnapshot with
      | .error e =>
        ensure (!s.accepted) s!"a finalized tree gives no snapshot: {e}"
        pure tree
      | .ok snapshot =>
        ensure s.accepted "a tree that was never finalized gives a snapshot"
        -- The snapshot travels as SSZ, so it is rebuilt from its bytes.
        match SszType.serialize snapshot with
        | .error _ => failWith "the snapshot does not serialize"
        | .ok bytes =>
          match SszType.deserialize DepositTreeSnapshot bytes with
          | .error _ => failWith "the snapshot does not read back"
          | .ok read =>
            ensure (read == snapshot) "the snapshot read back differs"
            match DepositTree.fromSnapshot read with
            | .ok next => pure next
            | .error e => failWith s!"the tree's own snapshot is refused: {e}"
    | .prove index =>
      match tree.getProof index with
      | .error e =>
        ensure (!s.accepted) s!"no proof of deposit {index}: {e}"
        pure tree
      | .ok (leaf, branch) =>
        ensure s.accepted s!"a proof of deposit {index}, which is finalized or absent"
        leaf === leafOf (s.leaves.getD index 0)
        let flat := branch.toArray.foldl (fun acc node => acc ++ ⟨node.toArray⟩) ByteArray.empty
        let ok ← oracle.ask ["pure", "deposit_proof", rootHex leaf, toString index,
          rootHex tree.getRoot, hex flat]
        ok === "true"
        pure tree
  invariants tree s := do
    rootHex tree.getRoot === (← modelRoot oracle s.leaves)
    tree.mixInLength === s.leaves.length
    tree.tree.getFinalized.2 === s.finalized
    match tree.getSnapshot with
    | .error _ => ensure (!s.hasBlock) "a finalized tree gives no snapshot"
    | .ok snapshot =>
      ensure s.hasBlock "a tree that was never finalized gives a snapshot"
      snapshot.depositCount.toNat === s.finalized
      snapshot.finalized.data.size === popCount s.finalized
      rootHex snapshot.depositRoot === (← modelRoot oracle (s.leaves.take s.finalized))

/-- The deposit tree agrees with a list of leaves on every sequence of operations. -/
def depositTree (oracle : Oracle) : Property IO := (treeMachine oracle).property (.linear 1 60)

end ConsensusProperty

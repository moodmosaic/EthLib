import Hedgehog
import Support
import EthLib.Consensus.LightClient.Sync
import EthLib.Consensus.DataAvailability.Custody
import EthLib.Consensus.Gossip.Topics
import EthLib.Consensus.WeakSubjectivity

/-!
# Pure helpers, against the pyspec

The order of light client updates, the custody groups of PeerDAS and the subnet computations.

Each runs on inputs at its edges, against `oracle/forkchoice_helpers.py`.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace HelpersProperty

/-- The preset of every property here. -/
abbrev P : Preset := Preset.minimal

/-- The configuration of every property here. -/
abbrev C : Consensus.Config := Consensus.Config.minimal

/-! ## `is_better_update` -/

/-- What `is_better_update` reads of an update. -/
structure UpdateShape where
  /-- The number of members of the sync committee that signed. -/
  signers : Nat
  /-- Whether the branch of the next sync committee is not zero. -/
  committee : Bool
  /-- Whether the finality branch is not zero. -/
  finality : Bool
  attestedSlot : Nat
  finalizedSlot : Nat
  signatureSlot : Nat
  deriving Repr, BEq

/-- A slot at the edges of the sync committee periods of the minimal preset, 64 slots each. -/
def genSlot : Gen Nat :=
  Gen.frequency [(5, Gen.element [0, 1, 63, 64, 65, 127, 128, 129]), (2, Gen.nat (.linear 0 200))]

/-- An update shape: the signers at the two thirds of the 32 members, the slots at period edges. -/
def genShape : Gen UpdateShape := do
  let signers ← Gen.frequency [(5, Gen.element [21, 22, 20, 0, 1, 32, 31]),
    (2, Gen.nat (.constant 0 32))]
  let (committee, finality) ← Gen.zip Gen.bool Gen.bool
  let (attestedSlot, finalizedSlot) ← Gen.zip genSlot genSlot
  pure { signers, committee, finality, attestedSlot, finalizedSlot, signatureSlot := ← genSlot }

/-- A branch that is zero, or not. -/
def branch (n : Nat) (present : Bool) : Vector Bytes32 n :=
  Vector.replicate n (Vector.replicate 32 (if present then 1 else 0))

/-- A header at a slot, zero elsewhere. -/
def headerAt (fork : Fork) (slot : Nat) : LightClientHeader P fork :=
  let empty := LightClientHeader.empty P fork
  { empty with beacon := { empty.beacon with slot := UInt64.ofNat slot } }

/-- The update of a shape at a fork. -/
def UpdateShape.update (fork : Fork) (shape : UpdateShape) : LightClientUpdate P fork where
  attestedHeader := headerAt fork shape.attestedSlot
  nextSyncCommittee := SyncCommittee.empty P
  nextSyncCommitteeBranch := branch _ shape.committee
  finalizedHeader := headerAt fork shape.finalizedSlot
  finalityBranch := branch _ shape.finality
  syncAggregate := ⟨⟨Vector.ofFn fun i => decide (i.val < shape.signers)⟩, Vector.replicate 96 0⟩
  signatureSlot := UInt64.ofNat shape.signatureSlot

/-- A second shape: the first with a few fields drawn again, so that the later tie-breaks run. -/
def genPair : Gen (UpdateShape × UpdateShape) := do
  let first ← genShape
  let other ← genShape
  let second ← Gen.element [other,
    { first with signers := other.signers },
    { first with attestedSlot := other.attestedSlot },
    { first with signatureSlot := other.signatureSlot },
    { first with finalizedSlot := other.finalizedSlot },
    { first with committee := other.committee, finality := other.finality },
    first]
  pure (first, second)

/-- `isBetterUpdate` is the `is_better_update` of the pyspec. -/
def betterUpdate (fork : Fork) (name : String) (oracle : Oracle) : Property IO := propertyM do
  let (new, old) ← forAll genPair
  pure do
    let encode (shape : UpdateShape) : TestT IO String :=
      match SszType.serialize (shape.update fork) with
      | .ok bytes => pure (hex bytes)
      | .error e => failWith s!"SSZ: {reprStr e}"
    let expected ← oracle.ask ["lc_better", name, ← encode new, ← encode old]
    toString (isBetterUpdate (new.update fork) (old.update fork)) === expected

/-- `isBetterUpdate` is a strict order on updates that differ in what it reads. -/
def betterOrder : Property IO := pureIO do
  let (a, b) ← forAll genPair
  let c ← forAll genShape
  let better (x y : UpdateShape) : Bool :=
    isBetterUpdate (x.update .pectra) (y.update .pectra)
  ensure (!better a a) "an update is better than itself"
  ensure (!(better a b && better b a)) "two updates are each better than the other"
  ensure (!(better a b && better b c) || better a c) "the order is not transitive"
  -- Incomparability is transitive too: the order is a strict weak order.
  let same (x y : UpdateShape) : Bool := !better x y && !better y x
  ensure (!(same a b && same b c) || same a c) "incomparable updates are not a class"

/-! ## Custody groups -/

/-- A node ID: the ends of the range, where the search wraps, and any other. -/
def genNodeId : Gen Nat :=
  Gen.frequency [(2, (2 ^ 256 - 1 - ·) <$> Gen.nat (.linear 0 130)), (1, Gen.nat (.linear 0 5)),
    (2, genNatBits 256)]

/-- A custody group count: none, one, all, one more, and any. -/
def genCount : Gen Nat :=
  Gen.frequency [(4, Gen.element [0, 1, 4, 127, 128, 129, 2 ^ 64 - 1]),
    (3, Gen.nat (.constant 0 128))]

/-- A list of numbers as the oracle writes one. -/
def numbers (values : List UInt64) : String :=
  if values.isEmpty then "-" else ",".intercalate (values.map toString)

/-- `getCustodyGroups` is `get_custody_groups`, and refuses a count above the number of groups. -/
def custodyGroups (oracle : Oracle) : Property IO := propertyM do
  let (nodeId, count) ← forAll (Gen.zip genNodeId genCount)
  pure do
    let expected ← oracle.ask ["custody", toString nodeId, toString count]
    -- The fuel is far above what the search takes: a refusal here is of the count.
    match DataAvailability.getCustodyGroups C (BitVec.ofNat 256 nodeId) (UInt64.ofNat count)
        100000 with
    | .ok groups => numbers groups === expected
    | .error _ => expected === "error AssertionError"

/-- `computeColumnsForCustodyGroup` is `compute_columns_for_custody_group`. -/
def custodyColumns (oracle : Oracle) : Property IO := propertyM do
  let group ← forAll (Gen.frequency [(1, Gen.element [0, 127, 128, 2 ^ 64 - 1]),
    (2, Gen.nat (.constant 0 130))])
  pure do
    let expected ← oracle.ask ["columns", toString group]
    match DataAvailability.computeColumnsForCustodyGroup C P (UInt64.ofNat group) with
    | .ok columns => numbers columns === expected
    | .error _ => expected === "error AssertionError"

/-! ## Subnets -/

/-- `computeSubnetForAttestation` is `compute_subnet_for_attestation`, overflow included. -/
def attestationSubnet (oracle : Oracle) : Property IO := propertyM do
  let perSlot ← forAll (Gen.frequency [(4, Gen.nat (.constant 0 64)), (1, genNatBits 64)])
  let slot ← forAll (Gen.frequency [(4, Gen.nat (.linear 0 100)), (1, genNatBits 64)])
  let index ← forAll (Gen.frequency [(4, Gen.nat (.constant 0 64)), (1, genNatBits 64)])
  pure do
    let expected ← oracle.ask ["att_subnet", toString perSlot, toString slot, toString index]
    match computeSubnetForAttestation P C (UInt64.ofNat perSlot) (UInt64.ofNat slot)
        (UInt64.ofNat index) with
    | .ok subnet => toString subnet === expected
    | .error _ => ensure (expected.startsWith "error") s!"EthLib refuses, the pyspec: {expected}"

/-- `computeSubnetForDataColumnSidecar` is `compute_subnet_for_data_column_sidecar`. -/
def columnSubnet (oracle : Oracle) : Property IO := propertyM do
  let column ← forAll (genNatBits 64)
  pure do
    let expected ← oracle.ask ["col_subnet", toString column]
    match computeSubnetForDataColumnSidecar C (UInt64.ofNat column) with
    | .ok subnet => toString subnet === expected
    | .error _ => failWith "EthLib refuses a column"

/-- `computeSubscribedSubnets` is `compute_subscribed_subnets`. -/
def subscribedSubnets (oracle : Oracle) : Property IO := propertyM do
  let nodeId ← forAll genNodeId
  let epoch ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 1000)), (1, genNatBits 64)])
  pure do
    let expected ← oracle.ask ["subscribed", toString nodeId, toString epoch]
    match computeSubscribedSubnets P C (BitVec.ofNat 256 nodeId) (UInt64.ofNat epoch) with
    | .ok subnets => numbers subnets === expected
    | .error _ => ensure (expected.startsWith "error") s!"EthLib refuses, the pyspec: {expected}"

/-! ## The weak subjectivity period -/

/-- The epochs of the phase 0 period, from the text of `weak-subjectivity.md`, in `Nat`.

It is none where the text divides by zero or subtracts below zero. -/
def phase0Epochs (N t T delta Delta : Nat) : Option Nat :=
  let D := 10
  if T * (200 + 3 * D) < t * (200 + 12 * D) then
    if delta = 0 ∨ Delta = 0 then none
    else some (max (N * (t * (200 + 12 * D) - T * (200 + 3 * D)) / (600 * delta * (2 * t + T)))
      (N * (200 + 3 * D) / (600 * Delta)))
  else if Delta = 0 ∨ T ≤ t then none
  else some (3 * N * D * t / (200 * Delta * (T - t)))

/-- `phase0PeriodEpochs` is the formula of the text wherever it answers.

It answers for every validator set that a chain can hold: up to 2^22 validators of 2048 ETH. -/
def weakSubjectivityPhase0 : Property IO := pureIO do
  let wide ← forAll Gen.bool
  let size : Gen Nat := if wide then genNatBits 64 else Gen.nat (.exponential 0 (2 ^ 22))
  let balance : Gen Nat := if wide then genNatBits 64 else Gen.nat (.linear 0 2048)
  let (N, t) ← forAll (Gen.zip size balance)
  let T ← forAll (Gen.frequency [(2, pure 32), (1, pure t), (1, pure 2048), (1, balance)])
  let (delta, Delta) ← forAll (Gen.zip (Gen.frequency [(1, pure 0), (4, Gen.nat (.linear 1 70))])
    (Gen.frequency [(1, pure 0), (4, Gen.element [128, 512])]))
  let got := phase0PeriodEpochs (.ofNat N) (.ofNat t) (.ofNat T) (.ofNat delta) (.ofNat Delta)
  match got, phase0Epochs N t T delta Delta with
  | .ok epochs, some expected => epochs.toNat === expected
  | .ok epochs, none => failWith s!"EthLib answers {epochs} where the text has no value"
  | .error _, none => pure ()
  | .error e, some expected =>
    -- Only an overflow of 64 bits may refuse a defined value, and no realistic input overflows.
    ensure wide s!"EthLib refuses ({reprStr e}) where the text gives {expected}"

/-- `balanceChurnPeriod` is the Electra formula, `delay + SAFETY_DECAY * t / (2 * delta * 100)`. -/
def weakSubjectivityElectra : Property IO := pureIO do
  let total ← forAll (Gen.frequency [(3, Gen.nat (.exponential 0 (2 ^ 60))), (1, genNatBits 64)])
  let churn ← forAll (Gen.frequency [(1, pure 0), (4, Gen.nat (.exponential 1 (2 ^ 50))),
    (1, genNatBits 64)])
  let delay ← forAll (Gen.frequency [(3, pure 256), (1, genNatBits 64)])
  let got := balanceChurnPeriod (.ofNat delay) (.ofNat total) (.ofNat churn)
  let fits := 10 * total < 2 ^ 64 ∧ 2 * churn * 100 < 2 ^ 64 ∧ churn ≠ 0 ∧
    delay + 10 * total / (2 * churn * 100) < 2 ^ 64
  match got with
  | .ok epochs =>
    ensure (churn ≠ 0) "EthLib divides by a churn of zero"
    epochs.toNat === delay + 10 * total / (2 * churn * 100)
  | .error _ => ensure (!decide fits) "EthLib refuses a period that fits in 64 bits"

end HelpersProperty

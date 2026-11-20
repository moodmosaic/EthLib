import Property.Protocols.Transition
import EthLib.Consensus.HonestValidator
import EthLib.Consensus.HonestProposer
import EthLib.Consensus.InclusionListCommittee
import EthLib.Consensus.WeakSubjectivity
import EthLib.Consensus.Gossip.Attestation
import EthLib.Consensus.Gossip.SyncCommittee
import EthLib.Consensus.Transition.ForkBoundary

/-!
# The duties of a validator, at any preset

These are the functions of `validator.md` that take a state.

They are the committee of a validator, the aggregator selection and the sync committee duties.

The committees of Gloas and Heze are here too.

The earlier rounds compared five committee assignments at the minimal preset, and no other duty.

At the minimal preset the aggregator modulo is 1, so every proof selects.

Here the presets give committees of other sizes, and a configuration its own churn.

So the weak subjectivity period varies with the case, as it did not on the earlier registries.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ProtocolsProperty

/-- A refusal of a duty is shown by its code, since the error has no `Repr`. -/
instance : Repr ValidatorDutyError := ⟨fun e _ => s!"a duty error of code {e.code}"⟩

/-- A refusal of a proposer's helper is shown by its code, since the error has no `Repr`. -/
instance : Repr ProposerError := ⟨fun e _ => s!"a proposer error of code {e.code}"⟩

/-- An optional slot in the text form of the oracle. -/
def showOptional (slot : Option Consensus.Slot) : String :=
  match slot with
  | some slot => toString slot.toNat
  | none => "None"

/-- A proof of selection: 96 bytes from a seed, so that some select and some do not. -/
def genProof : Gen String :=
  (fun seed => hex (Cryptography.Hash.sha256 (toString seed).toUTF8 ++
    ⟨Array.replicate 64 (UInt8.ofNat seed)⟩)) <$> Gen.nat (.linear 0 255)

/-- The bytes of a proof word as a signature. -/
def proofOf (word : String) : Cryptography.Bls.BLSSignature :=
  let bytes := (unhex? word).getD ByteArray.empty
  Vector.ofFn fun i : Fin 96 => bytes[i.val]!

/-- A validator of a registry, or one past it. -/
def genMember (shape : Shape) : Gen String :=
  num (Gen.frequency [(8, Gen.nat (.linear 0 (max shape.crowd 24))), (1, genIndex)])

/-- The duties of a validator, and the committees that Gloas and Heze add. -/
def duties (world : World) (checks : SignatureChecks) : List (Call world.preset) :=
  let shape := world.shape
  let config := world.config
  let slotsPerEpoch := world.preset.SLOTS_PER_EPOCH
  let genOffset := num (Gen.nat (.constant 0 (shape.slots - 1)))
  [numbered "get_committee_assignment" allForks
      [Gen.frequency [(8, genNear), (1, genAccessorEpoch shape)], genMember shape] fun _ s f =>
      match f with
      | [epoch, validator] =>
        .ofValue (fun found => match found with
          | some (committee, index, slot) =>
            s!"[{showNumbers committee.toList},{index.toNat},{slot.toNat}]"
          | none => "None") (getCommitteeAssignment s epoch validator)
      | _ => badArity,
    numbered "is_proposer" allForks [genMember shape] fun _ s f =>
      match f with
      | [validator] => .ofValue showBool (isProposer s validator)
      | _ => badArity,
    plain "compute_weak_subjectivity_period" (forksFrom .pectra) fun _ s =>
      .ofValue showNumber (computeWeakSubjectivityPeriod config s),
    numbered "is_assigned_to_sync_committee" (forksFrom .altair)
      [Gen.frequency [(4, genNear), (2, genAccessorEpoch shape)], genMember shape] fun fork s f =>
      match f with
      | [epoch, validator] =>
        if h : .altair ≤ fork then
          .ofValue showBool (isAssignedToSyncCommittee s h epoch validator)
        else .absent
      | _ => badArity,
    numbered "compute_subnets_for_sync_committee" (forksFrom .altair) [genMember shape]
      fun fork s f =>
      match f with
      | [validator] =>
        if h : .altair ≤ fork then
          .ofValue showNumbers (computeSubnetsForSyncCommittee s h validator)
        else .absent
      | _ => badArity,
    numbered "get_ptc" (forksFrom .glamsterdam)
      [Gen.frequency [(8, genNear), (1, genAccessorEpoch shape)], genOffset] fun fork s f =>
      match f with
      | [epoch, offset] =>
        if h : .glamsterdam ≤ fork then
          .ofValue (fun committee => showNumbers committee.toList)
            (getPtc config s h (epoch * slotsPerEpoch + offset))
        else .absent
      | _ => badArity,
    numbered "get_ptc_assignment" (forksFrom .glamsterdam)
      [Gen.frequency [(8, genNear), (1, genAccessorEpoch shape)], genMember shape] fun fork s f =>
      match f with
      | [epoch, validator] =>
        if h : .glamsterdam ≤ fork then
          .ofValue showOptional (getPtcAssignment config s h epoch validator)
        else .absent
      | _ => badArity,
    numbered "get_upcoming_proposal_slots" (forksFrom .glamsterdam) [genMember shape]
      fun fork s f =>
      match f with
      | [validator] =>
        if h : .glamsterdam ≤ fork then
          .ofValue showNumbers (getUpcomingProposalSlots s h validator)
        else .absent
      | _ => badArity,
    numbered "get_inclusion_list_committee" (forksFrom .hegota)
      [Gen.frequency [(8, genNear), (1, genAccessorEpoch shape)], genOffset] fun _ s f =>
      match f with
      | [epoch, offset] =>
        .ofValue (fun committee => showNumbers committee.toList)
          (getInclusionListCommittee s (epoch * slotsPerEpoch + offset))
      | _ => badArity,
    numbered "get_inclusion_list_committee_assignment" (forksFrom .hegota)
      [Gen.frequency [(8, genNear), (1, genAccessorEpoch shape)], genMember shape] fun _ s f =>
      match f with
      | [epoch, validator] =>
        .ofValue showOptional (getInclusionListCommitteeAssignment s epoch validator)
      | _ => badArity,
    ⟨"is_aggregator", allForks,
      (fun numbers proof => numbers ++ [proof]) <$>
        genWord [genNear, genOffset, num (Gen.frequency [(6, Gen.nat (.linear 0 1)),
          (1, Gen.nat (.linear 0 5))])] <*> genProof,
      fun _ s words _ =>
      match firstNumbers s words with
      | [epoch, offset, index] =>
        match getBeaconCommittee s (epoch * slotsPerEpoch + offset) index with
        | .error e => .refused (toString (repr e))
        | .ok committee =>
          .value (showBool (isAggregator committee.size (proofOf (words.getD 1 ""))))
      | _ => badArity⟩,
    ⟨"is_sync_committee_aggregator", forksFrom .altair, (fun proof => [proof]) <$> genProof,
      fun _ _ words _ =>
        .value (showBool (isSyncCommitteeAggregator world.preset (proofOf (words.headD ""))))⟩,
    ⟨"get_validators_custody_requirement", forksFrom .fusaka,
      (fun xs => [",".intercalate (xs.map toString)]) <$>
        Gen.list (.linear 0 12) (Gen.nat (.linear 0 30)),
      fun _ s words _ =>
        .ofValue showNumber
          (getValidatorsCustodyRequirement config s (firstNumbers s words))⟩,
    ⟨"process_payload_attestation", forksFrom .glamsterdam,
      genWord [num (Gen.nat (.linear 0 60)),
        num (Gen.frequency [(8, pure 1), (1, pure 0), (1, pure 2), (1, pure 3)])],
      fun fork s _ bytes =>
      if h : .glamsterdam ≤ fork then
        withArgument (PayloadAttestation world.preset) bytes fun attestation =>
          .ofState (processPayloadAttestation config checks s h attestation)
      else .absent⟩]

/-- A world whose forks start within the first epochs, so that a few slots cross into one.

Two forks may start at one epoch, and a fork may start before the one it follows. -/
def genForkingWorld : Gen World := do
  let presetKey ← Gen.element ["minimal", oddTime, tiny, oddLimits]
  let epochs ← genFields (["ALTAIR", "BELLATRIX", "CAPELLA", "DENEB", "ELECTRA", "FULU", "GLOAS",
    "HEZE"].map fun name =>
      genConfigPair s!"{name}_FORK_EPOCH" (Gen.frequency [(8, Gen.nat (.constant 0 3)),
        (1, pure (2 ^ 64 - 1))]))
  pure (World.ofKeys presetKey (";".intercalate epochs))

/-- A state of the first epochs, of settled validators. -/
def genEarlyState (shape : Shape) : Gen (List String) :=
  genStateOf shape (do
      let epoch ← Gen.nat (.constant 0 2)
      let offset ← Gen.frequency [(3, pure (shape.slots - 1)),
        (2, Gen.nat (.constant 0 (shape.slots - 1)))]
      pure (epoch * shape.slots + offset))
    (Gen.list (.constant 4 20) (genSettledValidator shape))

/-- The slots of a state across the epochs at which forks start. -/
def acrossCalls (world : World) (checks : SignatureChecks) : List (Call world.preset) := [
  ⟨"process_slots_across", allForks,
    genWord [num (Gen.frequency [(2, Gen.nat (.constant 1 (world.shape.slots + 1))),
      (3, Gen.nat (.constant 1 (3 * world.shape.slots)))])],
    fun fork s words _ =>
    match firstNumbers s words with
    | [count] =>
      match processSlotsAcross world.config checks ⟨fork, s⟩ (s.slot + count) with
      | .error e => .refused (toString (repr e))
      | .ok after =>
        match SszType.hashTreeRoot after.state, SszType.serialize after.state with
        | .ok root, .ok bytes =>
          let crossed := after.fork.ctorIdx - fork.ctorIdx
          .upgraded (hexVector root) bytes
            (if crossed = 0 then "no fork crossed" else s!"forks crossed: {crossed}")
        | _, _ => .broken "EthLib cannot hash or write the state after"
    | _ => badArity⟩]

end ProtocolsProperty

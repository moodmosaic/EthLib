import Property.Consensus.Operations
import EthLib.Consensus.SyncCommittee
import EthLib.Consensus.Proposers

/-!
# Accessors, mutators and fork upgrades on a state

These are the helpers that the steps and operations are built from.

Each runs against its own function of consensus-specs.

The arguments are at and past the edges of the registry and of the epochs.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ConsensusProperty

/-- A 64-bit number in the text form of the oracle. -/
def showNumber (n : UInt64) : String := toString n.toNat

/-- A list of 64-bit numbers in the text form of the oracle. -/
def showNumbers (xs : List UInt64) : String := showList showNumber xs

/-- A call without argument. -/
def plain (name : String) (forks : List (String × Fork))
    (run : (fork : Fork) → State fork → Outcome fork) : Call :=
  ⟨name, forks, pure [], fun fork s _ _ => run fork s⟩

/-- A call whose argument is one word of numbers. -/
def numbered (name : String) (forks : List (String × Fork)) (gens : List (Gen String))
    (run : (fork : Fork) → State fork → List UInt64 → Outcome fork) : Call :=
  ⟨name, forks, genWord gens, fun fork s words _ => run fork s (firstNumbers s words)⟩

/-- The outcome when the numbers of an argument are not as many as the call takes. -/
def badArity {fork : Fork} : Outcome fork := .broken "the argument has the wrong number of numbers"

/-- The domain types that the oracle numbers. -/
def domainTypes : List DomainType :=
  [DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER, DOMAIN_RANDAO, DOMAIN_DEPOSIT,
    DOMAIN_VOLUNTARY_EXIT, DOMAIN_SELECTION_PROOF, DOMAIN_AGGREGATE_AND_PROOF]

/-- A domain type by its number. -/
def domainType (n : UInt64) : DomainType :=
  domainTypes.getD (n.toNat % domainTypes.length) DOMAIN_BEACON_PROPOSER

/-- An epoch for an accessor: around the current one, or far from it. -/
def genAccessorEpoch : Gen String :=
  Gen.frequency [(6, genNear), (1, pure "0"), (1, pure (toString far)),
    (1, (fun n => s!"c+{n}") <$> Gen.element [63, 64, 65]),
    (1, (fun n => s!"c-{n}") <$> Gen.element [7, 8, 9, 63, 64, 65])]

/-- The withdrawals that a state expects, in the text form of the oracle. -/
def showExpected (fork : Fork) (expected : ExpectedWithdrawals) : String :=
  let rows := expected.withdrawals.toList.map fun w =>
    s!"{w.index.toNat}:{w.validatorIndex.toNat}:{hex ⟨w.address.toArray⟩}:{w.amount.toNat}"
  let counts :=
    if .glamsterdam ≤ fork then
      [expected.processedBuilderWithdrawalsCount, expected.processedPartialWithdrawalsCount,
        expected.processedBuildersSweepCount]
    else if .pectra ≤ fork then [expected.processedPartialWithdrawalsCount]
    else []
  showList id rows ++ "/" ++ ",".intercalate (counts.map toString)

/-- The accessors. -/
def accessors : List Call := [
  plain "get_total_active_balance" allForks fun _ s =>
    .ofValue showNumber (getTotalActiveBalance s),
  plain "get_validator_churn_limit" allForks fun _ s =>
    .value (showNumber (getValidatorChurnLimit Config.minimal s)),
  plain "get_validator_activation_churn_limit" (forksFrom .dencun) fun _ s =>
    .value (showNumber (getValidatorActivationChurnLimit Config.minimal s)),
  plain "get_balance_churn_limit" (forksFrom .pectra) fun _ s =>
    .ofValue showNumber (getBalanceChurnLimit Config.minimal s),
  plain "get_activation_exit_churn_limit" (forksFrom .pectra) fun _ s =>
    .ofValue showNumber (getActivationExitChurnLimit Config.minimal s),
  plain "get_consolidation_churn_limit" (forksFrom .pectra) fun _ s =>
    .ofValue showNumber (getConsolidationChurnLimit Config.minimal s),
  plain "get_exit_churn_limit" (forksFrom .glamsterdam) fun _ s =>
    .ofValue showNumber (getExitChurnLimit Config.minimal s),
  plain "get_activation_churn_limit" (forksFrom .glamsterdam) fun _ s =>
    .ofValue showNumber (getActivationChurnLimit Config.minimal s),
  plain "get_beacon_proposer_index" allForks fun _ s =>
    .ofValue showNumber (getBeaconProposerIndex s),
  plain "get_finality_delay" allForks fun _ s => .ofValue showNumber (getFinalityDelay s),
  plain "is_in_inactivity_leak" allForks fun _ s => .ofValue showBool (isInInactivityLeak s),
  plain "get_eligible_validator_indices" allForks fun _ s =>
    .ofValue showNumbers (getEligibleValidatorIndices s),
  plain "get_next_sync_committee_indices" (forksFrom .altair) fun _ s =>
    .ofValue (fun v => showNumbers v.toList) (getNextSyncCommitteeIndices s),
  plain "get_next_sync_committee" (forksFrom .altair) fun _ s =>
    match getNextSyncCommittee s with
    | .error e => .refused (toString (repr e))
    | .ok committee => .ofValue hexVector (SszType.hashTreeRoot committee),
  plain "get_expected_withdrawals" (forksFrom .shapella) fun fork s =>
    if h : .shapella ≤ fork then .ofValue (showExpected fork) (getExpectedWithdrawals s h)
    else .absent,
  numbered "get_active_validator_indices" allForks [genAccessorEpoch] fun _ s f =>
    match f with
    | [epoch] => .value (showNumbers (getActiveValidatorIndices s epoch))
    | _ => badArity,
  numbered "get_committee_count_per_slot" allForks [genAccessorEpoch] fun _ s f =>
    match f with
    | [epoch] => .value (showNumber (getCommitteeCountPerSlot s epoch))
    | _ => badArity,
  numbered "get_block_root" allForks [genAccessorEpoch] fun _ s f =>
    match f with
    | [epoch] => .ofValue hexVector (getBlockRoot s epoch)
    | _ => badArity,
  numbered "get_block_root_at_slot" allForks [genAccessorEpoch, num (Gen.nat (.constant 0 7))]
    fun _ s f =>
    match f with
    | [epoch, offset] => .ofValue hexVector (getBlockRootAtSlot s (epoch * 8 + offset))
    | _ => badArity,
  numbered "get_randao_mix" allForks [genAccessorEpoch] fun _ s f =>
    match f with
    | [epoch] => .ofValue hexVector (getRandaoMix s epoch)
    | _ => badArity,
  numbered "get_beacon_committee" allForks
    [Gen.frequency [(8, genNear), (1, genAccessorEpoch)], num (Gen.nat (.constant 0 7)),
      num (Gen.frequency [(6, Gen.nat (.linear 0 1)), (1, Gen.nat (.linear 0 5))])] fun _ s f =>
    match f with
    | [epoch, offset, index] =>
      .ofValue (fun c => showNumbers c.toList) (getBeaconCommittee s (epoch * 8 + offset) index)
    | _ => badArity,
  numbered "get_pending_balance_to_withdraw" (forksFrom .pectra) [num genIndex] fun fork s f =>
    match f with
    | [index] =>
      if h : .pectra ≤ fork then .ofValue showNumber (getPendingBalanceToWithdraw s h index)
      else .absent
    | _ => badArity,
  numbered "get_base_reward" allForks [num genIndex] fun _ s f =>
    match f with
    | [index] =>
      match getTotalActiveBalance s with
      | .error e => .refused (toString (repr e))
      | .ok total => .ofValue showNumber (getBaseReward s total index)
    | _ => badArity,
  numbered "get_beacon_proposer_indices" (forksFrom .fusaka) [genAccessorEpoch] fun _ s f =>
    match f with
    | [epoch] => .ofValue (fun v => showNumbers v.toList) (getBeaconProposerIndices s epoch)
    | _ => badArity,
  numbered "get_seed" allForks [genAccessorEpoch, num (Gen.nat (.constant 0 6))] fun _ s f =>
    match f with
    | [epoch, domain] => .ofValue hexVector (getSeed s epoch (domainType domain))
    | _ => badArity,
  numbered "get_domain" allForks
    [num (Gen.nat (.constant 0 6)), Gen.frequency [(1, pure (toString far)), (3, genAccessorEpoch)]]
    fun _ s f =>
    match f with
    | [domain, epoch] =>
      -- The far future epoch stands for no epoch, which reads the current one.
      let at_ := if epoch.toNat = far then none else some epoch
      .ofValue hexVector (getDomain Config.minimal s (domainType domain) at_)
    | _ => badArity,
  ⟨"compute_proposer_index", allForks,
    (fun seed indices => [toString seed, indices]) <$> Gen.nat (.linear 0 1000) <*>
      ((fun xs => ",".intercalate (xs.map toString)) <$>
        Gen.list (.linear 0 12) (Gen.frequency [(12, Gen.nat (.linear 0 20)), (1, genIndex)])),
    fun _ s words _ =>
      let seed := Cryptography.Hash.sha256 (words.headD "").toUTF8
      let indices := (numbersOf s (words.getD 1 "")).toArray
      .ofValue showNumber
        (computeProposerIndex s indices (Vector.ofFn fun i : Fin 32 => seed[i.val]!))⟩,
  ⟨"get_attesting_indices", allForks, genAttestationWord, fun fork s _ bytes =>
    withArgument (Attestation Preset.minimal fork) bytes fun attestation =>
      .ofValue (fun xs => showNumbers (xs.mergeSort (· ≤ ·)))
        (getAttestingIndices s attestation)⟩]

/-- A balance for the churn: an increment or a few thousand, or nearly all there is. -/
def genChurnBalance : Gen Nat :=
  Gen.frequency [(4, (· * increment) <$> Gen.nat (.linear 0 300)), (2, genGwei),
    (1, Gen.element [0, 1, 64 * increment - 1, 64 * increment, 64 * increment + 1,
      2048 * increment])]

/-- The mutators that operations are built from. -/
def mutators : List Call := [
  numbered "slash_validator" allForks
    [num genIndex, Gen.frequency [(2, pure (toString far)), (1, num genIndex)]] fun _ s f =>
    match f with
    | [index, whistleblower] =>
      let reporter := if whistleblower.toNat = far then none else some whistleblower
      .ofState (slashValidator Config.minimal s index reporter)
    | _ => badArity,
  numbered "initiate_validator_exit" allForks [num genIndex] fun _ s f =>
    match f with
    | [index] => .ofState (initiateValidatorExit Config.minimal s index)
    | _ => badArity,
  numbered "compute_exit_epoch_and_update_churn" (forksFrom .pectra) [num genChurnBalance]
    fun fork s f =>
    match f with
    | [balance] =>
      if h : .pectra ≤ fork then
        .ofState ((·.1) <$> computeExitEpochAndUpdateChurn Config.minimal s h balance)
      else .absent
    | _ => badArity,
  numbered "compute_consolidation_epoch_and_update_churn" (forksFrom .pectra)
    [num genChurnBalance] fun fork s f =>
    match f with
    | [balance] =>
      if h : .pectra ≤ fork then
        .ofState ((·.1) <$> computeConsolidationEpochAndUpdateChurn Config.minimal s h balance)
      else .absent
    | _ => badArity,
  numbered "switch_to_compounding_validator" (forksFrom .pectra) [num genIndex] fun fork s f =>
    match f with
    | [index] =>
      if h : .pectra ≤ fork then .ofState (switchToCompoundingValidator s h index) else .absent
    | _ => badArity,
  numbered "queue_excess_active_balance" (forksFrom .pectra) [num genIndex] fun fork s f =>
    match f with
    | [index] =>
      if h : .pectra ≤ fork then .ofState (queueExcessActiveBalance s h index) else .absent
    | _ => badArity,
  numbered "increase_balance" allForks [num genIndex, num genGwei] fun _ s f =>
    match f with
    | [index, delta] => .ofState (increaseBalance s index delta)
    | _ => badArity,
  numbered "decrease_balance" allForks [num genIndex, num genGwei] fun _ s f =>
    match f with
    | [index, delta] => .ofState (decreaseBalance s index delta)
    | _ => badArity]

/-- The outcome of an upgrade: the root and the bytes of the state of the next fork. -/
def upgraded {fork post : Fork} {ε : Type} [Repr ε] (result : Except ε (State post)) :
    Outcome fork :=
  match result with
  | .error e => .refused (toString (repr e))
  | .ok state =>
    match SszType.hashTreeRoot state, SszType.serialize state with
    | .ok root, .ok bytes => .upgraded (hexVector root) bytes
    | _, _ => .broken "EthLib cannot hash or write the upgraded state"

/-- An upgrade from one fork, as a call at that fork alone. -/
def upgrade (name : String) (forkName : String) (fork : Fork)
    (run : State fork → Outcome fork) : Call :=
  ⟨name, [(forkName, fork)], pure [], fun at_ s _ _ =>
    if same : at_ = fork then run (same ▸ s) |> (same ▸ ·) else .absent⟩

/-- A state to upgrade: any state, or one of settled validators with its deposit contract drained.

The upgrade to Heze refuses a state that still has deposits of the contract to process. -/
def genUpgradeState : Gen (List String) :=
  Gen.frequency [(1, genState), (1, genOperationState),
    (2, (· ++ ["drsi=same"]) <$> genOperationState)]

/-- The fork upgrades. -/
def upgrades : List Call := [
  upgrade "upgrade_to_altair" "phase0" .phase0 fun s =>
    upgraded (upgradeToAltair Config.minimal s),
  upgrade "upgrade_to_bellatrix" "altair" .altair fun s =>
    upgraded (ε := TransitionError)
      (.ok (carryFields Config.minimal .bellatrix s (by decide) (by decide))),
  upgrade "upgrade_to_capella" "bellatrix" .bellatrix fun s =>
    upgraded (ε := TransitionError)
      (.ok (carryFields Config.minimal .shapella s (by decide) (by decide))),
  upgrade "upgrade_to_deneb" "capella" .shapella fun s =>
    upgraded (ε := TransitionError)
      (.ok (carryFields Config.minimal .dencun s (by decide) (by decide))),
  upgrade "upgrade_to_electra" "deneb" .dencun fun s =>
    upgraded (upgradeToElectra Config.minimal s),
  upgrade "upgrade_to_fulu" "electra" .pectra fun s => upgraded (upgradeToFulu Config.minimal s),
  upgrade "upgrade_to_gloas" "fulu" .fusaka fun s =>
    upgraded (upgradeToGloas Config.minimal checks s),
  upgrade "upgrade_to_heze" "gloas" .glamsterdam fun s =>
    upgraded (upgradeToHeze Config.minimal s)]

end ConsensusProperty

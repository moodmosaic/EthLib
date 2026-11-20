import Property.Protocols.State
import EthLib.Consensus.Transition.Upgrade
import EthLib.Consensus.PayloadTimeliness
import EthLib.Consensus.SyncCommittee
import EthLib.Consensus.Proposers

/-!
# The calls of the state transition, at any preset and configuration

These are the calls that `Property/Consensus` ran at the minimal preset with a stand-in signature.

Here each takes the world of its case: the preset, the configuration and the signature checks.

So the same call runs at mainnet, at presets that differ from both named ones, and with real BLS.

EthLib must refuse what consensus-specs refuses and reach the same state otherwise.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ProtocolsProperty

/-- A call on a state: its name in consensus-specs, its forks, its argument and EthLib's. -/
structure Call (preset : Preset) where
  /-- The name of the function in consensus-specs. -/
  name : String
  /-- The forks that have the call. -/
  forks : List (String × Fork)
  /-- The words of the argument. -/
  arguments : Gen (List String)
  /-- EthLib's function, given the state, the words and the SSZ bytes of the argument. -/
  run : (fork : Fork) → State preset fork → List String → ByteArray → Outcome preset fork

/-- The numbers of the first word of an argument. -/
def firstNumbers {preset : Preset} {fork : Fork} (state : State preset fork)
    (words : List String) : List UInt64 :=
  numbersOf state (words.headD "")

/-- One word of numbers from generators of each. -/
def genWord (gens : List (Gen String)) : Gen (List String) :=
  (fun fields => [",".intercalate fields]) <$> genFields gens

/-- A number as a word field. -/
def num (gen : Gen Nat) : Gen String := toString <$> gen

/-- A flag that is mostly set: whether a signature is valid, a root right. -/
def genOk : Gen String := num (Gen.frequency [(5, pure 1), (1, pure 0)])

/-- An epoch of an operation: mostly the current one. -/
def genOperationEpoch : Gen String :=
  Gen.frequency [(4, pure "c-0"), (2, genNear), (1, pure "0"), (1, pure (toString far))]

/-- A list of validator indices as one word, sorted or not, with or without repeats. -/
def genIndices : Gen String :=
  (fun xs => ",".intercalate (xs.map toString)) <$>
    Gen.list (.linear 0 6) (Gen.frequency [(8, Gen.nat (.linear 0 6)), (1, genIndex)])

/-- The 64-bit amounts of a request: none, a few increments, or anything. -/
def genAmount (shape : Shape) : Gen Nat :=
  Gen.frequency [(3, pure 0), (3, (· * shape.increment) <$> Gen.nat (.linear 0 5)),
    (2, genGwei shape),
    (1, Gen.nat (.linear 0 shape.increment))]

/-- The words of a deposit: key, credentials, amount, signature. -/
def genDepositFields (shape : Shape) : List (Gen String) := [
  -- With real BLS a key from 900 on is no valid public key: see `oracle/protocols_real.py`.
  num (Gen.frequency [(8, Gen.nat (.linear 0 60)), (1, Gen.nat (.constant 900 903))]),
  num (Gen.frequency [(3, pure 1), (3, pure 2), (2, pure 0), (1, Gen.element [3, 0xB0])]),
  num (Gen.nat (.linear 0 5)),
  num (Gen.frequency [(3, pure (shape.low * shape.increment)), (2, pure shape.increment),
    (2, genGwei shape),
    (1, Gen.element [0, 1, shape.high * shape.increment, (shape.high + 1) * shape.increment])]),
  num (Gen.frequency [(5, pure 1), (1, pure 0), (1, pure 2)])]

/-- The words of an attestation: how far back, which committee, and what is wrong with it. -/
def genAttestationWord (shape : Shape) : Gen (List String) :=
  let slots := shape.slots
  Gen.frequency [(1, genWord [num (Gen.nat (.linear 1 slots)),
    num (Gen.frequency [(4, pure 0), (1, pure 1)]),
    num (Gen.nat (.linear 0 60)), pure "1", pure "1", genOk, pure "1", pure "1", pure "0",
    num (Gen.nat (.constant 0 1))]),
  (1, genWord [
    num (Gen.frequency [(6, Gen.nat (.linear 1 slots)), (2, Gen.nat (.linear 0 (3 * slots))),
      (1, Gen.element [0, slots, slots + 1, 2 * slots, 2 * slots + 1, 4 * slots, 4 * slots + 1,
        8 * slots, 8 * slots + 1])]),
    num (Gen.frequency [(6, Gen.nat (.linear 0 1)), (1, Gen.nat (.linear 0 5))]),
    num (Gen.nat (.linear 0 60)),
    num (Gen.frequency [(6, pure 1), (1, pure 0), (1, pure 2)]),
    num (Gen.frequency [(6, pure 1), (1, pure 0), (1, pure 2)]),
    genOk,
    genOk,
    num (Gen.frequency [(8, pure 1), (1, pure 0), (1, pure 2)]),
    num (Gen.frequency [(6, pure 0), (2, pure 2), (1, pure 3)]),
    num (Gen.frequency [(6, pure 0), (2, pure 1), (1, pure 2)])])]

/-- The slot of the parent block, which Gloas reads for an attestation. -/
def genParentSlot (shape : Shape) : Gen (List String) :=
  (fun n => [toString n]) <$>
    Gen.frequency [(2, Gen.nat (.linear 0 (110 * shape.slots))), (1, pure 0)]

/-- The operations of a block, each with a near-valid argument. -/
def operations (world : World) (checks : SignatureChecks) : List (Call world.preset) :=
  let shape := world.shape
  [
  ⟨"process_voluntary_exit", allForks,
    genWord [num genIndex, genOperationEpoch, genOk], fun _ s _ bytes =>
    withArgument SignedVoluntaryExit bytes fun exit =>
      .ofState (processVoluntaryExit world.config checks s exit)⟩,
  ⟨"process_proposer_slashing", allForks,
    genWord [num genIndex, num (Gen.nat (.linear 0 (110 * shape.slots))),
      num (Gen.frequency [(5, pure 0), (1, pure 1)]),
      genOk, genOk, num (Gen.frequency [(8, pure 0), (1, pure 1)]),
      num (Gen.frequency [(8, pure 0), (1, pure 1)])], fun _ s _ bytes =>
    withArgument ProposerSlashing bytes fun slashing =>
      .ofState (processProposerSlashing world.config checks s slashing)⟩,
  ⟨"process_attester_slashing", allForks,
    (fun head a b => head ++ [a, b]) <$>
      genWord [num (Gen.frequency [(5, Gen.nat (.constant 0 2)), (1, Gen.nat (.constant 0 5))]),
        genOk, genOk,
        num (Gen.frequency [(5, pure 1), (1, pure 0)]),
        num (Gen.frequency [(5, pure 1), (1, pure 0)])] <*> genIndices <*>
      -- `=` stands for the indices of the first attestation.
      Gen.frequency [(2, pure "="), (1, genIndices)],
    fun fork s _ bytes =>
    withArgument (AttesterSlashing world.preset fork) bytes fun slashing =>
      .ofState (processAttesterSlashing world.config checks s slashing)⟩,
  ⟨"process_attestation", allForks,
    (· ++ ·) <$> genAttestationWord shape <*> genParentSlot shape, fun fork s words bytes =>
    withArgument (Attestation world.preset fork) bytes fun attestation =>
      let parent := (numbersOf s (words.getD 1 "0")).headD 0
      .ofState (processAttestation world.config checks s parent attestation)⟩,
  ⟨"process_bls_to_execution_change", forksFrom .shapella,
    -- A key of 9 stands for the key that the credentials of the validator commit to.
    genWord [num genIndex, num (Gen.frequency [(3, pure 9), (1, Gen.nat (.linear 0 5))]),
      num (Gen.nat (.linear 0 5)), genOk],
    fun _ s _ bytes =>
    withArgument SignedBLSToExecutionChange bytes fun change =>
      .ofState (processBlsToExecutionChange world.config checks s change)⟩,
  ⟨"process_deposit", forksBefore .fusaka,
    genWord (genDepositFields shape ++ [num (Gen.nat (.linear 1 6)), num (Gen.nat (.linear 0 6)),
      num (Gen.frequency [(5, pure 0), (1, pure 1), (1, pure 2)])]), fun fork s _ bytes =>
    if h : fork < .hegota then
      withArgument Deposit bytes fun deposit =>
        .ofState (processDeposit world.config checks h s deposit)
    else .absent⟩,
  ⟨"process_deposit_request", forksFrom .pectra,
    genWord (genDepositFields shape ++
      [num (Gen.frequency [(3, Gen.nat (.linear 0 20)), (1, pure far)])]),
    fun fork s _ bytes =>
    if h : .pectra ≤ fork then
      withArgument DepositRequest bytes fun request => .ofState (processDepositRequest s h request)
    else .absent⟩,
  ⟨"process_withdrawal_request", forksFrom .pectra,
    -- An address of 9 stands for the address of the credentials of the validator.
    genWord [num (Gen.frequency [(4, pure 9), (1, Gen.nat (.linear 0 5))]), num genIndex,
      num (genAmount shape)],
    fun fork s _ bytes =>
    if h : .pectra ≤ fork then
      withArgument WithdrawalRequest bytes fun request =>
        .ofState (processWithdrawalRequest world.config s h request)
    else .absent⟩,
  ⟨"process_consolidation_request", forksFrom .pectra,
    genWord [num (Gen.frequency [(4, pure 9), (1, Gen.nat (.linear 0 5))]), num genIndex,
      num genIndex],
    fun fork s _ bytes =>
    if h : .pectra ≤ fork then
      withArgument ConsolidationRequest bytes fun request =>
        .ofState (processConsolidationRequest world.config s h request)
    else .absent⟩,
  ⟨"process_builder_deposit_request", forksFrom .glamsterdam,
    -- A signature flag of 2 signs under the domain of builder deposits.
    genWord [num (Gen.nat (.linear 0 8)),
      num (Gen.frequency [(6, pure 0xB0), (1, Gen.element [1, 2, 0])]),
      num (Gen.nat (.linear 0 5)),
      num (Gen.frequency [(3, (· * shape.increment) <$> Gen.nat (.linear 0 5)),
        (1, genGwei shape)]),
      num (Gen.frequency [(5, pure 2), (1, pure 1), (1, pure 0)])], fun fork s _ bytes =>
    if h : .glamsterdam ≤ fork then
      withArgument BuilderDepositRequest bytes fun request =>
        .ofState (processBuilderDepositRequest world.config checks s h request)
    else .absent⟩,
  ⟨"process_builder_exit_request", forksFrom .glamsterdam,
    genWord [num (Gen.frequency [(4, pure 9), (1, Gen.nat (.linear 0 5))]),
      num (Gen.nat (.linear 0 6))],
    fun fork s _ bytes =>
    if h : .glamsterdam ≤ fork then
      withArgument BuilderExitRequest bytes fun request =>
        .ofState (processBuilderExitRequest world.config s h request)
    else .absent⟩,
  ⟨"process_execution_payload_bid", forksFrom .glamsterdam,
    -- The far future index is a self-build, which signs with the point at infinity (2).
    Gen.frequency [
      (1, genWord [pure (toString far), num (Gen.frequency [(5, pure 0), (1, pure 1)]),
        num (Gen.frequency [(5, pure 2), (1, pure 1)]), pure "0", genOk, genOk, genOk, genOk,
        num (Gen.frequency [(4, Gen.nat (.linear 0 6)), (1, Gen.element [9, 10, 4096])])]),
      (2, genWord [num (Gen.nat (.linear 0 5)),
        num (Gen.frequency [(1, pure 0), (3, (· * shape.increment) <$> Gen.nat (.linear 0 40)),
          (1, genGwei shape)]),
        num (Gen.frequency [(6, pure 1), (1, pure 0), (1, pure 2)]),
        num (Gen.frequency [(8, pure 0), (1, pure 1)]), genOk, genOk, genOk, genOk,
        num (Gen.frequency [(4, Gen.nat (.linear 0 6)), (1, Gen.element [9, 10, 4096])])])],
    fun fork s _ bytes =>
    if h : .glamsterdam ≤ fork then
      withArgument (SignedExecutionPayloadBid world.preset fork) bytes fun bid =>
        .ofState (processExecutionPayloadBid world.config checks s h bid)
    else .absent⟩,
  ⟨"process_sync_aggregate", forksFrom .altair,
    genWord [num (Gen.nat (.linear 0 60)), genOk], fun fork s _ bytes =>
    if h : .altair ≤ fork then
      withArgument (SyncAggregate world.preset) bytes fun aggregate =>
        .ofState (processSyncAggregate world.config checks s h aggregate)
    else .absent⟩,
  ⟨"process_withdrawals", forksFrom .shapella,
    genWord [num (Gen.frequency [(4, pure 0), (1, Gen.nat (.constant 1 4))])], fun fork s _ bytes =>
    if h : .shapella ≤ fork then
      if gloas : .glamsterdam ≤ fork then
        .ofState (processWithdrawals s h fun before => absurd gloas (Nat.not_le_of_lt before))
      else
        withArgument (ExecutionPayload world.preset fork) bytes fun payload =>
          .ofState (processWithdrawals s h fun _ => payload)
    else .absent⟩,
  ⟨"process_slots", allForks,
    genWord [num (Gen.frequency [(4, Gen.nat (.linear 1 (shape.slots + 1))),
      (1, Gen.nat (.linear 0 (5 * shape.slots)))])],
    fun _ s words _ =>
    match firstNumbers s words with
    | [count] => .ofState (processSlots world.config checks s (s.slot + count))
    | _ => .broken "process_slots takes one number"⟩]

/-- A block before Gloas, whole: header, payload, RANDAO, deposit vote, operations, sync aggregate.

The numbers say what is wrong with it, mostly nothing. -/
def blocks (world : World) (checks : SignatureChecks) : List (Call world.preset) :=
  let shape := world.shape
  [
  ⟨"process_block", forksBefore .glamsterdam,
    genWord [num (Gen.frequency [(9, pure 0), (1, pure 1)]),
      num (Gen.frequency [(9, pure 0), (1, pure 1)]), genOk, genOk,
      num (Gen.frequency [(6, pure 0), (1, Gen.nat (.constant 1 3))]),
      num (Gen.frequency [(4, Gen.nat (.linear 0 6)), (1, Gen.element [9, 10, 12, 13, 21, 22])]),
      num (Gen.nat (.linear 0 3)), num (Gen.nat (.linear 0 60)), genOk,
      num (Gen.frequency [(6, pure 0), (1, pure 1)])],
    fun fork s _ bytes =>
    withArgument (BeaconBlock world.preset fork) bytes fun block =>
      .ofState (processBlock world.config checks (ExecutionEngine.constant true) s block)⟩]

/-- A block from Gloas, whole.

It has the parent's payload, header, withdrawals, bid, RANDAO and deposit vote.

It also has the operations with payload attestations, and the sync aggregate.

The numbers say what is wrong with it, mostly nothing:

- The slot.
- The proposer.
- The parent root.
- The RANDAO reveal.
- The parent's payload (full, empty, full with other requests, empty with requests).
- The kind of request.
- A seed.
- The sync aggregate.
- The slot of the bid.
- The number and the kind of the payload attestations. -/
def gloasBlocks (world : World) (checks : SignatureChecks) : List (Call world.preset) :=
  let shape := world.shape
  [
  ⟨"process_block", forksFrom .glamsterdam,
    genWord [num (Gen.frequency [(9, pure 0), (1, pure 1)]),
      num (Gen.frequency [(9, pure 0), (1, pure 1)]), genOk, genOk,
      num (Gen.frequency [(4, pure 0), (4, pure 1), (1, pure 2), (1, pure 3)]),
      num (Gen.nat (.constant 0 4)), num (Gen.nat (.linear 0 60)), genOk,
      num (Gen.frequency [(9, pure 0), (1, pure 1)]),
      num (Gen.frequency [(2, pure 0), (3, pure 1), (2, pure 2), (1, Gen.element [4, 5])]),
      num (Gen.frequency [(8, pure 1), (1, pure 0), (1, pure 2), (1, pure 3)])],
    fun fork s _ bytes =>
    withArgument (BeaconBlock world.preset fork) bytes fun block =>
      .ofState (processBlock world.config checks (ExecutionEngine.constant true) s block)⟩]

/-- A 64-bit number in the text form of the oracle. -/
def showNumber (n : UInt64) : String := toString n.toNat

/-- A list of 64-bit numbers in the text form of the oracle. -/
def showNumbers (xs : List UInt64) : String := showList showNumber xs

/-- A call without argument. -/
def plain {preset : Preset} (name : String) (forks : List (String × Fork))
    (run : (fork : Fork) → State preset fork → Outcome preset fork) : Call preset :=
  ⟨name, forks, pure [], fun fork s _ _ => run fork s⟩

/-- A call whose argument is one word of numbers. -/
def numbered {preset : Preset} (name : String) (forks : List (String × Fork))
    (gens : List (Gen String))
    (run : (fork : Fork) → State preset fork → List UInt64 → Outcome preset fork) :
    Call preset :=
  ⟨name, forks, genWord gens, fun fork s words _ => run fork s (firstNumbers s words)⟩

/-- The outcome when the numbers of an argument are not as many as the call takes. -/
def badArity {preset : Preset} {fork : Fork} : Outcome preset fork :=
  .broken "the argument has the wrong number of numbers"

/-- The steps of the epoch transition. -/
def steps (world : World) (checks : SignatureChecks) : List (Call world.preset) := [
  plain "process_justification_and_finalization" (allForks) fun _ s =>
    .ofState (processJustificationAndFinalization s),
  plain "process_inactivity_updates" (forksFrom .altair) fun fork s =>
    if h : .altair ≤ fork then .ofState (processInactivityUpdates world.config s h)
    else .absent,
  plain "process_rewards_and_penalties" (allForks) fun _ s =>
    .ofState (processRewardsAndPenalties world.config s),
  plain "process_registry_updates" (allForks) fun _ s =>
    .ofState (processRegistryUpdates world.config s),
  plain "process_slashings" (allForks) fun _ s => .ofState (processSlashings s),
  plain "process_eth1_data_reset" (forksBefore .hegota) fun fork s =>
    if h : fork < .hegota then .ofState (processEth1DataReset h s) else .absent,
  plain "process_pending_deposits" (forksFrom .pectra) fun fork s =>
    if h : .pectra ≤ fork then .ofState (processPendingDeposits world.config checks s h)
    else .absent,
  plain "process_pending_consolidations" (forksFrom .pectra) fun fork s =>
    if h : .pectra ≤ fork then .ofState (processPendingConsolidations s h) else .absent,
  plain "process_builder_pending_payments" (forksFrom .glamsterdam) fun fork s =>
    if h : .glamsterdam ≤ fork then .ofState (processBuilderPendingPayments s h) else .absent,
  plain "process_effective_balance_updates" (allForks) fun _ s =>
    .ofState (processEffectiveBalanceUpdates s),
  plain "process_slashings_reset" (allForks) fun _ s => .ofState (processSlashingsReset s),
  plain "process_randao_mixes_reset" (allForks) fun _ s => .ofState (processRandaoMixesReset s),
  plain "process_historical_roots_update" (forksBefore .shapella) fun _ s =>
    .ofState (processHistoricalRootsUpdate s),
  plain "process_historical_summaries_update" (forksFrom .shapella) fun fork s =>
    if h : .shapella ≤ fork then .ofState (processHistoricalSummariesUpdate s h) else .absent,
  plain "process_participation_record_updates" (forksBefore .altair) fun _ s =>
    .ofState (processParticipationRecordUpdates s),
  plain "process_participation_flag_updates" (forksFrom .altair) fun fork s =>
    if h : .altair ≤ fork then .state (processParticipationFlagUpdates s h) else .absent,
  plain "process_sync_committee_updates" (forksFrom .altair) fun fork s =>
    if h : .altair ≤ fork then .ofState (processSyncCommitteeUpdates s h) else .absent,
  plain "process_proposer_lookahead" (forksFrom .fusaka) fun fork s =>
    if h : .fusaka ≤ fork then .ofState (processProposerLookahead s h) else .absent,
  plain "process_ptc_window" (forksFrom .glamsterdam) fun fork s =>
    if h : .glamsterdam ≤ fork then .ofState (processPtcWindow s h) else .absent,
  plain "process_epoch" (allForks) fun _ s => .ofState (processEpoch world.config checks s),
  plain "process_slot" (allForks) fun _ s => .ofState (processSlot s)]

/-- The domain types that the oracle numbers. -/
def domainTypes : List DomainType :=
  [DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER, DOMAIN_RANDAO, DOMAIN_DEPOSIT,
    DOMAIN_VOLUNTARY_EXIT, DOMAIN_SELECTION_PROOF, DOMAIN_AGGREGATE_AND_PROOF]

/-- A domain type by its number. -/
def domainType (n : UInt64) : DomainType :=
  domainTypes.getD (n.toNat % domainTypes.length) DOMAIN_BEACON_PROPOSER

/-- An epoch for an accessor: around the current one, or far from it. -/
def genAccessorEpoch (shape : Shape) : Gen String :=
  let edges := periodEdges shape
  Gen.frequency [(6, genNear), (1, pure "0"), (1, pure (toString far)),
    (1, (fun n => s!"c+{n}") <$> Gen.element edges),
    (1, (fun n => s!"c-{n}") <$> Gen.element edges)]

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
def accessors (world : World) (checks : SignatureChecks) : List (Call world.preset) :=
  let shape := world.shape
  [
  plain "get_total_active_balance" allForks fun _ s =>
    .ofValue showNumber (getTotalActiveBalance s),
  plain "get_validator_churn_limit" allForks fun _ s =>
    .value (showNumber (getValidatorChurnLimit world.config s)),
  plain "get_validator_activation_churn_limit" (forksFrom .dencun) fun _ s =>
    .value (showNumber (getValidatorActivationChurnLimit world.config s)),
  plain "get_balance_churn_limit" (forksFrom .pectra) fun _ s =>
    .ofValue showNumber (getBalanceChurnLimit world.config s),
  plain "get_activation_exit_churn_limit" (forksFrom .pectra) fun _ s =>
    .ofValue showNumber (getActivationExitChurnLimit world.config s),
  plain "get_consolidation_churn_limit" (forksFrom .pectra) fun _ s =>
    .ofValue showNumber (getConsolidationChurnLimit world.config s),
  plain "get_exit_churn_limit" (forksFrom .glamsterdam) fun _ s =>
    .ofValue showNumber (getExitChurnLimit world.config s),
  plain "get_activation_churn_limit" (forksFrom .glamsterdam) fun _ s =>
    .ofValue showNumber (getActivationChurnLimit world.config s),
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
  numbered "get_active_validator_indices" allForks [genAccessorEpoch shape] fun _ s f =>
    match f with
    | [epoch] => .value (showNumbers (getActiveValidatorIndices s epoch))
    | _ => badArity,
  numbered "get_committee_count_per_slot" allForks [genAccessorEpoch shape] fun _ s f =>
    match f with
    | [epoch] => .value (showNumber (getCommitteeCountPerSlot s epoch))
    | _ => badArity,
  numbered "get_block_root" allForks [genAccessorEpoch shape] fun _ s f =>
    match f with
    | [epoch] => .ofValue hexVector (getBlockRoot s epoch)
    | _ => badArity,
  numbered "get_block_root_at_slot" allForks
    [genAccessorEpoch shape, num (Gen.nat (.constant 0 (shape.slots - 1)))]
    fun _ s f =>
    match f with
    | [epoch, offset] =>
      .ofValue hexVector (getBlockRootAtSlot s (epoch * world.preset.SLOTS_PER_EPOCH + offset))
    | _ => badArity,
  numbered "get_randao_mix" allForks [genAccessorEpoch shape] fun _ s f =>
    match f with
    | [epoch] => .ofValue hexVector (getRandaoMix s epoch)
    | _ => badArity,
  numbered "get_beacon_committee" allForks
    [Gen.frequency [(8, genNear), (1, genAccessorEpoch shape)],
      num (Gen.nat (.constant 0 (shape.slots - 1))),
      num (Gen.frequency [(6, Gen.nat (.linear 0 1)), (1, Gen.nat (.linear 0 5))])] fun _ s f =>
    match f with
    | [epoch, offset, index] =>
      .ofValue (fun c => showNumbers c.toList)
        (getBeaconCommittee s (epoch * world.preset.SLOTS_PER_EPOCH + offset) index)
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
  numbered "get_beacon_proposer_indices" (forksFrom .fusaka) [genAccessorEpoch shape] fun _ s f =>
    match f with
    | [epoch] => .ofValue (fun v => showNumbers v.toList) (getBeaconProposerIndices s epoch)
    | _ => badArity,
  numbered "get_seed" allForks [genAccessorEpoch shape, num (Gen.nat (.constant 0 6))] fun _ s f =>
    match f with
    | [epoch, domain] => .ofValue hexVector (getSeed s epoch (domainType domain))
    | _ => badArity,
  numbered "get_domain" allForks
    [num (Gen.nat (.constant 0 6)),
      Gen.frequency [(1, pure (toString far)), (3, genAccessorEpoch shape)]]
    fun _ s f =>
    match f with
    | [domain, epoch] =>
      -- The far future epoch stands for no epoch, which reads the current one.
      let at_ := if epoch.toNat = far then none else some epoch
      .ofValue hexVector (getDomain world.config s (domainType domain) at_)
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
  ⟨"get_attesting_indices", allForks, genAttestationWord shape, fun fork s _ bytes =>
    withArgument (Attestation world.preset fork) bytes fun attestation =>
      .ofValue (fun xs => showNumbers (xs.mergeSort (· ≤ ·)))
        (getAttestingIndices s attestation)⟩]

/-- A balance for the churn: an increment or a few thousand, or nearly all there is. -/
def genChurnBalance (shape : Shape) : Gen Nat :=
  Gen.frequency [(4, (· * shape.increment) <$> Gen.nat (.linear 0 300)), (2, genGwei shape),
    (1, Gen.element [0, 1, 2 * shape.low * shape.increment - 1, 2 * shape.low * shape.increment,
      2 * shape.low * shape.increment + 1, shape.high * shape.increment])]

/-- The mutators that operations are built from. -/
def mutators (world : World) (checks : SignatureChecks) : List (Call world.preset) :=
  let shape := world.shape
  [
  numbered "slash_validator" allForks
    [num genIndex, Gen.frequency [(2, pure (toString far)), (1, num genIndex)]] fun _ s f =>
    match f with
    | [index, whistleblower] =>
      let reporter := if whistleblower.toNat = far then none else some whistleblower
      .ofState (slashValidator world.config s index reporter)
    | _ => badArity,
  numbered "initiate_validator_exit" allForks [num genIndex] fun _ s f =>
    match f with
    | [index] => .ofState (initiateValidatorExit world.config s index)
    | _ => badArity,
  numbered "compute_exit_epoch_and_update_churn" (forksFrom .pectra) [num (genChurnBalance shape)]
    fun fork s f =>
    match f with
    | [balance] =>
      if h : .pectra ≤ fork then
        .ofState ((·.1) <$> computeExitEpochAndUpdateChurn world.config s h balance)
      else .absent
    | _ => badArity,
  numbered "compute_consolidation_epoch_and_update_churn" (forksFrom .pectra)
    [num (genChurnBalance shape)] fun fork s f =>
    match f with
    | [balance] =>
      if h : .pectra ≤ fork then
        .ofState ((·.1) <$> computeConsolidationEpochAndUpdateChurn world.config s h balance)
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
  numbered "increase_balance" allForks [num genIndex, num (genGwei shape)] fun _ s f =>
    match f with
    | [index, delta] => .ofState (increaseBalance s index delta)
    | _ => badArity,
  numbered "decrease_balance" allForks [num genIndex, num (genGwei shape)] fun _ s f =>
    match f with
    | [index, delta] => .ofState (decreaseBalance s index delta)
    | _ => badArity]

/-- The outcome of an upgrade: the root and the bytes of the state of the next fork. -/
def upgraded {preset : Preset} {fork post : Fork} {ε : Type} [Repr ε]
    (result : Except ε (State preset post)) : Outcome preset fork :=
  match result with
  | .error e => .refused (toString (repr e))
  | .ok state =>
    match SszType.hashTreeRoot state, SszType.serialize state with
    | .ok root, .ok bytes => .upgraded (hexVector root) bytes
    | _, _ => .broken "EthLib cannot hash or write the upgraded state"

/-- An upgrade from one fork, as a call at that fork alone. -/
def upgrade {preset : Preset} (name : String) (forkName : String) (fork : Fork)
    (run : State preset fork → Outcome preset fork) : Call preset :=
  ⟨name, [(forkName, fork)], pure [], fun at_ s _ _ =>
    if same : at_ = fork then run (same ▸ s) |> (same ▸ ·) else .absent⟩

/-- A state to upgrade: any state, or one of settled validators with its deposit contract drained.

The upgrade to Heze refuses a state that still has deposits of the contract to process. -/
def genUpgradeState (shape : Shape) : Gen (List String) :=
  Gen.frequency [(1, genState shape), (1, genOperationState shape),
    (2, (· ++ ["drsi=same"]) <$> genOperationState shape)]

/-- The fork upgrades. -/
def upgrades (world : World) (checks : SignatureChecks) : List (Call world.preset) :=
  let shape := world.shape
  [
  upgrade "upgrade_to_altair" "phase0" .phase0 fun s =>
    upgraded (upgradeToAltair world.config s),
  upgrade "upgrade_to_bellatrix" "altair" .altair fun s =>
    upgraded (ε := TransitionError)
      (.ok (carryFields world.config .bellatrix s (by decide) (by decide))),
  upgrade "upgrade_to_capella" "bellatrix" .bellatrix fun s =>
    upgraded (ε := TransitionError)
      (.ok (carryFields world.config .shapella s (by decide) (by decide))),
  upgrade "upgrade_to_deneb" "capella" .shapella fun s =>
    upgraded (ε := TransitionError)
      (.ok (carryFields world.config .dencun s (by decide) (by decide))),
  upgrade "upgrade_to_electra" "deneb" .dencun fun s =>
    upgraded (upgradeToElectra world.config s),
  upgrade "upgrade_to_fulu" "electra" .pectra fun s => upgraded (upgradeToFulu world.config s),
  upgrade "upgrade_to_gloas" "fulu" .fusaka fun s =>
    upgraded (upgradeToGloas world.config checks s),
  upgrade "upgrade_to_heze" "gloas" .glamsterdam fun s =>
    upgraded (upgradeToHeze world.config s)]

end ProtocolsProperty

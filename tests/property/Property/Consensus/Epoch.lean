import Property.Consensus.State
import EthLib.Consensus.PayloadTimeliness

/-!
# The steps of the epoch transition, one at a time

Each step runs on a generated state at every fork that has it, against the same function of
consensus-specs.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ConsensusProperty

/-- A step of the epoch transition: its name in consensus-specs, its forks, and EthLib's. -/
structure Step where
  /-- The name of the function in consensus-specs. -/
  name : String
  /-- The forks that have the step. -/
  forks : List (String × Fork)
  /-- EthLib's function. -/
  run : (fork : Fork) → State fork → Outcome fork

/-- The steps of the epoch transition. -/
def steps : List Step := [
  ⟨"process_justification_and_finalization", allForks, fun _ s =>
    .ofState (processJustificationAndFinalization s)⟩,
  ⟨"process_inactivity_updates", forksFrom .altair, fun fork s =>
    if h : .altair ≤ fork then .ofState (processInactivityUpdates Config.minimal s h)
    else .absent⟩,
  ⟨"process_rewards_and_penalties", allForks, fun _ s =>
    .ofState (processRewardsAndPenalties Config.minimal s)⟩,
  ⟨"process_registry_updates", allForks, fun _ s =>
    .ofState (processRegistryUpdates Config.minimal s)⟩,
  ⟨"process_slashings", allForks, fun _ s => .ofState (processSlashings s)⟩,
  ⟨"process_eth1_data_reset", forksBefore .hegota, fun fork s =>
    if h : fork < .hegota then .ofState (processEth1DataReset h s) else .absent⟩,
  ⟨"process_pending_deposits", forksFrom .pectra, fun fork s =>
    if h : .pectra ≤ fork then .ofState (processPendingDeposits Config.minimal checks s h)
    else .absent⟩,
  ⟨"process_pending_consolidations", forksFrom .pectra, fun fork s =>
    if h : .pectra ≤ fork then .ofState (processPendingConsolidations s h) else .absent⟩,
  ⟨"process_builder_pending_payments", forksFrom .glamsterdam, fun fork s =>
    if h : .glamsterdam ≤ fork then .ofState (processBuilderPendingPayments s h) else .absent⟩,
  ⟨"process_effective_balance_updates", allForks, fun _ s =>
    .ofState (processEffectiveBalanceUpdates s)⟩,
  ⟨"process_slashings_reset", allForks, fun _ s => .ofState (processSlashingsReset s)⟩,
  ⟨"process_randao_mixes_reset", allForks, fun _ s => .ofState (processRandaoMixesReset s)⟩,
  ⟨"process_historical_roots_update", forksBefore .shapella, fun _ s =>
    .ofState (processHistoricalRootsUpdate s)⟩,
  ⟨"process_historical_summaries_update", forksFrom .shapella, fun fork s =>
    if h : .shapella ≤ fork then .ofState (processHistoricalSummariesUpdate s h) else .absent⟩,
  ⟨"process_participation_record_updates", forksBefore .altair, fun _ s =>
    .ofState (processParticipationRecordUpdates s)⟩,
  ⟨"process_participation_flag_updates", forksFrom .altair, fun fork s =>
    if h : .altair ≤ fork then .state (processParticipationFlagUpdates s h) else .absent⟩,
  ⟨"process_sync_committee_updates", forksFrom .altair, fun fork s =>
    if h : .altair ≤ fork then .ofState (processSyncCommitteeUpdates s h) else .absent⟩,
  ⟨"process_proposer_lookahead", forksFrom .fusaka, fun fork s =>
    if h : .fusaka ≤ fork then .ofState (processProposerLookahead s h) else .absent⟩,
  ⟨"process_ptc_window", forksFrom .glamsterdam, fun fork s =>
    if h : .glamsterdam ≤ fork then .ofState (processPtcWindow s h) else .absent⟩,
  ⟨"process_epoch", allForks, fun _ s => .ofState (processEpoch Config.minimal checks s)⟩,
  ⟨"process_slot", allForks, fun _ s => .ofState (processSlot s)⟩]

/-- The properties of the steps: each agrees with consensus-specs at each of its forks.

`genWords` describes the states, and `suffix` tells the properties of one kind of state apart. -/
def stepProperties (oracle : Oracle) (cases : Nat) (genWords : Gen (List String) := genState)
    (suffix : String := "") : List (String × Property IO) :=
  steps.map fun step =>
    (step.name ++ suffix, (agrees oracle step.forks step.name genWords fun fork s _ _ =>
      step.run fork s).withTests cases)

end ConsensusProperty

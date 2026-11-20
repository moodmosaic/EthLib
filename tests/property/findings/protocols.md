# Protocols: the consensus layer that the earlier rounds did not run

The driver is `Property/Protocols.lean`, with its modules under `Property/Protocols/`.
The oracle is `oracle/protocols.py`, with the modules `oracle/protocols_*.py` that it names.
The reference is the executable consensus-specs (`eth_consensus_specs`) at the commit that `tests/sources.toml` pins, as `oracle/requirements-protocols.txt` lists it.

    cd tests/property
    lake build protocols-property
    lake exe protocols-property 1000                          # Every group.
    PROTOCOLS_GROUP=epoch lake exe protocols-property 1000    # One group, or several with commas.
    HEDGEHOG_ONLY=process_slashings lake exe protocols-property 1000
    HEDGEHOG_ONLY=... HEDGEHOG_RECHECK="size seed gamma" lake exe protocols-property

The groups are `epoch`, `epoch-settled`, `operations`, `blocks`, `blocks-gloas`, `accessors`, `mutators`, `upgrades`, `whole-blocks`, `duties`, `across`, `light-client`, `gossip`, `real-bls`, `between`, `mainnet`, `pure`, `lists`, `confirmation` and `optimistic`.
`PROTOCOLS_LOG=file` makes the oracle write every command it gets, and `ORACLE_REASONS=1` makes it print where the reference refused.

## Result

No property found a place where EthLib computes something other than its source defines.
So a bug that remains is not in what this driver reaches, or it needs an input that these generators do not make.
There is no group of findings, since nothing is pinned as a disagreement.
Every failure met on the way was a mistake of the harness; "Harness mistakes" lists them.
Three places where EthLib differs from the pinned consensus-specs on purpose are under "Findings", so that the next round does not meet them as failures.

## What is new against the earlier rounds

The earlier consensus driver ran the state transition at the minimal preset and configuration, with a stand-in signature, one operation per block, and a payload whose fields were zero.
The earlier fork choice driver left out fast confirmation, optimistic sync, inclusion lists and the duties of a validator.

### Every preset and configuration

Mainnet and minimal agree on many values, so a definition that reads the wrong one passes at both.
`MAX_EFFECTIVE_BALANCE` and `MIN_ACTIVATION_BALANCE` are 32 ETH in both.
`MIN_DEPOSIT_AMOUNT` and `EFFECTIVE_BALANCE_INCREMENT` are 1 ETH in both.
`MIN_SLASHING_PENALTY_QUOTIENT` equals its Altair value at minimal.
`MIN_SEED_LOOKAHEAD` is 1 in both, and it sizes the proposer lookahead of Fulu and the window of payload committees of Gloas.

Here every case draws its preset and its configuration.
A preset is `minimal` or `mainnet` and a list of `NAME=value`.
The driver builds a `Preset` from it with `setPreset` of `Property/Protocols/Names.lean`, one line per field.
The oracle runs the source of each fork of consensus-specs again with those literals replaced, and with the earlier forks taken from the same build (`oracle/protocols_spec.py`).
So the SSZ types of the reference have the lengths of the preset, and a state of 6 slots per epoch with a sync committee of 12 is a state on both sides.
A build takes about a second and is kept.

The presets are these (`Property/Protocols/World.lean`).

| Name | What it is |
| --- | --- |
| minimal | the minimal preset |
| mainnet, short vectors | every value of mainnet but three vector lengths, so that a state is small |
| odd times | 6 slots per epoch, 1 shuffle round, committees of 3, a sync committee of 12 and a period of 3 epochs, a seed lookahead of 2 and 3, an inclusion delay of 2 |
| odd rewards | every quotient and multiplier of rewards and penalties a different prime, per fork |
| odd balances | the five balance values of a preset each its own |
| odd limits | every limit of a list or of a sweep small and odd |
| tiny | 2 slots per epoch, committees of 1, 90 shuffle rounds, a sync committee of 4, a payload committee of 2 |
| drawn | one of 24 presets whose 37 values are picked from lists by a seed |
| mainnet | the mainnet preset itself, in the group `mainnet`, at a twentieth of the cases |

A configuration is drawn for every case, since the oracle sets it on the module without building anything.
Twenty values that the state transition reads are drawn, among them every churn limit and quotient, the two withdrawability delays, the exit period, the ejection balance, the inactivity score values, the blob limits and three fork versions.
Three cases of four also draw the first epoch of every fork: 0 mostly, a small epoch, or never.
Both named configurations leave Gloas and Heze in the far future, and `get_ptc` refuses a slot before the epoch of Gloas.
So the payload committee, and every payload attestation in a block, was refused on both sides in the earlier rounds; here it is reached.

The generators read their edges from the world: the last slot of an epoch, half the vector of slashings, the hysteresis steps, the exit period, the ends of the sync committee period and of the voting period.

### Every fork, also those between consensus forks

`Base.Fork` is one order of the forks of both layers, so a definition of the consensus layer takes any of them.
Berlin and London lie between Phase 0 and Altair, Arrow Glacier and Gray Glacier before Bellatrix, Paris before Capella, and five forks of the blob schedule between Fulu and Gloas.
`Config.forkVersion` says what such a fork means: the rules of the latest consensus fork at or before it.
The official vectors and the earlier rounds ran the nine consensus forks only.
The group `between` runs the steps, operations, accessors, mutators, whole blocks and duties at these ten forks, against consensus-specs at the consensus fork in force.
A comparison written as an equality with a consensus fork, where the rule holds from that fork on, would differ there.

### Real BLS

With `signatures = real` the oracle signs every operation with the secret keys of the test validators, and consensus-specs verifies with its own BLS.
EthLib runs `SignatureChecks.bls`.
A signature that a case wants wrong is wrong in one of five ways in turn: bytes that are no point, a signature by another key, a signature under another domain, the point at infinity, and a signature of the object root without the domain.
One deposit in nine carries a public key that is none: the point at infinity, an x coordinate off the curve, a point outside the subgroup, and bytes without the compression bit.
Such a deposit must be skipped and not fail its block, which both sides do.
A sync aggregate is signed by the members whose bit is set, so the three ways of `syncParticipantPubkeys` (the aggregate key, the aggregate less the absent keys, the keys of the signers) each meet a real signature.
The committees of the small registries hold a validator several times, so the sums count keys with their multiplicity.

A pairing costs EthLib a few milliseconds, so the group runs a quarter of the cases, not a twentieth as planned.

### Every field of a state and of a block

`fill=seed` sets the fields of a state that the words of the earlier driver left at zero: the genesis time, the deposit root and block hash, the state root and proposer of the latest header, every field of the latest payload header, historical summaries, and from Gloas the latest bid and the availability bits.
Four states of five have it.
An upgrade that copies the payload header field by field was compared on zero headers before.
`dup=i,j` gives two validators one key, in one state of six.
`ptc` gives a state the window of payload committees that its registry has.

A whole block (`oracle/protocols_blocks.py`) has every field of its payload filled from a seed, with transactions of lengths around a chunk, and holds up to several operations of each kind, picked so that most fit the state.
From Gloas a block may hold more operations than a block may, which each step must refuse by its own count.
The execution layer of both sides accepts, refuses, or answers from a digest of the request it is given: the root of the payload, the versioned hashes, the parent beacon block root and the typed request lists.
A request with a wrong versioned hash or a wrong list then gets another answer on one side.
`state_transition` runs a signed block some slots ahead, with the signature and the state root checked or not.

### Slots across forks, duties, light client, gossip

`process_slots_across` runs `processSlotsAcross` on a state of the first epochs, under a configuration whose forks start within those epochs.
The reference processes one slot at a time and upgrades when a slot starts the epoch of the next fork, as the `fork.md` of each fork says.
Two forks may start at one epoch, so one slot can cross several, up to all eight.

The duties of `validator.md` that take a state run as calls: the committee of a validator, the aggregator selections, the sync committee duties, the payload committee and its assignment, the inclusion list committee and its assignment, the custody requirement, and the weak subjectivity period.
The period varies here, since the configuration draws its churn values.

A full node makes a light client update from a block, its parent and their states, which the oracle builds so that their headers and roots agree, or breaks in one of four ways.
The update, its finality and optimistic updates, and its upgrade to the next fork that changes it are compared by root.

The gossip rules of voluntary exits, proposer slashings, attester slashings, changes of BLS credentials and sync committee messages run on a store whose anchor is the state of the case, twice each, so that the second check meets what the first recorded.

### Fork choice

The fast confirmation rule runs as a `StateMachine` on top of the store machine of `Property/ForkChoice/Store.lean`, at eight forks.
The optimistic store and the store of inclusion lists are `Command` scenarios in madhouse mode with ranges of 120 and 100 commands.

## What was tested

The label shares are percentages of the cases of the last run.
A minimum in a label is the one in force at that run; the minimums of the rule were lowered after it, to a third of what it showed.
`changed` and `unchanged` say whether the call changed the state, `refused` that both sides refused, `value` that the call returned a value, `skipped` that the reference has no such call or the oracle could build no argument.
Every property of a call draws its fork among those that have the call, and its preset and configuration as above.

### Group `epoch`

EthLib: the 21 steps of `steps` in `Calls.lean`.
Reference: the function of the same name.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_justification_and_finalization | 1000 | changed 70.6, unchanged 26.7, refused 2.7 | pass |
| process_inactivity_updates | 1000 | changed 43.2, unchanged 42.1, refused 14.7 | pass |
| process_rewards_and_penalties | 1000 | changed 44.6, unchanged 32.2, refused 23.2 | pass |
| process_registry_updates | 1000 | unchanged 57.3, changed 41.5, refused 1.2 | pass |
| process_slashings | 1000 | unchanged 78.6, changed 19.4, refused 2 | pass |
| process_eth1_data_reset | 1000 | unchanged 92.3, changed 7.7 | pass |
| process_pending_deposits | 1000 | changed 70.1, unchanged 19.5, refused 10.4 | pass |
| process_pending_consolidations | 1000 | unchanged 67.8, refused 21, changed 11.2 | pass |
| process_builder_pending_payments | 1000 | unchanged 50.9, changed 49.1 | pass |
| process_effective_balance_updates | 1000 | changed 56.2, unchanged 26.1, refused 17.7 | pass |
| process_slashings_reset | 1000 | unchanged 95.5, changed 4.5 | pass |
| process_randao_mixes_reset | 1000 | changed 100 | pass |
| process_historical_roots_update | 1000 | unchanged 85.9, changed 14.1 | pass |
| process_historical_summaries_update | 1000 | unchanged 85.5, changed 14.5 | pass |
| process_participation_record_updates | 1000 | changed 60.6, unchanged 39.4 | pass |
| process_participation_flag_updates | 1000 | changed 83.3, unchanged 16.7 | pass |
| process_sync_committee_updates | 1000 | unchanged 73.8, changed 17.9, refused 8.3 | pass |
| process_proposer_lookahead | 1000 | changed 55.8, refused 33, unchanged 11.2 | pass |
| process_ptc_window | 1000 | refused 88.4, changed 11.6 | pass |
| process_epoch | 1000 | refused 60.4, changed 39.6 | pass |
| process_slot | 1000 | changed 100 | pass |

### Group `epoch-settled`

EthLib: the same, on settled validators.
Reference: the same.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_justification_and_finalization, settled validators | 1000 | changed 80.2, unchanged 12.7, refused 7.1 | pass |
| process_inactivity_updates, settled validators | 1000 | changed 53.9, unchanged 28.9, refused 17.2 | pass |
| process_rewards_and_penalties, settled validators | 1000 | changed 58.5, refused 26.5, unchanged 15 | pass |
| process_registry_updates, settled validators | 1000 | changed 53.6, unchanged 44.8, refused 1.6 | pass |
| process_slashings, settled validators | 1000 | unchanged 98, refused 1.8, changed 0.2 | pass |
| process_eth1_data_reset, settled validators | 1000 | unchanged 92.9, changed 7.1 | pass |
| process_pending_deposits, settled validators | 1000 | changed 68.3, unchanged 20.4, refused 11.3 | pass |
| process_pending_consolidations, settled validators | 1000 | unchanged 83.2, refused 11.9, changed 4.9 | pass |
| process_builder_pending_payments, settled validators | 1000 | unchanged 52.3, changed 47.7 | pass |
| process_effective_balance_updates, settled validators | 1000 | changed 61.2, refused 24.3, unchanged 14.5 | pass |
| process_slashings_reset, settled validators | 1000 | unchanged 95.9, changed 4.1 | pass |
| process_randao_mixes_reset, settled validators | 1000 | changed 100 | pass |
| process_historical_roots_update, settled validators | 1000 | unchanged 86.3, changed 13.7 | pass |
| process_historical_summaries_update, settled validators | 1000 | unchanged 87.6, changed 12.4 | pass |
| process_participation_record_updates, settled validators | 1000 | changed 55.1, unchanged 44.9 | pass |
| process_participation_flag_updates, settled validators | 1000 | changed 94, unchanged 6 | pass |
| process_sync_committee_updates, settled validators | 1000 | unchanged 74.9, changed 21.9, refused 3.2 | pass |
| process_proposer_lookahead, settled validators | 1000 | changed 86.6, refused 8.8, unchanged 4.6 | pass |
| process_ptc_window, settled validators | 1000 | changed 61.2, refused 38.8 | pass |
| process_epoch, settled validators | 1000 | refused 55.8, changed 44.2 | pass |
| process_slot, settled validators | 1000 | changed 100 | pass |

### Group `operations`

EthLib: the 15 operations of `operations`.
Reference: the same.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_voluntary_exit | 1000 | refused 77.1, changed 22.9 | pass |
| process_proposer_slashing | 1000 | refused 75.8, changed 24.2 | pass |
| process_attester_slashing | 1000 | refused 90.3, changed 9.7 | pass |
| process_attestation | 1000 | refused 77.2, changed 12.1, unchanged 7.5, skipped 3.2 | pass |
| process_bls_to_execution_change | 1000 | refused 83, changed 17 | pass |
| process_deposit | 1000 | changed 70.6, refused 29.4 | pass |
| process_deposit_request | 1000 | changed 100 | pass |
| process_withdrawal_request | 1000 | unchanged 86.1, changed 12.7, refused 1.2 | pass |
| process_consolidation_request | 1000 | unchanged 92.9, changed 7.1 | pass |
| process_builder_deposit_request | 1000 | changed 60.8, unchanged 39.1, refused 0.1 | pass |
| process_builder_exit_request | 1000 | unchanged 98.4, changed 1.6 | pass |
| process_execution_payload_bid | 1000 | refused 90.5, changed 9.5 | pass |
| process_sync_aggregate | 1000 | changed 61.7, refused 38.3 | pass |
| process_withdrawals | 1000 | changed 47.1, refused 43.8, unchanged 9.1 | pass |
| process_slots | 1000 | changed 69.2, refused 30.8 | pass |

### Group `blocks`

EthLib: `processBlock` before Gloas.
Reference: `process_block`.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_block | 1000 | refused 68.1, changed 31.9 | pass |

### Group `blocks-gloas`

EthLib: `processBlock` from Gloas, with payload attestations.
Reference: `process_block`.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_block, from Gloas | 1000 | refused 79.6, changed 20.4 | pass |

### Group `accessors`

EthLib: the 28 accessors of `accessors`.
Reference: the same.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| get_total_active_balance | 1000 | value 100 | pass |
| get_validator_churn_limit | 1000 | value 100 | pass |
| get_validator_activation_churn_limit | 1000 | skipped 81.1, value 18.9 | pass |
| get_balance_churn_limit | 1000 | value 50.8, skipped 49.2 | pass |
| get_activation_exit_churn_limit | 1000 | value 50.2, skipped 49.8 | pass |
| get_consolidation_churn_limit | 1000 | value 100 | pass |
| get_exit_churn_limit | 1000 | value 100 | pass |
| get_activation_churn_limit | 1000 | value 100 | pass |
| get_beacon_proposer_index | 1000 | value 95.2, refused 4.8 | pass |
| get_finality_delay | 1000 | value 89.4, refused 10.6 | pass |
| is_in_inactivity_leak | 1000 | value 91, refused 9 | pass |
| get_eligible_validator_indices | 1000 | value 100 | pass |
| get_next_sync_committee_indices | 1000 | value 92, refused 8 | pass |
| get_next_sync_committee | 1000 | value 91.1, refused 8.9 | pass |
| get_expected_withdrawals | 1000 | value 72.6, refused 27.4 | pass |
| get_active_validator_indices | 1000 | value 100 | pass |
| get_committee_count_per_slot | 1000 | value 100 | pass |
| get_block_root | 1000 | refused 54.7, value 45.3 | pass |
| get_block_root_at_slot | 1000 | refused 62.7, value 37.3 | pass |
| get_randao_mix | 1000 | value 100 | pass |
| get_beacon_committee | 1000 | value 99, refused 1 | pass |
| get_pending_balance_to_withdraw | 1000 | value 100 | pass |
| get_base_reward | 1000 | value 80.4, refused 19.6 | pass |
| get_beacon_proposer_indices | 1000 | value 80.1, refused 19.9 | pass |
| get_seed | 1000 | value 89.2, refused 10.8 | pass |
| get_domain | 1000 | value 100 | pass |
| compute_proposer_index | 1000 | value 44, refused 30.6, skipped 25.4 | pass |
| get_attesting_indices | 1000 | value 92.9, refused 4.7, skipped 2.4 | pass |

### Group `mutators`

EthLib: the 8 mutators of `mutators`.
Reference: the same.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| slash_validator | 1000 | changed 72.1, refused 27.9 | pass |
| initiate_validator_exit | 1000 | changed 60.9, refused 26.4, unchanged 12.7 | pass |
| compute_exit_epoch_and_update_churn | 1000 | changed 86.3, unchanged 7, refused 6.7 | pass |
| compute_consolidation_epoch_and_update_churn | 1000 | changed 63.2, refused 29, unchanged 7.8 | pass |
| switch_to_compounding_validator | 1000 | changed 64.6, refused 24.4, unchanged 11 | pass |
| queue_excess_active_balance | 1000 | changed 42.3, unchanged 38.8, refused 18.9 | pass |
| increase_balance | 1000 | changed 41.3, refused 32.6, unchanged 26.1 | pass |
| decrease_balance | 1000 | changed 53.4, unchanged 24.6, refused 22 | pass |

### Group `upgrades`

EthLib: the 8 fork upgrades.
Reference: `upgrade_to_<fork>`.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| upgrade_to_altair | 1000 | upgraded 75.3, refused 24.7 | pass |
| upgrade_to_bellatrix | 1000 | upgraded 100 | pass |
| upgrade_to_capella | 1000 | upgraded 100 | pass |
| upgrade_to_deneb | 1000 | upgraded 100 | pass |
| upgrade_to_electra | 1000 | upgraded 100 | pass |
| upgrade_to_fulu | 1000 | upgraded 86.5, refused 13.5 | pass |
| upgrade_to_gloas | 1000 | upgraded 51.9, refused 48.1 | pass |
| upgrade_to_heze | 1000 | upgraded 52.6, refused 47.4 | pass |

### Group `whole-blocks`

EthLib: `processBlock`, `processOperations`, `processExecutionPayload`, `stateTransition`.
Reference: the same, with the digest engine.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_block_full | 1000 | refused 69.4, changed 30.6 | pass |
| process_operations | 1000 | refused 37.5, changed 34.8, unchanged 27.7 | pass |
| process_execution_payload | 1000 | changed 55.2, refused 44.8 | pass |
| state_transition | 1000 | refused 69.8, changed 24.8, skipped 5.4 | pass |

### Group `duties`

EthLib: `HonestValidator`, `PayloadTimeliness`, `InclusionListCommittee`, `WeakSubjectivity`, `isAggregator`, `isSyncCommitteeAggregator`.
Reference: `validator.md` of each fork.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| get_committee_assignment | 1000 | value 81.3, refused 18.7 | pass |
| is_proposer | 1000 | value 98.6, refused 1.4 | pass |
| compute_weak_subjectivity_period | 1000 | value 100 | pass |
| is_assigned_to_sync_committee | 1000 | value 56.2, refused 43.8 | pass |
| compute_subnets_for_sync_committee | 1000 | value 68.3, refused 31.7 | pass |
| get_ptc | 1000 | refused 56.1, value 43.9 | pass |
| get_ptc_assignment | 1000 | refused 55.6, value 44.4 | pass |
| get_upcoming_proposal_slots | 1000 | value 100 | pass |
| get_inclusion_list_committee | 1000 | value 89.4, refused 10.6 | pass |
| get_inclusion_list_committee_assignment | 1000 | value 64.4, refused 35.6 | pass |
| is_aggregator | 1000 | value 99.1, refused 0.9 | pass |
| is_sync_committee_aggregator | 1000 | value 100 | pass |
| get_validators_custody_requirement | 1000 | value 72, refused 28 | pass |
| process_payload_attestation | 1000 | unchanged 37.6, skipped 34.2, refused 28.2 | pass |

### Group `across`

EthLib: `processSlotsAcross`.
Reference: `process_slots` and `upgrade_to_<fork>` at each fork epoch.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_slots_across | 1000 | no fork crossed 61.6, refused 20, forks crossed: 1 6.2, forks crossed: 3 3.9, forks crossed: 2 3.3, forks crossed: 6 2.9, forks crossed: 5 0.8, forks crossed: 7 0.5, forks crossed: 4 0.3, forks crossed: 8 0.3, forks crossed: 9 0.2 | pass |

### Group `light-client`

EthLib: `createLightClientUpdate`, the finality and optimistic updates, `LightClientUpdate.upgrade`.
Reference: `create_light_client_update`, `upgrade_lc_update_to_<fork>`.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| create_light_client_update | 1000 | refused 54.1, value 45.9 | pass |

### Group `gossip`

EthLib: `validateGossipMessage` for exits, slashings, credential changes, sync messages.
Reference: `validate_*_gossip`.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| gossip | 1000 | value 91.9, answers reject,reject 41.9, answers accept,ignore 28.6, answers ignore,ignore 21.4, skipped 8.1 | pass |

### Group `real-bls`

EthLib: the signed calls with `SignatureChecks.bls`.
Reference: consensus-specs with its own BLS.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_voluntary_exit, real BLS | 250 | refused 75.2, changed 24.8 | pass |
| process_proposer_slashing, real BLS | 250 | refused 72, changed 28 | pass |
| process_attester_slashing, real BLS | 250 | refused 88.8, changed 11.2 | pass |
| process_attestation, real BLS | 250 | refused 78.8, changed 11.2, unchanged 7.6, skipped 2.4 | pass |
| process_bls_to_execution_change, real BLS | 250 | refused 82.8, changed 17.2 | pass |
| process_deposit, real BLS | 250 | changed 68, refused 32 | pass |
| process_deposit_request, real BLS | 250 | changed 100 | pass |
| process_builder_deposit_request, real BLS | 250 | changed 64.4, unchanged 35.2, refused 0.4 | pass |
| process_execution_payload_bid, real BLS | 250 | refused 89.2, changed 10.8 | pass |
| process_sync_aggregate, real BLS | 250 | changed 64.4, refused 35.6 | pass |
| process_pending_deposits, real BLS | 250 | changed 73.6, unchanged 18.8, refused 7.6 | pass |
| upgrade_to_gloas, real BLS | 250 | upgraded 51.2, refused 48.8 | pass |
| process_block, real BLS | 250 | refused 64.8, changed 35.2 | pass |
| process_block, from Gloas, real BLS | 250 | refused 79.2, changed 20.8 | pass |
| process_block_full, real BLS | 250 | refused 64.8, changed 35.2 | pass |
| state_transition, real BLS | 250 | refused 70, changed 25.2, skipped 4.8 | pass |
| process_payload_attestation, real BLS | 250 | unchanged 38.8, skipped 38, refused 23.2 | pass |

EthLib: deposits with public keys that are none.
Reference: the same.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_deposit, real BLS | 1000 | changed 70.6, refused 29.4 | pass |
| process_deposit_request, real BLS | 1000 | changed 100 | pass |
| process_pending_deposits, real BLS | 1000 | changed 69, unchanged 21.6, refused 9.4 | pass |

### Group `between`

EthLib: the calls at the ten forks between consensus forks.
Reference: the consensus fork in force.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_justification_and_finalization, between forks | 400 | changed 77.5, unchanged 15.3, refused 7.3 | pass |
| process_inactivity_updates, between forks | 400 | changed 53.3, unchanged 29.5, refused 17.3 | pass |
| process_rewards_and_penalties, between forks | 400 | changed 56.3, refused 27, unchanged 16.8 | pass |
| process_registry_updates, between forks | 400 | changed 55.8, unchanged 43.3, refused 1 | pass |
| process_eth1_data_reset, between forks | 400 | unchanged 93.5, changed 6.5 | pass |
| process_pending_deposits, between forks | 400 | changed 74, unchanged 14.8, refused 11.3 | pass |
| process_pending_consolidations, between forks | 400 | unchanged 83.5, refused 13, changed 3.5 | pass |
| process_effective_balance_updates, between forks | 400 | changed 65.8, refused 20.5, unchanged 13.8 | pass |
| process_randao_mixes_reset, between forks | 400 | changed 100 | pass |
| process_participation_record_updates, between forks | 400 | changed 54.8, unchanged 45.3 | pass |
| process_participation_flag_updates, between forks | 400 | changed 93.3, unchanged 6.8 | pass |
| process_proposer_lookahead, between forks | 400 | changed 83.3, refused 10.8, unchanged 6 | pass |
| process_ptc_window, between forks | 400 | changed 61.5, refused 38.5 | pass |
| process_epoch, between forks | 400 | refused 51.5, changed 48.5 | pass |
| process_proposer_slashing, between forks | 400 | refused 74.5, changed 25.5 | pass |
| process_execution_payload_bid, between forks | 400 | refused 90.5, changed 9.5 | pass |
| process_execution_payload, between forks | 400 | changed 58.3, refused 41.8 | pass |
| process_payload_attestation, between forks | 400 | unchanged 37.5, skipped 36.5, refused 26 | pass |
| process_slashings, between forks | 400 | unchanged 97, refused 2.8, changed 0.3 | pass |
| process_builder_pending_payments, between forks | 400 | unchanged 51.5, changed 48.5 | pass |
| process_slashings_reset, between forks | 400 | unchanged 95, changed 5 | pass |
| process_historical_roots_update, between forks | 400 | unchanged 86, changed 14 | pass |
| process_historical_summaries_update, between forks | 400 | unchanged 89, changed 11 | pass |
| process_sync_committee_updates, between forks | 400 | unchanged 75.3, changed 20, refused 4.8 | pass |
| process_slot, between forks | 400 | changed 100 | pass |
| process_voluntary_exit, between forks | 400 | refused 76.8, changed 23.3 | pass |
| process_attester_slashing, between forks | 400 | refused 88.5, changed 11.5 | pass |
| process_attestation, between forks | 400 | refused 79.5, changed 12, unchanged 6.3, skipped 2.3 | pass |
| process_bls_to_execution_change, between forks | 400 | refused 82.5, changed 17.5 | pass |
| process_deposit, between forks | 400 | changed 69.5, refused 30.5 | pass |
| process_deposit_request, between forks | 400 | changed 100 | pass |
| process_builder_deposit_request, between forks | 400 | changed 59, unchanged 39.8, refused 1.3 | pass |
| process_builder_exit_request, between forks | 400 | unchanged 97.3, changed 2.8 | pass |
| process_sync_aggregate, between forks | 400 | changed 62.5, refused 37.5 | pass |
| process_slots, between forks | 400 | changed 69.5, refused 30.5 | pass |
| process_block_full, between forks | 400 | refused 62.3, changed 37.8 | pass |
| process_withdrawal_request, between forks | 400 | unchanged 85.3, changed 13.3, refused 1.5 | pass |
| process_consolidation_request, between forks | 400 | unchanged 94.3, changed 5.5, refused 0.3 | pass |
| process_withdrawals, between forks | 400 | changed 51.3, refused 47.8, unchanged 1 | pass |
| process_operations, between forks | 400 | changed 38.3, unchanged 34.3, refused 27.5 | pass |
| state_transition, between forks | 400 | refused 62, changed 31, skipped 7 | pass |
| get_total_active_balance, between forks | 400 | value 100 | pass |
| get_validator_churn_limit, between forks | 400 | value 100 | pass |
| get_validator_activation_churn_limit, between forks | 400 | skipped 100 | pass |
| get_balance_churn_limit, between forks | 400 | value 100 | pass |
| get_activation_exit_churn_limit, between forks | 400 | value 100 | pass |
| get_exit_churn_limit, between forks | 400 | value 100 | pass |
| get_activation_churn_limit, between forks | 400 | value 100 | pass |
| get_beacon_proposer_index, between forks | 400 | value 95, refused 5 | pass |
| get_finality_delay, between forks | 400 | value 89.8, refused 10.3 | pass |
| get_eligible_validator_indices, between forks | 400 | value 100, answers [] 10 | pass |
| get_next_sync_committee_indices, between forks | 400 | value 90, refused 10 | pass |
| get_next_sync_committee, between forks | 400 | value 90.8, refused 9.3 | pass |
| get_expected_withdrawals, between forks | 400 | value 73.3, refused 26.8 | pass |
| get_active_validator_indices, between forks | 400 | value 100, answers [] 18.8 | pass |
| get_block_root, between forks | 400 | refused 56.5, value 43.5 | pass |
| get_block_root_at_slot, between forks | 400 | refused 64.8, value 35.3 | pass |
| get_beacon_committee, between forks | 400 | value 98.8, answers [] 27.3, refused 1.3 | pass |
| get_base_reward, between forks | 400 | value 73.8, refused 26.3 | pass |
| get_beacon_proposer_indices, between forks | 400 | value 79.3, refused 20.8 | pass |
| get_attesting_indices, between forks | 400 | value 91.5, answers [] 49.5, refused 5, skipped 3.5 | pass |
| get_validators_custody_requirement, between forks | 400 | value 74.5, refused 25.5 | pass |
| get_consolidation_churn_limit, between forks | 400 | value 100 | pass |
| get_committee_count_per_slot, between forks | 400 | value 100 | pass |
| get_randao_mix, between forks | 400 | value 100 | pass |
| get_pending_balance_to_withdraw, between forks | 400 | value 100 | pass |
| get_seed, between forks | 400 | value 90.5, refused 9.5 | pass |
| get_domain, between forks | 400 | value 100 | pass |
| get_committee_assignment, between forks | 400 | value 80.8, answers None 28, refused 19.3 | pass |
| get_ptc, between forks | 400 | refused 60.3, value 39.8 | pass |
| get_ptc_assignment, between forks | 400 | refused 59.5, value 40.5, answers None 33.3 | pass |
| get_upcoming_proposal_slots, between forks | 400 | value 100, answers [] 89.8 | pass |
| get_inclusion_list_committee, between forks | 400 | value 89.3, refused 10.8 | pass |
| get_inclusion_list_committee_assignment, between forks | 400 | value 64.5, refused 35.5, answers None 24.5 | pass |
| process_slashings, between forks | 400 | unchanged 98, refused 1.5, changed 0.5 | pass |
| process_slashings_reset, between forks | 400 | unchanged 93.5, changed 6.5 | pass |
| process_proposer_slashing, between forks | 400 | refused 75.3, changed 24.8 | pass |
| process_attester_slashing, between forks | 400 | refused 90.3, changed 9.8 | pass |
| is_in_inactivity_leak, between forks | 400 | value 91, answers false 72.3, answers true 18.8, refused 9 | pass |
| compute_proposer_index, between forks | 400 | value 59, refused 41 | pass |
| slash_validator, between forks | 400 | changed 69, refused 31 | pass |
| initiate_validator_exit, between forks | 400 | changed 64.8, refused 22.8, unchanged 12.5 | pass |
| compute_exit_epoch_and_update_churn, between forks | 400 | changed 86.8, unchanged 8.3, refused 5 | pass |
| compute_consolidation_epoch_and_update_churn, between forks | 400 | changed 62, refused 30.3, unchanged 7.8 | pass |
| switch_to_compounding_validator, between forks | 400 | changed 66.5, refused 22.8, unchanged 10.8 | pass |
| queue_excess_active_balance, between forks | 400 | changed 42.5, unchanged 31.8, refused 25.8 | pass |
| increase_balance, between forks | 400 | changed 46.5, refused 30.5, unchanged 23 | pass |
| decrease_balance, between forks | 400 | changed 51.5, refused 27.3, unchanged 21.3 | pass |
| is_proposer, between forks | 400 | value 99, answers false 93, answers true 6, refused 1 | pass |
| compute_weak_subjectivity_period, between forks | 400 | value 100 | pass |
| is_assigned_to_sync_committee, between forks | 400 | value 53.8, refused 46.3, answers true 41.8, answers false 12 | pass |
| compute_subnets_for_sync_committee, between forks | 400 | value 63.8, refused 36.3, answers [] 17.5 | pass |
| is_aggregator, between forks | 400 | value 97, answers true 97, refused 3 | pass |
| is_sync_committee_aggregator, between forks | 400 | value 100, answers true 88, answers false 12 | pass |

### Group `mainnet`

EthLib: the calls at the mainnet preset itself.
Reference: `eth_consensus_specs.<fork>.mainnet`.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| process_justification_and_finalization, mainnet | 50 | changed 80, unchanged 20 | pass |
| process_inactivity_updates, mainnet | 50 | unchanged 40, changed 32, refused 28 | pass |
| process_rewards_and_penalties, mainnet | 50 | changed 62, refused 24, unchanged 14 | pass |
| process_registry_updates, mainnet | 50 | changed 60, unchanged 40 | pass |
| process_slashings, mainnet | 50 | unchanged 100 | pass |
| process_eth1_data_reset, mainnet | 50 | unchanged 96, changed 4 | pass |
| process_pending_deposits, mainnet | 50 | changed 68, unchanged 22, refused 10 | pass |
| process_pending_consolidations, mainnet | 50 | unchanged 96, refused 4 | pass |
| process_builder_pending_payments, mainnet | 50 | unchanged 76, changed 24 | pass |
| process_effective_balance_updates, mainnet | 50 | changed 56, refused 28, unchanged 16 | pass |
| process_slashings_reset, mainnet | 50 | unchanged 100 | pass |
| process_randao_mixes_reset, mainnet | 50 | changed 100 | pass |
| process_historical_roots_update, mainnet | 50 | unchanged 96, changed 4 | pass |
| process_historical_summaries_update, mainnet | 50 | unchanged 90, changed 10 | pass |
| process_participation_record_updates, mainnet | 50 | unchanged 50, changed 50 | pass |
| process_participation_flag_updates, mainnet | 50 | changed 92, unchanged 8 | pass |
| process_sync_committee_updates, mainnet | 50 | unchanged 96, refused 2, changed 2 | pass |
| process_proposer_lookahead, mainnet | 50 | changed 86, refused 14 | pass |
| process_ptc_window, mainnet | 50 | refused 90, changed 10 | pass |
| process_epoch, mainnet | 50 | refused 54, changed 46 | pass |
| process_slot, mainnet | 50 | changed 100 | pass |
| process_voluntary_exit, mainnet | 50 | refused 72, changed 28 | pass |
| process_proposer_slashing, mainnet | 50 | refused 84, changed 16 | pass |
| process_attester_slashing, mainnet | 50 | refused 90, changed 10 | pass |
| process_attestation, mainnet | 50 | refused 86, changed 10, unchanged 4 | pass |
| process_bls_to_execution_change, mainnet | 50 | refused 74, changed 26 | pass |
| process_deposit, mainnet | 50 | changed 64, refused 36 | pass |
| process_deposit_request, mainnet | 50 | changed 100 | pass |
| process_withdrawal_request, mainnet | 50 | unchanged 76, changed 22, refused 2 | pass |
| process_consolidation_request, mainnet | 50 | unchanged 90, changed 10 | pass |
| process_builder_deposit_request, mainnet | 50 | changed 52, unchanged 48 | pass |
| process_builder_exit_request, mainnet | 50 | unchanged 100 | pass |
| process_execution_payload_bid, mainnet | 50 | refused 96, changed 4 | pass |
| process_sync_aggregate, mainnet | 50 | changed 56, refused 44 | pass |
| process_withdrawals, mainnet | 50 | refused 48, changed 44, unchanged 8 | pass |
| process_slots, mainnet | 50 | changed 78, refused 22 | pass |
| get_total_active_balance, mainnet | 50 | value 100 | pass |
| get_validator_churn_limit, mainnet | 50 | value 100 | pass |
| get_validator_activation_churn_limit, mainnet | 50 | skipped 76, value 24 | pass |
| get_balance_churn_limit, mainnet | 50 | skipped 56, value 44 | pass |
| get_activation_exit_churn_limit, mainnet | 50 | value 56, skipped 44 | pass |
| get_consolidation_churn_limit, mainnet | 50 | value 100 | pass |
| get_exit_churn_limit, mainnet | 50 | value 100 | pass |
| get_activation_churn_limit, mainnet | 50 | value 100 | pass |
| get_beacon_proposer_index, mainnet | 50 | value 92, refused 8 | pass |
| get_finality_delay, mainnet | 50 | value 84, refused 16 | pass |
| is_in_inactivity_leak, mainnet | 50 | value 94, refused 6 | pass |
| get_eligible_validator_indices, mainnet | 50 | value 100 | pass |
| get_next_sync_committee_indices, mainnet | 50 | value 98, refused 2 | pass |
| get_next_sync_committee, mainnet | 50 | value 96, refused 4 | pass |
| get_expected_withdrawals, mainnet | 50 | value 80, refused 20 | pass |
| get_active_validator_indices, mainnet | 50 | value 100 | pass |
| get_committee_count_per_slot, mainnet | 50 | value 100 | pass |
| get_block_root, mainnet | 50 | refused 52, value 48 | pass |
| get_block_root_at_slot, mainnet | 50 | refused 62, value 38 | pass |
| get_randao_mix, mainnet | 50 | value 100 | pass |
| get_beacon_committee, mainnet | 50 | value 100 | pass |
| get_pending_balance_to_withdraw, mainnet | 50 | value 100 | pass |
| get_base_reward, mainnet | 50 | value 80, refused 20 | pass |
| get_beacon_proposer_indices, mainnet | 50 | value 68, refused 32 | pass |
| get_seed, mainnet | 50 | value 88, refused 12 | pass |
| get_domain, mainnet | 50 | value 100 | pass |
| compute_proposer_index, mainnet | 50 | value 36, refused 34, skipped 30 | pass |

EthLib: the same, the calls that the run above did not reach in time.
Reference: the same.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| get_total_active_balance, mainnet | 15 | value 100 | pass |
| get_validator_churn_limit, mainnet | 15 | value 100 | pass |
| get_validator_activation_churn_limit, mainnet | 15 | skipped 86.7, value 13.3 | pass |
| get_balance_churn_limit, mainnet | 15 | skipped 60, value 40 | pass |
| get_activation_exit_churn_limit, mainnet | 15 | skipped 53.3, value 46.7 | pass |
| get_exit_churn_limit, mainnet | 15 | value 100 | pass |
| get_activation_churn_limit, mainnet | 15 | value 100 | pass |
| get_beacon_proposer_index, mainnet | 15 | value 93.3, refused 6.7 | pass |
| get_finality_delay, mainnet | 15 | value 60, refused 40 | pass |
| get_eligible_validator_indices, mainnet | 15 | value 100, answers [] 13.3 | pass |
| get_next_sync_committee_indices, mainnet | 15 | value 80, refused 20 | pass |
| get_next_sync_committee, mainnet | 15 | value 93.3, refused 6.7 | pass |
| get_expected_withdrawals, mainnet | 15 | value 73.3, answers []/ 26.7, refused 26.7 | pass |
| get_active_validator_indices, mainnet | 15 | value 100, answers [] 6.7 | pass |
| get_block_root, mainnet | 15 | value 80, refused 20 | pass |
| get_block_root_at_slot, mainnet | 15 | refused 53.3, value 46.7 | pass |
| get_beacon_committee, mainnet | 15 | value 100, answers [] 46.7 | pass |
| get_base_reward, mainnet | 15 | value 93.3, refused 6.7 | pass |
| get_beacon_proposer_indices, mainnet | 15 | value 80, refused 20 | pass |
| get_attesting_indices, mainnet | 15 | value 100, answers [] 86.7 | pass |
| get_consolidation_churn_limit, mainnet | 15 | value 100 | pass |
| is_in_inactivity_leak, mainnet | 15 | value 80, answers false 53.3, answers true 26.7, refused 20 | pass |
| get_committee_count_per_slot, mainnet | 15 | value 100 | pass |
| get_randao_mix, mainnet | 15 | value 100 | pass |
| get_pending_balance_to_withdraw, mainnet | 15 | value 100 | pass |
| get_seed, mainnet | 15 | value 86.7, refused 13.3 | pass |
| get_domain, mainnet | 15 | value 100 | pass |
| compute_proposer_index, mainnet | 15 | refused 66.7, value 20, skipped 13.3 | pass |
| compute_exit_epoch_and_update_churn, mainnet | 15 | changed 100 | pass |
| compute_consolidation_epoch_and_update_churn, mainnet | 15 | refused 53.3, changed 26.7, unchanged 20 | pass |
| process_slashings, mainnet | 15 | unchanged 100 | pass |
| process_slashings_reset, mainnet | 15 | unchanged 100 | pass |
| process_proposer_slashing, mainnet | 15 | refused 86.7, changed 13.3 | pass |
| process_attester_slashing, mainnet | 15 | refused 100 | pass |
| slash_validator, mainnet | 15 | changed 80, refused 20 | pass |
| initiate_validator_exit, mainnet | 15 | changed 93.3, unchanged 6.7 | pass |
| switch_to_compounding_validator, mainnet | 15 | changed 86.7, unchanged 6.7, refused 6.7 | pass |
| queue_excess_active_balance, mainnet | 15 | unchanged 60, changed 26.7, refused 13.3 | pass |
| increase_balance, mainnet | 15 | changed 53.3, unchanged 26.7, refused 20 | pass |
| decrease_balance, mainnet | 15 | changed 46.7, unchanged 26.7, refused 26.7 | pass |
| upgrade_to_altair, mainnet | 15 | upgraded 66.7, refused 33.3 | pass |
| upgrade_to_bellatrix, mainnet | 15 | upgraded 100 | pass |
| upgrade_to_capella, mainnet | 15 | upgraded 100 | pass |
| upgrade_to_deneb, mainnet | 15 | upgraded 100 | pass |
| upgrade_to_electra, mainnet | 15 | upgraded 100 | pass |
| upgrade_to_fulu, mainnet | 15 | upgraded 80, refused 20 | pass |
| upgrade_to_gloas, mainnet | 15 | refused 100 | pass |
| upgrade_to_heze, mainnet | 15 | upgraded 73.3, refused 26.7 | pass |
| process_execution_payload_bid, mainnet | 15 | refused 93.3, changed 6.7 | pass |
| process_block_full, mainnet | 15 | refused 53.3, changed 46.7 | pass |
| process_operations, mainnet | 15 | unchanged 66.7, changed 20, refused 13.3 | pass |
| process_execution_payload, mainnet | 15 | changed 60, refused 40 | pass |
| state_transition, mainnet | 15 | refused 66.7, changed 26.7, skipped 6.7 | pass |
| process_builder_pending_payments, mainnet | 15 | unchanged 100 | pass |
| process_withdrawal_request, mainnet | 15 | unchanged 86.7, changed 13.3 | pass |
| process_consolidation_request, mainnet | 15 | unchanged 86.7, changed 13.3 | pass |
| process_builder_deposit_request, mainnet | 15 | changed 53.3, unchanged 46.7 | pass |
| process_builder_exit_request, mainnet | 15 | unchanged 100 | pass |
| process_execution_payload_bid, mainnet | 15 | refused 100 | pass |
| process_sync_aggregate, mainnet | 15 | changed 53.3, refused 46.7 | pass |
| process_withdrawals, mainnet | 15 | changed 46.7, unchanged 26.7, refused 26.7 | pass |
| process_slots, mainnet | 15 | changed 100 | pass |

### Group `pure`

EthLib: `computeShuffledIndex`, `computeShuffledPermutation`, `Time.lean`.
Reference: the steps of `compute_shuffled_permutation` on one index; the time functions.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| the shuffled position of an index, at any count and round count | 1000 | a count above 2^16 51.5, a count above 2^24 41, a count above 2^32 25.8, refused 22.5, no round 6.4 | pass |
| the shuffle of a whole list, at any round count | 100 | - | pass |
| slots, epochs and time, at any constants | 1000 | - | pass |

EthLib: `getExecutionRequests`.
Reference: `get_execution_requests`.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| the requests of a list of typed requests | 1000 | refused 41.8, some requests 16.4 | pass |

### Group `lists`

EthLib: `InclusionListStore`.
Reference: `process_inclusion_list`, `get_inclusion_list_transactions`, `get_inclusion_list_bits`, `is_inclusion_list_bits_inclusive`.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| the store of inclusion lists follows consensus-specs (madhouse) | 1000 | a first list of a member 93.7, a list was equivocated, at least 10% 70.8, bits: some seat has a list 55.6, bits: the given bits do not include them 47.2 | pass |

### Group `confirmation`

EthLib: `FastConfirmation.lean`.
Reference: consensus-specs with the three changes of finding 1.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| the fast confirmation rule agrees with the reference at altair | 60 | the rule: the confirmed block moved forward, at least 20% 60, the rule: ran at the start of an epoch 53.3, the rule: twice in one slot 33.3, the rule: back to the finalized block, at least 3% 23.3, a restart: keeps the block confirmed before 13.3, the rule: the observed justified checkpoint moved 6.7, a restart: of a block that the store lacks 5 | pass |
| the fast confirmation rule agrees with the reference at bellatrix | 60 | the rule: ran at the start of an epoch 61.7, the rule: the confirmed block moved forward, at least 20% 48.3, the rule: twice in one slot 38.3, a restart: keeps the block confirmed before 21.7, the rule: back to the finalized block, at least 3% 15, the rule: the observed justified checkpoint moved 8.3, a restart: of a block that the store lacks 6.7 | pass |
| the fast confirmation rule agrees with the reference at capella | 60 | the rule: the confirmed block moved forward, at least 20% 53.3, the rule: ran at the start of an epoch 51.7, the rule: twice in one slot 30, a restart: keeps the block confirmed before 20, the rule: back to the finalized block, at least 3% 18.3, the rule: the observed justified checkpoint moved 8.3, a restart: of a block that the store lacks 8.3 | pass |
| the fast confirmation rule agrees with the reference at deneb | 60 | the rule: ran at the start of an epoch 51.7, the rule: the confirmed block moved forward, at least 20% 46.7, the rule: twice in one slot 33.3, a restart: keeps the block confirmed before 21.7, the rule: back to the finalized block, at least 3% 15, a restart: of a block that the store lacks 8.3, the rule: the observed justified checkpoint moved 5 | pass |
| the fast confirmation rule agrees with the reference at electra | 60 | the rule: ran at the start of an epoch 60, the rule: the confirmed block moved forward, at least 20% 36.7, the rule: twice in one slot 30, a restart: keeps the block confirmed before 25, the rule: back to the finalized block, at least 3% 5, a restart: of a block that the store lacks 5, the rule: the observed justified checkpoint moved 3.3 | pass |
| the fast confirmation rule agrees with the reference at fulu | 60 | the rule: the confirmed block moved forward, at least 20% 48.3, the rule: ran at the start of an epoch 48.3, the rule: twice in one slot 35, a restart: keeps the block confirmed before 21.7, the rule: back to the finalized block, at least 3% 11.7, the rule: the observed justified checkpoint moved 10 | pass |
| the fast confirmation rule agrees with the reference at phase0 | 60 | the rule: the confirmed block moved forward, at least 20% 53.3, the rule: ran at the start of an epoch 46.7, the rule: twice in one slot 26.7, a restart: keeps the block confirmed before 15, the rule: back to the finalized block, at least 3% 13.3, a restart: of a block that the store lacks 6.7, the rule: the observed justified checkpoint moved 5 | pass |

EthLib: the same, at Gloas, where the reference is slow.
Reference: the same.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| the fast confirmation rule agrees with the reference at gloas | 14 | the rule: ran at the start of an epoch 21.4, the rule: the confirmed block moved forward 7.1, the rule: twice in one slot 0, the rule: back to the finalized block 0, the rule: the observed justified checkpoint moved 0 | pass |

### Group `optimistic`

EthLib: `OptimisticStore`, `Store.onInvalidPayload`.
Reference: consensus-specs and a model of the guide.

| Property | Cases | Shares of the labels | Result |
| --- | --- | --- | --- |
| the optimistic store follows the guide at fulu (madhouse) | 1000 | valid: of a block that was dropped 74.7, an import: refused, the clock is too near 70.3, invalid: nothing dropped 68.3, an import: a candidate by its parent's payload 47.3, invalid: the head moved back, at least 5% 32.2, invalid: a branch was invalidated, at least 10% 21.1, valid: ancestors left the optimistic set, at least 5% 14 | pass |
| the optimistic store follows the guide at electra (madhouse) | 1000 | valid: of a block that was dropped 72.7, an import: refused, the clock is too near 70.8, invalid: nothing dropped 65, an import: a candidate by its parent's payload 45, invalid: the head moved back, at least 5% 30.1, invalid: a branch was invalidated, at least 10% 18.8, valid: ancestors left the optimistic set, at least 5% 12.2 | pass |
| the optimistic store follows the guide at deneb (madhouse) | 1000 | valid: of a block that was dropped 73.6, an import: refused, the clock is too near 70.7, invalid: nothing dropped 66.6, an import: a candidate by its parent's payload 49.7, invalid: the head moved back, at least 5% 33, invalid: a branch was invalidated, at least 10% 21.2, valid: ancestors left the optimistic set, at least 5% 14.8 | pass |
| the optimistic store follows the guide at capella (madhouse) | 1000 | valid: of a block that was dropped 72.9, an import: refused, the clock is too near 68.8, invalid: nothing dropped 67.2, an import: a candidate by its parent's payload 46.8, invalid: the head moved back, at least 5% 32, invalid: a branch was invalidated, at least 10% 20.2, valid: ancestors left the optimistic set, at least 5% 15.2 | pass |
| the optimistic store follows the guide at bellatrix (madhouse) | 1000 | valid: of a block that was dropped 72.1, an import: refused, the clock is too near 70.8, invalid: nothing dropped 63, an import: a candidate by its parent's payload 48.7, invalid: the head moved back, at least 5% 32.9, invalid: a branch was invalidated, at least 10% 21, valid: ancestors left the optimistic set, at least 5% 16.6 | pass |

In all 381 properties and 182464 cases, 0 failed.

## Findings

None of class BUG.

### 1. The fast confirmation rule differs from the pinned consensus-specs in three stated ways (DOC, known)

`EthLib/Consensus/ForkChoice/FastConfirmation.lean` weighs the committees of a range of slots exactly, where `estimate_committee_weight_between_slots` of consensus-specs takes an average per slot and adjusts it.
Its `computeSafetyThreshold` fails when the discount for empty slots exceeds the weight of the committees since the parent, where `compute_safety_threshold` answers zero.
From Gloas its `computeEmptySlotSupportDiscount` also counts the votes for the pending node of the parent.
The CHANGELOG of EthLib states all three, with the issues 1828, 1832 and 1368, and the module docstring states the first.
So a comparison with the functions of consensus-specs as they are fails by design, and it is not a finding.
The oracle gives consensus-specs the same three changes, written from the CHANGELOG and the docstrings (`patch` in `oracle/protocols_forkchoice.py`), and every other function of the rule is that of consensus-specs.
With that, the two sides agree on every step.
What this does not test: whether the three changes are right, since the reference has them from the same text.

### 2. `computeShuffledIndex` refuses a count above `2^40` (DOC)

`EthLib/Consensus/Shuffle.lean:157` refuses `count > 2^40`, the limit of the validator registry.
`compute_shuffled_index` of consensus-specs has no bound of its own.
No state can hold more validators, so no call of the protocol differs.
The property requires the refusal above `2^40` and the position of consensus-specs at and below it.

### 3. `is_optimistic_candidate_block` is absent from the modules after Bellatrix (reference)

The pinned `eth_consensus_specs` carries `is_optimistic_candidate_block` and `is_execution_block` in its Bellatrix module only.
The oracle writes the three lines of the guide for the later forks.

## Harness mistakes

- HARNESS: `consensus.py` replaces `bls.Verify` when it is imported, so the "real" checks kept after that import were the stand-in; EthLib then accepted a real sync aggregate that the reference refused.
  The oracle now keeps the checks of consensus-specs before that import.
- HARNESS: the same import left the stand-in in place for the fork choice, whose gossip rules then rejected every vote; the oracle now names three modes of signatures, `standin`, `real` and `off`.
- HARNESS: a state of a preset with a short voting period cannot hold 32 votes; the generator now reads the limit from the preset.
- HARNESS: a reader that answers `None` was taken for a call that changes the state.
- HARNESS: `state_transition` to the slot of the state itself is refused by `process_slots`; the generator now moves ahead by a slot or more.
- HARNESS: a scenario shrank to an import on a parent that no earlier command had made; the command needed a `check`.
- HARNESS: the anchor of a store must be a block at the start of an epoch, or the head of the store has no checkpoint block.
- HARNESS: the modules of consensus-specs cache the shuffled permutation by count and seed, not by the number of rounds; the oracle calls the function before its cache.
- HARNESS: `get_ptc` refuses a slot before the epoch of Gloas in the configuration, which both named configurations leave in the far future; the configuration now draws the fork epochs.

## The harness was checked with mutants

`PROTOCOLS_MUTANT=NAME=value` gives the reference one constant that the driver does not have.
`PROTOCOLS_MUTANT=byzantine` gives the reference one percent more of Byzantine stake in the fast confirmation rule.
A constant that sizes a type, such as `PTC_SIZE`, fails at once, since EthLib then cannot read the state.
Each run was of 300 cases, or 40 sequences for the rule.
A mutant of one ETH in `MAX_EFFECTIVE_BALANCE` took 215 cases to show in `get_beacon_proposer_index`: a small change of a constant can be rare to see, which is why the presets here set such constants far apart.
A run with it must fail, which says that the property reads that constant.

| Mutant | The properties that failed |
| --- | --- |
| `EPOCHS_PER_SYNC_COMMITTEE_PERIOD=9` | `is_assigned_to_sync_committee` after 37 cases |
| `INACTIVITY_PENALTY_QUOTIENT_BELLATRIX=16777217` | `process_rewards_and_penalties` after 59 cases |
| `MAX_EFFECTIVE_BALANCE=33000000000` | `get_beacon_proposer_index` after 215 cases; `get_next_sync_committee_indices` after 6 cases |
| `MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP=17` | `get_expected_withdrawals` after 2 cases |
| `MIN_ACTIVATION_BALANCE=33000000000` | `process_registry_updates` after 56 cases; `process_pending_deposits` after 85 cases |
| `MIN_SEED_LOOKAHEAD=2` | `get_seed` after 2 cases |
| `MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR=65` | `slash_validator` after 4 cases |
| `PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX=4` | `process_slashings` after 27 cases |
| `PTC_SIZE=15` | `get_ptc` after 1 cases; `get_ptc_assignment` after 1 cases |
| `SHUFFLE_ROUND_COUNT=11` | `get_beacon_committee` after 1 cases |
| `byzantine` | `the fast confirmation rule agrees with the reference at phase0` after 2 cases |

## Not covered

- The fork choice at another preset than minimal, and with real BLS: the store machine of the earlier round is fixed to the minimal preset, and the machines here run on top of it.
- The Gloas store in depth: no block of the fork choice machine carries payload attestations, builder bids or requests, so `notifyPtcMessages` and the majorities of the payload committee are reached only by single votes.
  The state transition of such blocks is covered in `blocks-gloas`, `whole-blocks` and `duties`.
- Optimistic sync from Gloas: the guide has no text there and EthLib reads it by a choice of its own; `isOptimisticNode` with `hasNoViableBranch` is not run, since the scenario has no votes.
- The fast confirmation rule: the three changes of finding 1 are not tested against an independent source.
  The confirmation machine ran 60 sequences of up to 30 steps at each fork before Gloas, not 1,000: a step may stand for 30 blocks with their votes, and a sequence takes the reference some tens of seconds.
  At Gloas the reference is slower still: the run there is of 14 sequences, and the confirmed block moved in one of them.
  A run of 60 sequences at Gloas and one of 300 at every fork were started and did not end in time.
- Heze: the committee, its assignment and the store of lists are compared; `on_inclusion_list` with the view freeze, the gossip rule of inclusion lists, the satisfaction check of a payload and `getSignedInclusionList` are not.
- The honest validator: `get_eth1_vote`, `compute_on_chain_aggregate`, `process_sync_committee_contributions`, the construction of attestations and aggregates of `HonestAggregation.lean`, every signing helper of `HonestValidator.lean` (they need secret keys in EthLib), `HonestBuilder.lean`.
- Light client: `create_light_client_update` is compared with its finality and optimistic updates and one upgrade; the upgrade of a bootstrap and of a store, an update whose finalized block is of an earlier fork, and a header of an earlier fork inside a later store are not.
- Gossip: the rules of contributions, blob and column sidecars, bids, proposer preferences and inclusion lists.
  The five kinds here run on a store of one block, so no rule that reads a second block is reached.
- `DataAvailability/`: sidecar verification with KZG, and the matrix of columns.
- `ReqResp/`, `History/Era.lean`, `PqKeys/`, `BeaconApi/`, `BuilderApi*`, `RelayApi.lean`: not looked at.
- `Constants.lean`: the 60 values were compared with the constants of consensus-specs by eye, not by a property.
- The whole mainnet state runs a twentieth of the cases, 50 for a property, and the run was cut after its first 29 properties; the others ran 15 cases each.
  Its registries hold at most 128 validators, so a slot of mainnet never has more than one committee and never 128 members.
  The committee count and size at other values are reached by the small presets instead.
- A preset is drawn from 8 written ones and 24 seeded ones, not from all values: a build of the reference takes a second.
  `BYTES_PER_LOGS_BLOOM`, `MAX_EXTRA_DATA_BYTES`, the blob and cell sizes, the transaction limits and the message size bounds are never changed.
- Presets outside what consensus-specs assumes (no slot in an epoch, a sync committee that four subnets do not divide) are not generated: the reference divides by zero there.
- The acceptance of some calls is low, see the table: a bid, an attester slashing, an attestation and a builder exit request are accepted in a tenth of the cases or fewer.

## Notes on lean-hedgehog 0.3.0

What helped.

- `classify`, `label` and `cover` are what the earlier rounds missed most, and they changed how the work went.
  Every run printed the shares, and three generators were fixed on what they showed before any property was trusted: `get_ptc` at 100% refused, a whole block at 16% accepted, `state_transition` at 9%.
- `cover` did its job once on its own: the optimistic scenario passed 200 sequences and failed on "valid: ancestors left the optimistic set" at 6% against a minimum of 10%.
  The generator of `Valid` aimed at blocks that had already been dropped.
- The context first in `check`, `apply` and `next` removed the oracle from every command: the commands of the two scenarios hold only their own numbers, and a `Repr` of a command is what a report prints.
- `buildIn` with `next` let a command name a block that exists (`IMPORT(on 7, ...)`), which made the optimistic scenario reach long chains.
  Without it the first version imported almost nothing.
- `scenario` with a range and a setup: the setup starts the reference store, and 120 commands a sequence gave branches worth invalidating.
- `applySut` with the state before: the fast confirmation machine says from it whether the rule already ran in the same slot.
- `Selection.fromEnv`: `HEDGEHOG_ONLY` with several parts was used for every targeted run and every mutant; no code for selection is left in the driver but a group filter.
- `Gen.bytes` and `bytesHex` replaced the helpers of `Support/`.
- Shrinking stayed good on words: a failing state of 30 words shrank to the slot and the one word that mattered, and a scenario to two imports and one command.

What was awkward.

- A scenario whose command lacks a `check` shrinks into nonsense: a removed import leaves a later `IMPORT(on 5)` without its parent, the oracle fails, and the report shows that harness failure in place of the real one.
  USAGE says so in one sentence; a `Command` whose `buildIn` reads the state could warn when `check` is the default.
- The out-parameters of `Command` force a phantom index: `Import fork` exists only so that `Frame fork` and `Node fork` are determined.
  USAGE documents it, and it still cost a build failure whose message ("instance does not provide concrete values for (semi-)out-params") does not point at the fix.
- `cover` in a command counts sequences, not commands, as USAGE says.
  So "invalid: nothing dropped 68%" reads as if most invalidations did nothing, while it only says that most sequences had one such command.
  A share of the times the line was reached would say more for commands.
- A label is counted only for a case that passes, and a `label` after the comparison is skipped by a failure; that is right, but it means labels must come before the assertion to describe a failing run, and after it to describe only agreed cases.
  I put the preset label after, the outcome label before, and had to think about it.
- The report prints labels in an order that is neither that of the code nor sorted; with nine preset labels and four outcome labels a property's report is hard to scan.
  Sorting by name, or grouping by a prefix, would help.
- Lean's standard output is fully buffered when it goes to a file, so a long run shows nothing until a property ends.
  A flush after each property's report in `checkGroup` would let a run of an hour be watched.
- `checkGroup` has no way to say "this group, a fraction of the cases": the slow groups compute `cases / 4` and `cases / 20` by hand.
- There is no time bound for a property: a state machine of 300 sequences took over an hour on a loaded machine, and the only control is the number of tests.
- `StateMachine.property` needs the model to produce the initial state as a `Gen`, and `initSut` in `m`; wrapping another machine (the fast confirmation machine reuses the store machine of another driver) worked because both are plain structures, but its `Cmd` had to be embedded in a new transition type by hand.
  A combinator that lifts a machine into a larger one would have saved a hundred lines.

What is missing.

- A share per value of a generated dimension: `collect` exists, but nine `preset:` labels on each of 150 properties drown the outcome labels.
  A way to cross two labels (outcome by preset) would show at once that a preset never reaches a branch.
- Confidence for `cover` (the `withConfidence` of Haskell): the minimum had to be set at a third of what a run showed, by hand, per label.

Bugs of the library: none met.

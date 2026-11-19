# Consensus: the beacon chain state transition and its helpers

The driver is `Property/Consensus.lean`, with its modules under `Property/Consensus/`.
The reference is the executable consensus-specs (`eth_consensus_specs`, minimal preset) at commit `aa16bb4c`, which is `v1.7.0-beta.4`, the pin of `tests/sources.toml`.
`oracle/requirements-consensus.txt` lists what the oracle needs.

    cd tests/property
    lake exe consensus-property 1000                 # Every group.
    lake exe consensus-property 1000 epoch           # One group.

    lake exe consensus-property 1000 process_slashings   # The properties so named.

The groups are `pure`, `genesis`, `deposit-tree`, `scenario`, `epoch`, `operations`, `blocks`, `accessors`, `mutators` and `upgrades`.
A full run at 1,000 cases takes about half an hour of one core per group; the groups ran side by side.

## Result

No property found a place where EthLib computes something other than consensus-specs.
There is no `consensus: findings` group, since nothing is pinned as a known disagreement.
Every failure met on the way was a mistake of the harness; "Harness mistakes" lists them.

## How a state reaches both sides

A generator makes a description of a state: words such as `slot=805`, `fin=c-2` and `v=2,3,2048000000000,2048000000001,0,0,0,18446744073709551615,c+1,7,7,0`.
`c+n` and `c-n` are epochs around the current one, so a validator does not depend on the slot and the two shrink apart.
The oracle builds the state with consensus-specs types and returns its SSZ bytes.
EthLib reads those bytes with `SszType.deserialize`, applies its function, and gives the root of the state after.
The oracle applies the function of consensus-specs to the same state.
The two must agree on refusal and on the root, and on a difference the oracle names the fields that differ.
An operation travels the same way: a few numbers say what it is and what is wrong with it, the oracle builds it, EthLib reads its SSZ bytes.

A signature is valid when its first 32 bytes are the SHA-256 of the public keys and the message.
The oracle replaces `bls.Verify` and `bls.FastAggregateVerify` by that check, and the driver gives EthLib the same check as its `SignatureChecks`.
So a wrong domain, a wrong signing root or a wrong set of keys still fails a test, without a pairing.
Public keys are real ones, since sync committees aggregate them.

The generators bias to the edges:
balances at an effective balance plus or minus 0, 1, 2, 4, 5 and 6 hysteresis steps and one Gwei around each;
effective balances at 32 and 2048 ETH and between;
epochs at the current one plus or minus a few, at 31 to 33 and 255 to 257 ahead, at zero and at the far future;
credentials `0x00`, `0x01`, `0x02`, `0x03` and `0xB0`;
amounts near `2^64`, which the reference refuses as an overflow;
registries from empty to 72 validators, the last so that a slot has two committees;
slots in the first three epochs, at sync committee period ends, and anywhere in an epoch.

After each group the driver prints how often the reference accepted, left the state unchanged, refused and skipped each call.
A property that only meets refusals tests little, so the generators were tuned on these numbers.

## What was tested

Cases are per property; a property of a call draws its fork among those that have the call.
The counts are those of the last full run.

| Property | EthLib definitions | Oracle | Cases | Result |
| --- | --- | --- | --- | --- |
| the shuffle of every index, and of the whole list | `computeShuffledIndex`, `computeShuffledPermutation` | `compute_shuffled_index`, both presets; and a permutation | 1000 | pass |
| no shuffled position past the count | `computeShuffledIndex` | the assertion of the source | 1000 | pass |
| a committee of a list of indices | `computeCommittee`, `shuffledCommittee` | `compute_committee`, both presets | 1000 | pass |
| the fork version, blob parameters and digest of a schedule | `Config.forkAtEpoch`, `Config.computeForkVersion`, `Config.getBlobParameters`, `computeForkDigest`, `computeForkDataRoot` | `compute_fork_version`, `get_blob_parameters`, `compute_fork_digest` of Heze under generated fork epochs and blob schedules | 1000 | pass |
| slots, epochs and time | `computeEpochAtSlot`, `computeStartSlotAtEpoch`, `computeActivationExitEpoch`, `computeSyncCommitteePeriod`, `computeTimeAtSlot(Ms)`, `computeSlotAtTime(Ms)`, `secondsToMilliseconds` | the same functions, overflow included | 1000 | pass |
| the presets and configurations | every numeric and byte field of `Preset.minimal`, `Preset.mainnet`, `Config.minimal`, `Config.mainnet` | the constants of the latest fork that names each (162 values per preset) | 8 | pass |
| the genesis state of generated deposits | `initializeBeaconStateFromEth1`, `isValidGenesisState`, `processDeposit` at genesis | `initialize_beacon_state_from_eth1`, `is_valid_genesis_state` of Phase 0, with deposits proved against a naive tree | 1000 | pass |
| the deposit tree against a list of leaves (`StateMachine`) | `DepositTree.new`, `pushLeaf`, `finalize`, `getSnapshot`, `fromSnapshot`, `getProof`, `getRoot`, `DepositTreeSnapshot` SSZ | a naive Merkle tree of depth 32 and `is_valid_merkle_branch` in Python | 1000 sequences of 1 to 60 | pass |
| the operations of a block in any order, per fork (`Command`, madhouse) | fourteen of the operations below, chained on one state | consensus-specs on the same chain of states | 9 forks x 1000 sequences of 1 to 15 | pass |
| the operations of a block in order, per fork (`Command`, deterministic) | the same | the same | 9 x 1 | pass |
| 21 steps of the epoch transition | `processJustificationAndFinalization`, `processInactivityUpdates`, `processRewardsAndPenalties`, `processRegistryUpdates`, `processSlashings`, `processEth1DataReset`, `processPendingDeposits`, `processPendingConsolidations`, `processBuilderPendingPayments`, `processEffectiveBalanceUpdates`, `processSlashingsReset`, `processRandaoMixesReset`, `processHistoricalRootsUpdate`, `processHistoricalSummariesUpdate`, `processParticipationRecordUpdates`, `processParticipationFlagUpdates`, `processSyncCommitteeUpdates`, `processProposerLookahead`, `processPtcWindow`, `processEpoch`, `processSlot` | the function of the same name | 1000 each | pass |
| 15 operations | `processVoluntaryExit`, `processProposerSlashing`, `processAttesterSlashing`, `processAttestation`, `processBlsToExecutionChange`, `processDeposit`, `processDepositRequest`, `processWithdrawalRequest`, `processConsolidationRequest`, `processBuilderDepositRequest`, `processBuilderExitRequest`, `processExecutionPayloadBid`, `processSyncAggregate`, `processWithdrawals`, `processSlots` | the function of the same name | 1000 each | pass |
| a whole block before Gloas | `processBlock` with `processBlockHeader`, `processExecutionPayload`, `processRandao`, `processEth1Data`, `processOperations` | `process_block` | 1000 | pass |
| 28 accessors | `getTotalActiveBalance`, the churn limits of `Accessors` and `Churn`, `getBeaconProposerIndex`, `getFinalityDelay`, `isInInactivityLeak`, `getEligibleValidatorIndices`, `getNextSyncCommitteeIndices`, `getNextSyncCommittee`, `getExpectedWithdrawals`, `getActiveValidatorIndices`, `getCommitteeCountPerSlot`, `getBlockRoot`, `getBlockRootAtSlot`, `getRandaoMix`, `getBeaconCommittee`, `getPendingBalanceToWithdraw`, `getBaseReward`, `getBeaconProposerIndices`, `getSeed`, `getDomain`, `computeProposerIndex`, `getAttestingIndices` | the function of the same name | 1000 each | pass |
| 8 mutators | `slashValidator`, `initiateValidatorExit`, `computeExitEpochAndUpdateChurn`, `computeConsolidationEpochAndUpdateChurn`, `switchToCompoundingValidator`, `queueExcessActiveBalance`, `increaseBalance`, `decreaseBalance` | the function of the same name | 1000 each | pass |
| 8 fork upgrades | `upgradeToAltair`, `carryFields` to Bellatrix, Capella and Deneb, `upgradeToElectra`, `upgradeToFulu`, `upgradeToGloas`, `upgradeToHeze` | `upgrade_to_<fork>` | 1000 each | pass |

In all 107 properties, 97 of them at 1,000 cases, with no failure left.
The slashed validators whose penalty is due were added to the generator after a run showed that `process_slashings` changed the state in 3 cases of 1,000; it then did in 182.

The two state machine styles of lean-hedgehog are both here.
`Property/Consensus/DepositTree.lean` is a `StateMachine` over a `Model`: push, finalize, restore from a snapshot, prove.
A finalization with a count past the leaves, below an earlier one, or with a wrong root must be refused and leave the tree as it was.
After every transition the root, the count, the finalized count and the snapshot are those of the model, and a proof exists exactly for a deposit that is held and not finalized.
`Property/Consensus/Scenario.lean` has one `Command` type per operation of a block, fourteen of them, and runs them in madhouse mode at each fork, whatever the environment says.
The 9,000 madhouse sequences ran about 27,000 commands, of which the reference accepted about 14,000.
The state after a command is the state the next one meets on both sides, so a sequence reaches an exit after a slashing, a consolidation of a validator with a pending withdrawal, an epoch boundary between two requests.

## Findings

None.

## Harness mistakes

Each is one line, as the brief asks.

- HARNESS: `Gen.sequence` dropped fields of a word while shrinking; it needs `atLeast` set to keep its length.
- HARNESS: lists and bit lists of consensus-specs types need their own class, not a Python list.
- HARNESS: Python integers passed where the specification wants `Uint64` made `get_seed` fail on its own.
- HARNESS: a proposer index plus one overflowed in the oracle before the specification saw it.
- HARNESS: a call that a fork's specification lacks (`process_deposit` from Fulu, `compute_proposer_index` and `get_balance_churn_limit` from Gloas, `get_validator_activation_churn_limit` outside Deneb) is skipped, not compared.
- HARNESS: an extra withdrawal past the limit of a payload cannot be built; the last one is replaced.
- HARNESS: the text of a `BitVec` in a `Repr` starts with `0x`, which the constants check read as zero.

## Not covered

- The mainnet preset of the state transition: states are of the minimal preset, and only the helpers that need no state run at both.
  The constants of both presets and configurations are compared by name, so what is left is a use of the wrong constant that the minimal values hide.
- Real BLS: signatures are checked by a stand-in on both sides, so `SignatureChecks.bls` and the point checks of public keys never run here.
- From Gloas: `processParentExecutionPayload`, `processPayloadAttestation`, a whole `processBlock` and `stateTransition` with a block signature and a state root.
  The builders, their payments and their withdrawals are in the generated states, and the bid, the builder requests and the steps that read them are compared.
- Heze: the inclusion list parts belong to another layer, and the Heze state transition is covered only where it shares code with Gloas.
- Genesis after Phase 0: EthLib defines it before Altair only, and so does this test.
- `processExecutionPayload` with an engine that refuses, with transactions, and with execution requests in a payload; `processOperations` with more than one operation in a block (the scenario runs them one by one instead).
- `SyncCommittee.aggregatePubkeys` on keys that are not on the curve, and a registry with two validators of one key: the generated registries hold distinct valid keys.
- `Containers/`: the SSZ of every container is exercised only through the states and operations that the oracle writes and EthLib reads; a container that no call here takes is not read.
- `Constants.lean`: domain types and weights are not compared by name, only through the behaviour of what uses them.
- The acceptance rate of some operations is low, so their refusal paths have more cases than the paths that change the state.
  Of 1,000 cases the reference accepted 135 attestations, 58 attester slashings, 146 blocks, 99 bids, and let 22 builder exits, 67 consolidation requests and 141 withdrawal requests change the state.
  No builder exit took effect in a scenario: a builder that a scenario deposits is never active before the finalized epoch moves, which the scenarios do not make it do.

## Notes on lean-hedgehog

What worked well.

- `Gen` as a monad with shrinking for free made a description of a state cheap to write, and a failing state shrank to a handful of words.
  The harness mistakes above mostly shrank to `slot=7` and one more word, which named the mistake at once.
- `Gen.frequency` carried all the bias to the edges; nothing else was needed for that.
- `forAllWith` with `" ".intercalate` printed a counterexample as the very line the oracle takes, so a failure pastes into the oracle.
- `StateMachine` fitted the deposit tree in under a hundred lines; `transitions` reading the model state made valid finalizations frequent without a filter.
- `propertyM` returning a `TestT IO Unit` kept generation pure and the oracle call in the test; the runner calling the oracle again for every shrink just worked.
- `checkGroup` and `withTests` were all the driver needed.

What was awkward or missing.

- `Gen.sequence` shrinks by dropping elements unless `atLeast` is given, and USAGE does not say so.
  For a record of fixed arity that is a trap: the shrunk value is not a value the generator can make.
  A `Gen.tuple` or a documented `Gen.sequence gs gs.length` idiom would help.
- `Command.build` sees only the context, never the state, so a command cannot be generated to fit the state it will meet (an exit of a validator that is active now).
  The commands here carry small numbers and the oracle resolves them against the state; a `build : χ → σ → Gen κ` is not possible in madhouse mode as it is designed, since the whole sequence is generated before it runs.
- `scenario` needs `Inhabited σ` and starts from `default`, so a first state that comes from `IO` (here: bytes from the oracle) has to travel in the context and in every command, with `none` as the default state.
  An `init : χ → m σ` would be simpler.
- `scenario` fixes the sequence length at 1 to 15; `StateMachine.property` takes a range, `scenario` does not.
- The class `Command κ σ χ m` wants a type per command, and the fourteen instances here are the same four lines; a helper that makes an instance from a name would cut that, though it is the design working as intended.
- A `Property` has no label or classification (`classify`, `cover` of Haskell's Hedgehog), so the share of accepted cases had to be counted in the oracle.
  This was the most missed feature: without it a green run does not say whether it tested the accepting path.
- `Hedgehog.Config` clashes with `EthLib.Consensus.Config` when both namespaces are open; a qualified name solved it.
- The size goes from 0 to 99 with the case number and then starts over, so with `Range.linear` the first cases of a run are always tiny; for a test that needs a populated state a `Range.constant` was the only way to get one early.

Bugs in the library: none met.

Shrinking: counterexamples were good.
A failing state of twenty validators with queues shrank to the slot, the scalars at their origins and the one or two validators that mattered, in 20 to 140 shrinks.
After a `bind` the shrunk values sometimes stopped short of their origin (a slot of 512 where 0 would do), as USAGE says; `Gen.zip` and `genFields` over independent fields avoided most of it.

# Findings: the consensus protocols around the state transition

The driver is `Property/ForkChoice.lean`, with its modules under `Property/ForkChoice/`.
The oracle is `oracle/forkchoice.py`, with `oracle/forkchoice_store.py`, `oracle/forkchoice_lightclient.py` and `oracle/forkchoice_helpers.py`.
The reference is the executable pyspec of consensus-specs at the commit that `tests/sources.toml` pins (`aa16bb4c`, v1.7.0-beta.4), with the minimal preset and BLS switched off on both sides.

```bash
cd tests/property
.venv/bin/pip install -r oracle/requirements-forkchoice.txt
lake build forkchoice-property
lake exe forkchoice-property 1000
ONLY=phase0 lake exe forkchoice-property 1000    # The properties whose name holds a word.
```

No property found a place where EthLib computes something other than its source defines, apart from one documented and deliberate deviation (finding 1).
Every other disagreement that a run showed was the harness or the pyspec itself, and is listed under Findings so that the next round does not meet it again.

## What was tested

Each state machine row counts sequences, not commands.
A sequence of the store holds 1 to 40 commands, and one `chain` command stands for up to 12 blocks with their votes.

| Property | Style | EthLib definitions | Reference | Cases | Result |
| --- | --- | --- | --- | --- | --- |
| the store and gossip agree with the pyspec, at gloas, fulu, electra, deneb, capella, bellatrix, altair and phase0 | `StateMachine` | `getForkchoiceStore`, `Store.onTick`, `onBlock`, `onAttestation`, `onAttesterSlashing`, `getHead`, `getWeight`, `getProposerHead` and its seven tests, `validateGossipMessage` for blocks, attestations, aggregates and attester slashings with one `Seen`, `computeWeakSubjectivityPeriod`, `getCommitteeAssignment`, `createLightClientBootstrap`, `initializeLightClientStore`; at gloas also `onExecutionPayloadEnvelope`, `onPayloadAttestationMessage`, the empty and full node of every block, `shouldApplyProposerBoost`, `getPayloadStatusTiebreaker`, and the gossip of envelopes and payload votes | pyspec, same command stream | 8 x 1,000 | pass |
| a signer follows EIP-3076 (state machine) | `StateMachine` | `Interchange.checkBlock`, `checkAttestation`, `recordBlock`, `recordAttestation`, `importFile`, `toMinimal`, `limits`, `toJson`, `ofJson` | a model written from EIP-3076, and the definitions of a slashable pair on the full history | 1,000 | pass |
| a signer follows EIP-3076 (madhouse) | `Command` scenario, madhouse | the same | the same | 1,000 | pass |
| an integer of the interchange file | plain | `Interchange.readUInt64` | the rule of the EIP: decimal digits in a string, below 2^64 | 1,000 | pass |
| the light client store agrees with the pyspec, at electra, deneb, capella and altair (madhouse) | `Command` scenario, madhouse | `initializeLightClientStore`, `processLightClientUpdate`, `validateLightClientUpdate`, `applyLightClientUpdate`, `processLightClientStoreForceUpdate`, `isBetterUpdate`, `isValidLightClientHeader`, the generalized indices per fork | pyspec, same command stream, updates with true Merkle branches | 4 x 1,000 | pass |
| `is_better_update` at deneb and electra | plain | `isBetterUpdate` | pyspec | 2 x 1,000 | pass |
| `is_better_update` is a strict weak order | plain | `isBetterUpdate` | the laws of the order | 1,000 | pass |
| `get_custody_groups` | plain | `DataAvailability.getCustodyGroups` | pyspec | 1,000 | pass |
| `compute_columns_for_custody_group` | plain | `DataAvailability.computeColumnsForCustodyGroup` | pyspec | 1,000 | pass |
| `compute_subnet_for_attestation` | plain | `computeSubnetForAttestation` | pyspec, with its 64-bit overflow | 1,000 | pass |
| `compute_subnet_for_data_column_sidecar` | plain | `computeSubnetForDataColumnSidecar` | pyspec | 1,000 | pass |
| `compute_subscribed_subnets` | plain | `computeSubscribedSubnets` | pyspec | 1,000 | pass |
| the weak subjectivity period of phase 0 | plain | `phase0PeriodEpochs` | the formula of `weak-subjectivity.md` in `Nat` | 1,000 | pass |
| the weak subjectivity period of Electra | plain | `balanceChurnPeriod` | the Electra formula in `Nat`, with its 64-bit bounds | 1,000 | pass |
| `on_attestation` takes every vote that the pyspec takes, at fulu and phase0 | `StateMachine`, group `forkchoice: findings` | `Store.onAttestation` | pyspec | 2 x 1,000 | fails by design (finding 1) |

### The store and gossip machine

The transitions are one type, `Cmd`: `tick`, `ahead`, `block`, `again`, `chain`, `attest`, `slash`, and from Gloas `envelope` and `ptc`.
The model is the shape of the run: the clock and the slot of every block built so far.
A generator reads it to aim a block at the current slot, at the next one and at its parent's, and a vote at the slot before the current one.
The oracle builds each object with the pyspec, runs the pyspec handler, and answers with the steps it ran and a view of its store.
The driver runs the same steps on EthLib and compares the verdict of every step and the whole view after every command.

The view holds the head, the justified and finalized checkpoints, both unrealized checkpoints, the boost root, the proposer head with its seven tests, the weak subjectivity period of the head state, five committee assignments, the root of the bootstrap of the head, the clock, the number of blocks, the equivocators, every latest message and the weight of every block.

The anchor state has 16, 24, 32 or 64 validators, and a variant gives it unequal balances, a slashed validator or one that is not active yet.
A block may carry a wrong state root, a wrong proposer or an unknown parent, may be late, early or from the future, and may be sent again.
A vote may be mutated in thirteen ways: its target root, target epoch, block root, slot, committee index, the length and the content of its bits, its source, and from Electra its committee bits.
A slashing may be a double vote, a surround vote, not slashable, unsorted, with a repeated index, empty, or with an index out of range.
Every wire block, vote and slashing first goes through its gossip check on both sides, at a clock that may run ahead of the store by the edges of the 500 ms disparity, then through its handler.

At Gloas a block has a payload of its own and builds on the payload of its parent or without it, a `chain` reveals the envelope of most of its blocks, and the view holds the status of the head and the weights of the pending, the empty and the full node of every block.
An envelope may be mutated in five ways, and a payload vote may come from outside the committee, for another slot or for an unknown block.
The run of 1,000 sequences at gloas had 2,668 envelopes accepted and 598 refused, 232 payload votes accepted and 268 refused, and 3,987 views with a full head.

EthLib alone must also keep five invariants after every command: the finalized and justified epochs and the clock do not go back, the finalized epoch is at most the justified one, the head descends from the justified block, and a boost names a block of the current slot.

The final run of 1,000 sequences at each of the eight forks, with the 300 or so sequences of the findings group, reached this, as `FC_STATS=1` prints: 94,827 views compared, 26,949 blocks accepted and 8,873 refused, 36,459 votes from blocks, 1,748 wire votes accepted and 7,737 refused, 839 slashings accepted and 3,284 refused, 4,334 views with a justified epoch above 0 and 681 with a finalized one, 11,684 views of a forked tree, 7,080 with equivocators, 229 where the proposer head is the parent.
Gossip gave 24,581 accepts, 11,092 ignores and 149 rejects on blocks, 4,560, 10,954 and 2,077 on attestations, 3,976, 5,149 and 1,540 on aggregates, and 824, 259 and 3,040 on slashings.

The harness was checked with four mutants of the pyspec, set by `FC_MUTANT` (`tie`, `boost`, `newer`, `viable`): a tie that goes to the lesser root, a boost of one percent less, a latest message replaced at an equal epoch, and a voting source one epoch off.
Each failed within 300 sequences.

### The slashing protection machines

The model keeps two things: the data that the five conditions of EIP-3076 range over, as plain lists, and the full history of every message signed or imported.
After every request, EthLib must refuse exactly when a condition says refuse, hold exactly the records of the model, and never accept a message that is slashable with any message of the history.
An import follows Advice for Minimal Databases: per key, the greatest slot, the greatest source and the greatest target.
A file may hold records without a signing root, the same key in many entries, and records that are slashable with each other.
The `StateMachine` generator reads the model and aims slots and epochs within 2 of the records that exist, so repeats, double votes and both directions of a surround are common.
The `Command` scenario generates the same four commands blind.

### The light client scenario

The commands are `Update` and `Force`, each a type with a `Command` instance.
The oracle builds an update from a template state whose finalized root and next sync committee it sets, so that the finality branch and the committee branch are true proofs against the attested state root.
Seven mutations break a branch at its first or last node, drop a branch, or change a header.
The run of 1,000 sequences per fork processed 13,041 updates, 2,461 of them accepted, with 2,780 digests of a moved finalized header and 180 in a later sync committee period.
A mutant of the pyspec with the arguments of `is_better_update` swapped (`FC_MUTANT=better`) failed after 35 sequences and shrank to two updates of 22 and 21 signers, the two sides of the two thirds.

## Findings

### 1. `Store.onAttestation` refuses votes that `on_attestation` accepts (OPEN: documented and deliberate)

Definition: `EthLib/Consensus/ForkChoice/Handlers.lean:386`, the call of `checkAttestationCommittees`.

Shrunk counterexample at phase0, 32 validators, so one committee per slot:

```text
[Cmd.tick 6000, Cmd.attest 0 0 0 65535 5]
```

It is a vote at slot 0 for the anchor, by the whole committee 0, with `data.index` then raised to 1.
EthLib answers `the state transition fails: TransitionError.committeeIndexOutOfRange 1 1`.
The pyspec accepts it and records a latest message for each member.

The same holds for a vote whose bits do not have the length of its committee (`aggregationBitsLength 4 3`, at fulu: `[Cmd.chain 0 7 0 0, Cmd.chain 7 10 0 0, Cmd.attest 0 17 0 65535 4]`), and from Electra for a vote with `data.index != 0` (`attestationIndexNotZero 1`) or with a committee that has no attester.

The source, `fork-choice.md` at the pinned commit, as the pyspec has it:

```python
def on_attestation(store: Store, attestation: Attestation, is_from_block: bool = False) -> None:
    validate_on_attestation(store, attestation, is_from_block)
    store_target_checkpoint_state(store, attestation.data.target)
    # Get state at the `target` to fully validate attestation
    target_state = store.checkpoint_states[attestation.data.target]
    indexed_attestation = get_indexed_attestation(target_state, attestation)
    assert is_valid_indexed_attestation(target_state, indexed_attestation)
    update_latest_messages(store, indexed_attestation.attesting_indices, attestation)
```

Neither `validate_on_attestation` nor `get_indexed_attestation` bounds the committee index or the length of the bits; `process_attestation` and the gossip rules do.
EthLib's docstring says so: "Its committees must be those of its slot, with one bit for each member, as blocks require. ... Otherwise an index past the count of committees of its slot could name one of a later slot."
So the code and its docstring agree, and the code is stricter than the function of the source.
A node that follows the specification never hands such a vote to `on_attestation`: a vote from a block passed `process_attestation`, and a vote from the wire passed the gossip rules, which the machine above confirms reject each of these.
What would decide it: whether `onAttestation` is meant to be the function of `fork-choice.md` or a hardened one.
If the former, this is a BUG of the kind "an input refused that the source accepts"; the docstring reads as the latter.

To see it again:

```bash
ONLY="every vote" lake exe forkchoice-property 300
```

The main machine leaves these votes out of `on_attestation` (the oracle's `shape_ok` writes the shape rules of `process_attestation`), and still sends them through gossip.

### 2. Gossip: an aggregate whose bits have another length than a seen one (not a bug)

At phase0 the pyspec raised `ValueError` in `is_non_strict_superset`, whose `zip(..., strict=True)` takes no two lengths, where EthLib said `ignore (already seen aggregate for this epoch and aggregator)`.
EthLib's `isNonStrictSuperset` says that earlier bits of another length cover nothing, and `p2p-interface.md` gives no verdict for the case, since a later rule rejects the wrong length.
The driver now takes an exception of the pyspec that is no gossip verdict as undefined there, and requires only that EthLib does not accept.
`FC_DEBUG=1` prints each such case.

### 3. HARNESS and pyspec artifacts

- A harness bug gave 257 against EthLib's 256 for the weak subjectivity period at gloas: the oracle chose the phase 0 formula by the absence of `get_balance_churn_limit`, which Gloas removes; fixed.
- `compute_weak_subjectivity_period` of the pyspec raises `TypeError` before Electra (`Unsupported operand type(s) for >: 'Slot' and 'Gwei'`), so the oracle computes its text in plain integers there.
- `is_data_available` of the pyspec at Deneb and Electra fails on the empty batch, in its KZG wrapper; the oracle answers true for a block without commitments.
- The pyspec modules have every fork epoch in the far future; the oracle and the driver both set the epochs of the forks up to the one under test to 0.
- A driver bug: with `ONLY` unset the filter dropped every property; fixed.
- In every state of the machine the weak subjectivity period is 256: the validator sets are too small to add an epoch.
  The two pure properties of the period cover the arithmetic instead.

## Not covered

- Gloas in depth: the machine runs at gloas, but no block carries payload attestations, bids of builders, execution requests or blobs, so `notifyPtcMessages`, the payload timeliness and data availability majorities (`ptcMajority`, `shouldExtendPayload`) with more than a few votes, `HonestBuilder.lean` and the gossip of bids and proposer preferences are not reached.
  A run at gloas rarely justifies an epoch, since a `chain` fills fewer votes there.
- Heze: the inclusion list store, `onInclusionList`, `InclusionList*.lean` and its gossip.
  The pyspec has it, and the oracle would need one more builder.
- Fast confirmation (`FastConfirmation.lean`) and optimistic sync (`Optimistic.lean`, `OptimisticSync.lean`): the pyspec has both, and they would be further fields of the view.
- Gossip of sync committee messages and contributions, voluntary exits, proposer slashings, BLS changes, blob and column sidecars: no command builds them.
- Signatures: BLS is off on both sides, so no signing root or domain is checked here, and `isAggregator` always selects in the minimal preset (the modulo is 1).
- `createLightClientUpdate` and the upgrade functions of `LightClient/Upgrade.lean`; only the bootstrap of a full node is compared.
- A light client header of an earlier fork inside a later store, since every fork epoch is 0.
- `HonestProposer.lean` (the Eth1 vote, `computeOnChainAggregate`, `getExecutionRequests`), `HonestAggregation.lean`, the signatures of `HonestValidator.lean`.
- The slashing protection model was not checked with a mutant, as the store and the light client were.
- `ReqResp/`: the validity rules have no executable reference; a model from `p2p-interface.md` would be a second reading of the same prose.
- `History/Era.lean`, `PqKeys/`, `BeaconApi/`, `BuilderApi*`, `RelayApi.lean`: not looked at.
- Sidecar verification and the matrix of `DataAvailability/Column.lean`: slow (KZG), and no block here has a blob.
- The complete strategy of EIP-3076 beyond what `Interchange` holds: EthLib imports by the minimal strategy only, and the official interchange test files were not run.
- The mainnet preset: every run is minimal.

## Notes on lean-hedgehog

What worked well:

- `StateMachine` fits a differential test against another process: the model is the bookkeeping that a generator and a precondition need, and `applySut` in `TestT IO` talks to the oracle.
  The model state after the transition is exactly what a command needs to send absolute times.
- Shrinking of sequences is good.
  A disagreement found after 40 sequences shrank to `[chain 0 1 0 0, attest 0 0 1 65535 0]`, and the four mutants shrank to two or three commands each.
- `Gen.frequency` and `Gen.element` make edge-aimed generators short, and `Gen.zip` kept the two epochs of a vote shrinking independently.
- `annotate` inside `applySut` gives a readable trace of the steps before the failing one.
- `Command` instances read well and a new command touches nothing else.

What was awkward or missing:

- `Command.apply` gets no context, only `build` does.
  A system under test in another process is reached through a handle, so every command structure carries the oracle that `build` copied from the context (`LightClient.lean`, `Context`).
  An `apply : χ → κ → σ → TestT m σ` would remove that.
- `Command.build` gets no state, so a command cannot aim at what exists.
  The light client commands draw their slots blind; the first version accepted 65 of 901 updates until the command moved the clock itself.
  The slashing scenario finds less per sequence than the `StateMachine` whose generator reads the model.
- `scenario` starts from `default` and has no place for setup in `m`.
  The store of the light client needs the oracle, so the state holds an `Option` and every `apply` starts with a `ready` step.
  It also fixes the length at 1 to 15 commands; `StateMachine.property` takes a range, `scenario` does not.
- `scenario` needs `(σ := ...)` when the state type has a parameter; the `outParam` is not found through `Command.gen` alone.
- A `StateMachine` whose reference is external runs the model twice in spirit: `Model.apply` must be pure, so the oracle cannot be the model, and the model must predict the shape of what the oracle does.
  The oracle had to be made total for that (a `chain` always ticks and always appends the same number of entries).
- No `classify`, `cover` or `collect`.
  How often a run reached finality or an accepted slashing had to be counted in the oracle and printed at exit.
  This was the most missed feature: without it a passing state machine says little.
- `forAll` of a sequence prints every command with its full constructor path (`ForkChoiceProperty.Cmd.chain 0 3 0 0`), and the report of a failing `===` on a long string prints both sides whole; a diff of the two would help.
- A failing property that throws from `initSut` ends the whole run with `uncaught exception` instead of failing the property.
- `recheck size seed` is printed as `recheck 39 ⟨…⟩ <property>`; there is no way to pass it to a driver built on `checkGroup` without writing code.

No bug of the library itself was met.

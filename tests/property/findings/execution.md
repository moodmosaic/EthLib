# The execution chain: what the property tests found

The driver is `Property/Execution.lean`, with its modules under `Property/Execution/`.
The oracle is `oracle/execution.py`, and `oracle/requirements-execution.txt` lists what it needs.

    cd tests/property
    lake build execution-property
    lake exe execution-property 1000

The scope is `EthLib/Execution/` without `Evm/`, `Fees/`, `Proofs/` and `Exports/`.
The main reference is execution-specs 2.20.0 (EELS), which has every fork from Frontier to BPO2.
It has no Glamsterdam, so round 1 compared no rule that starts there.
Round 3 adds the branch `forks/amsterdam` of execution-specs for the forks after BPO2.

No property found a place where EthLib computes another value than its source.
One finding stands: EthLib refuses the answer that go-ethereum gives for a slot of an account with no storage, a case that EIP-1186 does not define.
Upstream has since fixed it, in pull request #3405 for issue #3386.
This branch is not yet rebased on that fix, so the two properties of the finding still fail here.
Three places where EthLib and the reference decode differently, with the same verdict on the transaction, are listed as notes.

## What was tested

This table is of round 1: each row ran 2,000 cases in its last run then, unless it says otherwise.
Round 3 changed the generator of nearly every row and added 12 properties: see "Round 3: the coverage audit" below.

| Property | EthLib definitions | Reference | Result |
| --- | --- | --- | --- |
| a transaction as bytes is the reference's | `decodeTransaction`, `transactionHash`, `checkChainId`, `recoverSender`, `legacyRecovery`, `validS`, `intrinsicGas`, `calldataFloor`, `validateTransaction`, `checkContents` at 20 forks | EELS `decode_transaction`, `recover_sender`, `calculate_intrinsic_cost`, `validate_transaction`; EIP-1559, 4844, 7594, 7702 for the rules EELS keeps in `check_transaction` | pass |
| a transaction of eth-account reads back | `decodeTransaction`, `encodeTransaction`, `transactionHash`, `signingInput` and the five signing hashes, `recoverSender` at four forks, `checkChainId`, `authorizationHash`, `recoverAuthority`, the low-`s` rule of EIP-2 | eth-account 0.14.0 | pass |
| the sender of a transaction passes the rules of its EIPs | `checkSender`, `Transaction.maxGasFee`, `effectiveGasPrice`, `isValidDelegation` | a model in `Nat` from EIP-1559, 3607, 4844, 7702 | pass |
| the root of a trie is the reference's | `trieSet`, `Trie.root`, plain and secured | EELS `trie.root` | pass |
| the proof of a key is py-trie's | `getProof`, `verifyProof` | py-trie 4.0.0 `get_proof`, and the entries themselves | pass |
| an accepted proof does not lie | `verifyProof` on changed proofs | the entries themselves, and py-trie `get_from_proof` | pass |
| state machine: a trie under writes, beside py-trie (`StateMachine`) | `trieSet`, `trieGet`, `Trie.root` | py-trie, which rewrites its nodes at each write; a list of entries | pass |
| the logs bloom is the reference's | `logsBloom`, `Bloom.ofLogs`, `Bloom.mayContain` | EELS `logs_bloom` and eth-bloom, which must agree | pass |
| a header as bytes is the reference's | `Codec (Header fork)`, `Header.hash`, `Header.fieldCount` at 20 forks | EELS `Header` | pass |
| a header after its parent is valid as in the reference | `checkHeader`, `headerChecks`, `expectedBaseFeeAcross`, `expectedExcessBlobGas`, `expectedDifficulty`, `checkGasLimitAcross` at 20 forks | EELS `validate_header`, the seal patched out | pass |
| the ommers of a block are valid as in the reference | `validateOmmers`, `checkOmmerHeader`, `ommersItem` at five forks | EELS `validate_ommers`, the seal patched out | pass |
| a receipt as bytes is the reference's | `decodeReceipt`, `Codec (Receipt fork)`, `Outcome` at 20 forks | EELS `decode_receipt`, `Receipt` | pass |
| the difficulty of a block is the reference's | `blockDifficulty`, `bomb`, `bombDelay`, `timeFactor` at 13 forks | EELS `calculate_block_difficulty` | pass |
| the rewards of a block are the reference's | `blockReward`, `minerReward`, `ommerReward` | EELS `BLOCK_REWARD`; Yellow Paper 11.3 in `Nat` | pass |
| the requests hash is EIP-7685's | `requestsHash` | hashlib, from the text of EIP-7685 | pass |
| the deposit request of a log is the reference's | `depositRequestOfEvent` | EELS `extract_deposit_data` | pass |
| the root of a list is the reference's | `withdrawalsRoot`, `indexedRoot`, `Codec Withdrawal` | EELS trie of `rlp(index)` | pass |
| the DAO Fork moves the accounts of EIP-779 | `DAO_ACCOUNTS`, `DAO_RECOVERY`, `applyDaoFork` | EELS `dao.py`; sums in `Nat` | pass |
| state machine: the tracker reads as a model that copies its state (`StateMachine`) | `TransactionState`: every read and write, `restoreTxState`, `incorporateTxIntoBlock`, `BlockState.applyChanges`, at 7 forks | a model here from the text of `state.py`, one flat state copied at each snapshot | pass |
| an answer of eth_getProof holds exactly when it is true | `AccountProof.ofState`, `verify`, `verifyAccount`, `verifySlot`, `stateRoot`, `storageRoot` | the model of the tracker; one field changed must be refused | pass |
| scenario: the tracker beside state.py, at 7 forks (`Command`, madhouse) | the same operations, and `stateRoot` at the end of each transaction | EELS `state.py` at Tangerine Whistle, Spurious Dragon, Istanbul, London, Paris, Cancun, Osaka | pass, 2,000 sequences each |
| OPEN: the empty proof shows absence in the empty trie | `verifyProof` | py-trie | fails, 100 cases |
| OPEN: go-ethereum's answer for a slot of an empty storage holds | `AccountProof.verify` | go-ethereum `GetProof` | fails, 100 cases |

The generators were checked before they were trusted.
With `EXECUTION_ORACLE_STATS=1` the oracle counts its answers.
The reference accepts about 59% of the transactions as bytes, 56% of the headers, 42% of the header pairs, 54% of the receipts, 37% of the deposit logs and 55% of the ommer lists.
So each acceptance test has both verdicts in number.

## Findings

### OPEN: the proof of a key in the empty trie

Status in round 3: upstream fixed this in pull request #3405, for issue #3386.
This branch is not yet rebased on the fix, so both properties still fail here, in the group that must fail.
After the next rebase they move to the passing groups.

Classification: BUG of interoperability, by the second check below; OPEN by the text of EIP-1186 alone.
The source that the module cites, EIP-1186, does not define the proof of the empty trie, so EthLib does not deviate from its text.
EthLib is consistent with itself and with its docstring.
But `AccountProof` is "the check of an account proof, the answer of `eth_getProof`", and it refuses the true answer that go-ethereum gives for any slot of an account that exists and has no storage.
Every externally owned account is such an account.

Second check, 2026-11-19: `internal/ethapi/api.go` of go-ethereum was fetched at `master` and read.
Lines 414 to 439 open the storage trie only when the storage root is neither the root of the empty trie nor zero, and otherwise answer each key with `StorageResult{outputKey, &hexutil.Big{}, []string{}}`.
The fixture `tests/eth_getProof/get-account-proof-missing-account.io` of execution-apis has the same shape, `"proof": []`, for the slot of an address with no account.
EthLib does not read the slot proofs of an absent account, so it accepts that fixture; it is the account that exists and has no storage that it refuses.
No fixture of execution-apis asks for a slot of such an account, which is how the suite of EthLib did not meet it.

- Definition: `verifyProof` (`EthLib/Execution/Trie/Proof.lean:181`), through `resolve` (line 124), and so `AccountProof.verifySlot` (`EthLib/Execution/State/AccountProof.lean:229`).
- Counterexample: the root `56e81f17…b421` of the empty trie, any key, and the proof with no node.
- EthLib: `verifyProof` gives `Except.error (ProofError.missingNode …)`.
  `AccountProof.verify` gives `AccountProofError.slot 0 (missingNode …)` for an account with a balance, no storage, and a slot whose proof has no node.
  Both were run, by the two properties of the group `execution: findings`.
- EthLib builds `[0x80]` for the empty trie (`getProof`), and accepts only that.
- go-ethereum, read at `master`, `internal/ethapi/api.go`, `GetProof`: the storage trie is opened only `if storageRoot != types.EmptyRootHash && storageRoot != (common.Hash{})`, and otherwise each slot is answered by

      if storageTrie == nil {
          storageProof[i] = StorageResult{outputKey, &hexutil.Big{}, []string{}}
          continue
      }

  So `storageProof[i].proof` is the empty array `[]`, with the value `0x0`, for every slot of an account with no storage.
  This was read from the source, not from a running node.
- py-trie 4.0.0 agrees with go-ethereum: `get_proof` of the empty trie is `()`, and `get_from_proof(root, key, ())` is the absent value.
- EIP-1186 says of `proof`: "Array of rlp-serialized MerkleTree-Nodes, starting with the storageHash-Node, following the path of the SHA3 (key) as path."
  It has no example of an empty trie, and no sentence on it.
  The Yellow Paper (Appendix D) gives the empty trie no node: its root is the hash of the empty byte string, which favours the empty array.
  The docstring of `verifyProof` says "The root is always the hash of the root node's encoding, so the proof starts with that encoding", so the behaviour is deliberate.
- Why it matters: every externally owned account has the empty storage root.
  `AccountProof.verify` refuses the answer of go-ethereum for any slot of such an account, although the answer is true.
- What would decide it: whether `AccountProof` means to check the answers of clients (its docstring says "The answer of `eth_getProof`").
  If it does, `verifyProof` should take the proof with no node against the root of the empty trie, and keep taking `[0x80]`.

      lake exe execution-property 100 2>&1 | sed -n '/findings/,$p'

### HARNESS: two slots of a trie with one leaf

The property of `eth_getProof` first swapped the proofs of two slots and expected a refusal.
A storage of one leaf proves every key by that one node, so the swap changed nothing and the answer stayed true.
The swap now applies only when the two proofs differ.

## Notes, not findings

- The nonce of a set code transaction.
  EELS types it on 64 bits, so `decode_transaction` refuses `2^64` and more.
  EthLib reads it and `validateTransaction` then refuses it by EIP-2681.
  The transaction is invalid either way, and the driver maps the first to the second.
- The gas limit and the fees.
  EELS types `gas`, `gas_price`, `max_fee_per_gas` and `max_priority_fee_per_gas` as unbounded integers.
  EthLib refuses `2^256` and more at decoding, as the Yellow Paper (4.2) bounds each.
  No balance pays for such a transaction, and the oracle maps the second to the first.
- The chain of a typed transaction.
  EELS `recover_sender` does not compare `tx.chain_id` with the chain; EthLib's `checkChainId` does, as EIP-2930 asks.
  The oracle adds that rule.
- py-trie 4.0.0 raises `ValidationError` on a key that ends inside an extension, in `__contains__` and in `get_from_proof`.
  This is a defect of the reference, found by the state machine, and the driver works around it.
- `getProof` of the empty trie gives `[0x80]` where py-trie gives no node: the open finding above, seen from the builder.

## Not covered

This is the list of round 1.
Round 3 covers three of its items, as marked, and the list that stands now is "Not covered after round 3".

- Glamsterdam and Hegotá: EIP-2780, 7976, 7981, 8037, 8038, 7954, 7928 (block access lists), 8246, 8282.
  No reference was at hand; `Blocks/BlockAccessList.lean` and `Blocks/AccessListBuilder.lean` were not tested.
  Round 3: the bytes of a transaction, of a header and of a receipt at Glamsterdam are compared with the branch `forks/amsterdam` of the reference.
- `Transactions/Process.lean`, `Transactions/Settlement.lean` beyond the price, `Blocks/Transition.lean`, `Blocks/SystemCall.lean`, `Blocks/Genesis.lean`: they run the EVM, and need whole blocks beside EELS `state_transition`.
  This is the largest gap, and the next round should start there, with the fixtures of `ethereum/tests` or a block builder in the oracle.
- `checkInclusion` as a whole: only `checkSender` and the rules without state were compared; the order of its checks and `checkBlockGas` were not.
- `applyAuthorizations` and `delegate`: only `recoverAuthority` and `authorizationHash` were compared.
- `Blocks/ProofOfWork.lean` (Ethash): too slow for a property, and it needs the cache of an epoch.
- `Transactions/Network.lean` (blobs with their proofs): it needs KZG, which another layer tests.
- `Trie/Range.lean` (`verifyRange`, the range proofs of snap): no reference; its boundary cases deserve a model.
  Round 3: covered, by "a range of a trie is accepted exactly when it is true".
- A proof for a trie that is not canonical (a leaf with an empty value, a branch with one child, a child of fewer than 32 bytes held by its hash): a forged root is needed, and EIP-1186 does not say what to do.
  Round 3: covered, by the two properties of tries built node by node.
- `History/Era1.lean`: it needs a writer of era1 files written apart from EthLib (e2store, Snappy frames, the SSZ root).
- `Network/` (eth and snap messages) and `Rpc/`: only read; the message identifiers agree with devp2p.
  Their codecs stand on the RLP layer, which another driver tests.
- `daoExtraDataValid` and the rule of the DAO Fork on the extra data.
- `payRewards` and `processWithdrawals` on a state: only their amounts and the tracker under them.

## Notes on lean-hedgehog, round 1

These notes are of lean-hedgehog 0.2, before the port.
Version 0.3.0 answers several of them: the context in `apply`, the setup and the range of `scenario`, `Property.lift`, coverage, and the replay of a case from the environment.
The notes on 0.3.0 are at the end of this file.

What worked well:

- `Gen.frequency` over hand-picked edges, with `Gen.element`, made near-valid inputs easy: the first two runs of the transaction property each stopped at a real difference of typing between EthLib and EELS.
- Shrinking of a composed generator is good without any work.
  A transaction of 300 bytes with the nonce `2^64` shrank in 29 steps to 40 bytes where only the nonce was not zero.
  A trie of 24 writes shrank to the three writes that made py-trie raise.
- `StateMachine` fits a closed set of operations well: `transitions` reads the model state, so "write to a key that is set" and "roll back only with an open snapshot" are one line each, and `preconditions` keeps shrunk sequences valid.
  A sequence of 60 operations on the tracker shrinks to one or two.
- `Model.sequence` is usable alone: the property of `eth_getProof` draws a sequence from the model of the tracker and builds a state from it.
- `forAllWith` kept reports readable where `Repr` of a byte array is noise.
- The report line `recheck <size> <seed>` is short and exact.

What was awkward or missing:

- `Command.apply` does not receive the context `χ`, only `build` does.
  A command that drives a system through a handle (here the oracle and the fork) must copy the context into every command value.
  All 15 command types here extend one structure that holds it.
- `scenario` starts from `default` and has no hook to set up or tear down.
  The oracle's twin state is created by a `started` flag that every command checks first.
  `StateMachine.initSut` has this; `scenario` wants an `init : χ → m σ`.
- `scenario` fixes the length of a madhouse sequence at 1 to 15, with no parameter.
  Snapshots nested three deep with writes between them need more; `StateMachine.property` takes a range, and `scenario` should too.
- A `Command` instance is seven lines of which five repeat for each type (`check`, `apply`, `label` here are the same for all).
  A helper that builds an instance from a generator and one `apply` would cut the 15 instances to 15 lines.
- `StateMachine` over `Id` does not fit in `checkGroup` beside `Property IO`; there is no `Property.lift`.
  The pure tracker machine is declared in `IO` for that reason alone.
  `Support.pureIO` does this for `PropertyM Unit`, and the library could offer it for a `Property Id`.
- No `classify`, `cover` or `label` (NEWS lists them as not ported).
  Whether a generator of near-valid inputs is accepted half the time is the first thing to know, and it had to be counted outside: by `Gen.sample` in a scratch file and by a counter in the oracle.
  The first generator of transactions was refused 71% of the time, which no report showed.
- `Gen.sample` runs at the fixed size 30, with no argument for the size.
- A name collision: `open Hedgehog` brings `Hedgehog.Log` into scope, which is ambiguous with any `Log` of the code under test (`Execution.Blocks.Log` here).
- `recheck` needs the property as a Lean term, so a driver must be edited and rebuilt to replay a failure of `lake exe`.
  A `checkGroup` that reads a size and a seed from the arguments or the environment would do.
- After `bind`, a shrink of the first value redraws the second (USAGE says so).
  In practice the shrunk transactions were still minimal, because the failing field kept failing when redrawn; no case stopped short.

No bug of the library was hit.
One stale-build trap is worth a line in USAGE: `lake env lean scratch.lean` reads the built `.olean` of an imported module, so a generator edited without `lake build` is sampled in its old form.

## Round 3: the coverage audit

The properties above were written before lean-hedgehog had coverage, and all of them passed.
This round labelled every case of every property, read the shares, repaired the generators, and then applied the rule of the round: every general function at every value of its parameters.

    cd tests/property
    lake build execution-property
    lake exe execution-property 1000
    HEDGEHOG_ONLY="trie,proof,range" lake exe execution-property 5000

The driver now has 39 properties that must pass and 2 that must fail.
The last runs were on this branch, with both references installed:

- 1,000 cases, twice: the 39 properties passed and the two of the finding failed as they must, with the exit code 0.
  A run took five to eight minutes on a machine that ran other drivers.
- 100 cases, the default, three times: the same.
- 5,000 cases of 14 properties: the tries, their proofs and ranges, hex-prefix, a signed transaction, the rules that read no state, the bloom, and the first header of a fork.

No property found a place where EthLib computes another value than its source.
The finding of round 1 stands on this branch, and upstream has fixed it: see "The finding of round 1" below.
Three notes are new, and none is a deviation from a source.

So a bug that remains is not in what these properties reach.
What they do not reach is listed under "Not covered after round 3".

### Step 1: the shares before any change to a generator

Each property ran 1,000 cases with its generator as round 1 left it.
A share is of the 1,000 cases; in a state machine or a scenario it is the share of sequences that hold such a step.
The last column holds the classes under 3%, which a passing property did not in effect test.

| Property | Classes at 3% or more | Classes under 3% |
| --- | --- | --- |
| a transaction as bytes is the reference's | call data with a byte 56.3%; form: legacy 54.4%; verdict: no transaction, decoding 26.9%; verdict: a transaction, invalid, insufficientGas 25.1%; legacy: signs a chain (EIP-155) 21.3%; fork: Byzantium to Muir Glacier 20.6%; sender: recovered 17.6%; form: type 1 15.5%; fork: Fusaka to BPO5 14.4%; fork: Homestead to Tangerine Whistle 13.9%; gas: further above the least 13.8%; fork: London to Gray Glacier 13.6%; gas: further below the least 13.1%; verdict: no transaction, unsupportedType 12.5%; legacy: signs no chain 12.5%; form: type 2 12.4%; a contract creation 12.2%; gas: one below the least 12.0%; gas: the least 11.8%; verdict: a transaction, valid but for its signature 11.3%; an access list with an entry 10.1%; gas: one above the least 9.9%; verdict: a transaction, invalid, nonceOverflow 8.7%; form: a type that the fork does not have yet 8.2%; verdict: a transaction, valid but for its chain 7.8%; form: type 3 7.0%; the floor of EIP-7623 is above the intrinsic gas 6.5%; form: type 4 6.4%; fork: Berlin 6.4%; fork: Spurious Dragon 6.2%; legacy: signs a chain before Spurious Dragon 5.5%; fork: Frontier 5.5%; fork: Paris 5.3%; fork: Pectra 5.1%; fork: Dencun 5.1%; verdict: a transaction, valid, with a sender 5.1%; form: another first byte 4.3%; legacy: another v 4.3%; fork: Shapella 3.9%; valid with a sender: type 0 3.7% | sender: recovered, on another chain 2.2%; authorizations: 0 2.2%; blobs: 1 to 6 2.2%; verdict: a transaction, invalid, priorityFeeGreaterThanMaxFee 2.0%; valid with a sender: type 1 0.9%; authorizations: 1+ 0.8%; blobs: 0 0.4%; valid with a sender: type 2 0.3%; verdict: a transaction, invalid, noBlobData 0.2%; verdict: a transaction, invalid, emptyAuthorizationList 0.2%; verdict: a transaction, invalid, invalidBlobVersionedHash 0.2%; blobs: 7+ 0.1%; valid with a sender: type 4 0.1%; valid with a sender: type 3 0.1%; init code above the limit of EIP-3860 0.0% |
| a transaction of eth-account reads back | call data with a byte 93.2%; chain: 2^63 or more 47.3%; an access list with an entry 32.0%; type 1 21.5%; type 0 20.7%; type 2 19.8%; type 4 19.1%; type 3 18.9%; legacy: signs a chain (EIP-155) 17.2%; an authorization for a chain 14.2%; a contract creation 12.9%; an authorization for every chain 7.4%; legacy: signs no chain 3.5% | - |
| the sender of a transaction passes the rules of its EIPs | nonce: the sender's 79.5%; code: other 57.0%; balance: exact 40.8%; the tip is capped by the fee 39.6%; verdict: refused, senderNotEoa 38.3%; code: none 30.8%; balance: more 30.0%; type 0 28.0%; type 2 25.6%; type 1 23.3%; type 3 23.1%; verdict: refused, insufficientBalance 22.8%; fork: Byzantium to Muir Glacier 21.9%; balance: one wei short 19.4%; verdict: may send 18.4%; fork: Homestead to Tangerine Whistle 15.3%; fork: London to Gray Glacier 15.2%; fork: Fusaka to BPO5 12.9%; code: a delegation indicator 12.2%; verdict: refused, nonceTooLow 11.8%; nonce: below the sender's 11.8%; balance: further short 9.8%; a delegation indicator before Pectra 9.6%; the tip is paid whole 9.1%; verdict: refused, nonceTooHigh 8.7%; nonce: above the sender's 8.7%; fork: Frontier 5.9%; fork: Shapella 5.7%; fork: Dencun 5.7%; fork: Berlin 5.2%; fork: Pectra 4.9%; fork: Paris 4.6% | fork: Spurious Dragon 2.7%; a delegation indicator from Pectra 2.6% |
| the root of a trie is the reference's | root: a branch 59.2%; trie: a node held by hash 58.3%; secured 46.6%; writes: a key written twice 41.4%; keys: 3 to 8 39.1%; trie: a key is a prefix of another 27.4%; trie: a branch with a value 27.4%; trie: a node held inside its parent 27.3%; trie: nodes held both ways 24.6%; trie: an extension 21.3%; keys: 0 21.2%; root: no node 21.2%; writes: a delete of a key that is set 19.1%; keys: 1 17.8%; root: a leaf 17.8%; keys: 2 11.3%; keys: 9 or more 10.6% | root: an extension 1.8% |
| the proof of a key is py-trie's | proof: 1 node 68.7%; root: a branch 57.3%; trie: a node held by hash 55.7%; the key is absent 53.8%; trie: a key is a prefix of another 51.2%; trie: a branch with a value 51.2%; trie: a node held inside its parent 51.0%; path: through a branch with a value 46.5%; the key is set 46.2%; trie: nodes held both ways 46.0%; key: 1 to 4 bytes 39.8%; key: empty 39.5%; keys: 3 to 8 36.3%; trie: an extension 35.6%; path: into a node held by hash 31.3%; path ends at: the leaf of the key 30.3%; keys: 0 21.3%; root: no node 21.3%; path ends at: the empty trie 21.3%; key: 32 bytes or more 20.7%; proof: 3 nodes or more 20.3%; path ends at: the leaf of another key 18.7%; keys: 1 18.0%; root: a leaf 18.0%; path: through an extension 17.1%; path ends at: the value of a branch 15.9%; path: into a node held inside its parent 15.8%; keys: 2 12.9%; keys: 9 or more 11.5%; proof: 2 nodes 11.0%; path ends at: an empty slot of a branch 6.5%; path ends at: an extension that the key leaves 4.2%; root: an extension 3.4%; path ends at: a branch with no value 3.1% | - |
| an accepted proof does not lie | root: a branch 59.8%; trie: a node held by hash 58.1%; trie: a key is a prefix of another 53.7%; trie: a branch with a value 53.7%; trie: a node held inside its parent 53.7%; the proof is changed, and not the proof of the key asked 52.5%; trie: nodes held both ways 49.0%; path: through a branch with a value 48.9%; the proof is the proof of the key asked 47.5%; key: empty 43.4%; keys: 3 to 8 41.6%; trie: an extension 38.8%; key: 1 to 4 bytes 38.0%; changes: 2 35.9%; EthLib: refuses, hashMismatch 32.9%; changes: 0 32.5%; changes: 1 31.6%; path: into a node held by hash 30.8%; EthLib: accepts, the key is absent 27.7%; path ends at: the leaf of the key 24.7%; path ends at: the leaf of another key 21.3%; keys: 0 20.4%; root: no node 20.4%; path ends at: the empty trie 20.4%; change: a node repeated 20.4%; change: a node dropped 20.0%; EthLib: accepts, the key is set 19.8%; change: the tail of another proof 19.3%; change: a byte 19.1%; key: 32 bytes or more 18.6%; change: a node rewritten 18.2%; path ends at: the value of a branch 17.2%; path: through an extension 17.0%; keys: 1 16.8%; root: a leaf 16.8%; path: into a node held inside its parent 15.2%; keys: 2 10.8%; keys: 9 or more 10.4%; EthLib: refuses, unusedNodes 10.0%; EthLib: refuses, missingNode 9.6%; path ends at: an empty slot of a branch 6.8%; path ends at: an extension that the key leaves 5.3%; path ends at: a branch with no value 4.3%; root: an extension 3.0% | accepted by EthLib alone 0.1%; accepted by both, a changed proof 0.0% |
| state machine: a trie under writes, beside py-trie | write: a new key 94.6%; write: a delete of no key 76.1%; write: a new value of a key that is set 72.9%; write: a delete of a key that is set 70.9%; a delete leaves its branch, or the trie had none 61.7%; a write to a trie where a key is a prefix of another 40.8%; a write to a trie with a branch with a value 40.8%; a delete turns a branch into a leaf 39.6%; a write to a trie with nodes held both ways 34.8%; a delete turns a branch into an extension 6.6% | reaches 9 keys or more 0.1% |
| the logs bloom is the reference's | logs: 0 41.6%; distinct entries: 0 41.6%; a log with no topic 36.2%; logs: 2+ 35.3%; an entry outside the seven fixed ones 34.6%; distinct entries: 1 to 3 32.8%; a log with one topic 30.3%; a log with two topics or more 26.1%; distinct entries: 4 to 8 23.6%; logs: 1 23.1%; an entry twice 21.7% | distinct entries: 9+ 2.0%; a log with four topics 0.2% |
| a header as bytes is the reference's | form: the count of fields of the fork 90.6%; verdict: a header 60.6%; verdict: no header, inField 30.0%; a header with a base fee 28.6%; fork: Byzantium to Muir Glacier 17.8%; fork: Homestead to Tangerine Whistle 17.7%; a header with a number of 2^64 or more 16.7%; fork: London to Gray Glacier 15.8%; a header with a withdrawals root 14.6%; fork: Fusaka to BPO5 14.6%; a header with blob gas 12.2%; a header with a requests hash 10.8%; verdict: no header, wrongFieldCount 9.4%; form: more fields 6.7%; fork: Spurious Dragon 6.1%; fork: Berlin 5.9%; fork: Frontier 5.0%; fork: Paris 4.7%; fork: Shapella 4.3%; fork: Pectra 4.3%; fork: Dencun 3.8% | form: fewer fields 2.7% |
| a header after its parent is valid as in the reference | parent gas: below the target 53.0%; gas limit: the parent's 49.0%; parent gas: above the target 43.1%; verdict: valid 42.7%; gas limit: below the parent's 25.9%; gas limit: above the parent's 25.1%; valid, before London 24.2%; fork: Byzantium to Muir Glacier 20.4%; fork: Homestead to Tangerine Whistle 15.8%; fork: London to Gray Glacier 15.4%; fork: Fusaka to BPO5 15.0%; verdict: invalid, invalidGasLimit 15.0%; verdict: invalid, gasUsedAboveLimit 9.3%; valid, from Dencun 8.9%; verdict: invalid, wrongNumber 7.2%; valid, London to Gray Glacier 6.5%; fork: Pectra 6.2%; verdict: invalid, timestampNotAfterParent 5.8%; fork: Spurious Dragon 5.5%; verdict: invalid, wrongDifficulty 5.1%; verdict: invalid, wrongBaseFee 5.0%; fork: Dencun 4.9%; fork: Frontier 4.6%; fork: Berlin 4.5%; fork: Shapella 4.2%; parent gas: at the target 3.9%; fork: Paris 3.5%; valid, Paris and Shapella 3.1% | verdict: invalid, wrongParentHash 2.5%; verdict: invalid, wrongExcessBlobGas 2.5%; verdict: invalid, extraDataTooLong 1.9%; verdict: invalid, nonzeroNonce 1.2%; verdict: invalid, nonzeroDifficulty 0.9%; verdict: invalid, genesisNumber 0.5%; verdict: invalid, wrongOmmersHash 0.4% |
| the ommers of a block are valid as in the reference | pick: a fresh ommer in range 73.7%; verdict: valid 59.7%; valid, with an ommer 45.8%; ommers: 1 41.0%; ommers: 2 34.1%; fork: london 22.0%; fork: frontier 21.6%; fork: homestead 19.3%; fork: byzantium 18.6%; fork: gray_glacier 18.5%; valid, with two ommers 16.3%; ommers: 0 15.5%; pick: a wrong difficulty 10.9%; pick: an ommer of a recent block 10.8%; pick: a block of the chain 9.8%; ommers: 3 9.4%; verdict: invalid header, wrongDifficulty 9.3%; verdict: invalid, wrongOmmersHash 9.1%; pick: a fresh ommer out of range 6.6%; verdict: invalid, ommerInChain 6.1%; verdict: invalid, tooManyOmmers 5.9% | verdict: invalid, wrongAge 2.9%; verdict: invalid, ommerAlreadyIncluded 2.0%; verdict: invalid, duplicateOmmer 2.0%; verdict: invalid, numberOutOfRange 1.8%; verdict: invalid, parentMissing 1.2% |
| a receipt as bytes is the reference's | form: legacy 54.1%; verdict: no receipt, inField 41.9%; logs: 0 30.7%; verdict: a receipt with status 0 21.6%; fork: Byzantium to Muir Glacier 19.3%; verdict: a receipt with status 1 19.1%; form: type 1 16.4%; fork: London to Gray Glacier 15.8%; form: type 2 15.7%; a log with a topic 15.6%; fork: Fusaka to BPO5 15.1%; fork: Homestead to Tangerine Whistle 14.8%; logs: 1 14.2%; verdict: a receipt with a state root 11.8%; logs: 2+ 7.6%; form: type 3 6.9%; fork: Shapella 5.9%; verdict: no receipt, unsupportedType 5.6%; fork: Dencun 5.6%; fork: Pectra 5.1%; fork: Spurious Dragon 4.9%; form: type 4 4.9%; fork: Berlin 4.8%; fork: Paris 4.4%; fork: Frontier 4.3% | form: another first byte 2.0% |
| the difficulty of a block is the reference's | result: above the minimum 90.6%; bomb: 2 or more 62.2%; time factor: below 0 61.6%; rule: Byzantium on 61.5%; bomb delay: 0 38.5%; rule: Homestead to Spurious Dragon 30.6%; bomb: the number is below the delay 30.3%; the parent has ommers, from Byzantium 29.2%; time factor: -99, the least 22.6%; bomb delay: 5000000 16.7%; bomb delay: 9000000 15.8%; result: the minimum, by the rule 9.3%; bomb delay: 11400000 8.6%; bomb delay: 9700000 8.0%; rule: Frontier 7.9%; time factor: 1 7.6%; bomb: none, in the first two periods 7.0%; bomb delay: 3000000 6.3%; time factor: 0 6.3%; bomb delay: 10700000 6.1% | time factor: 2 1.9%; elapsed: 0 seconds 1.3%; bomb: 1, the third period 0.5%; result: exactly the minimum 0.1% |
| the rewards of a block are the reference's | reward: 2 ether 51.0%; reward: 5 ether 41.8%; ommers: 0 34.4%; ommers: 2 32.9%; ommers: 1 32.7%; age: 3 15.9%; age: 4 15.6%; age: 5 14.4%; age: 2 14.3%; age: 6 13.5%; age: 1 13.3%; age: 7 13.0%; reward: 3 ether 7.2% | - |
| the requests hash is EIP-7685's | requests: 0 44.6%; a request with data 38.7%; requests: 2+ 30.4%; requests: 1 25.0%; a request of its type alone 15.1%; a request of no byte 14.1%; a request of two bytes 13.8%; every request is left out 10.5% | - |
| the deposit request of a log is the reference's | size: 576 81.3%; verdict: a deposit request 35.2%; verdict: no request, wrongOffset 23.8%; verdict: no request, wrongSize 22.3%; verdict: no request, wrongLength 18.7%; size: below 576 9.6%; size: above 576 9.1% | - |
| the root of a list is the reference's | every value is below 32 bytes 77.2%; withdrawals: 2 to 16 55.2%; values: 2 to 16 54.7%; withdrawals: 0 13.9%; values: 0 13.2%; values: 129+ 12.8%; withdrawals: 1 10.9%; a value of 32 bytes or more 9.6%; values: 1 9.4%; withdrawals: 129+ 9.0%; withdrawals: 17 to 127 7.5%; values: 17 to 127 7.1%; withdrawals: 128 3.5% | values: 128 2.8% |
| the DAO Fork moves the accounts of EIP-779 | index: in the list 98.7%; the recovery contract holds ether before 97.4%; funded accounts: 2+ 54.8%; funded accounts: 0 26.3%; funded accounts: 1 18.9%; an account funded twice 4.6% | index: past the list 1.3% |
| state machine: the tracker reads as a model that copies its state | op: setStorage 75.9%; a storage write to no account 67.5%; op: setBalance 64.5%; op: moveEther 64.2%; op: snapshot 62.4%; op: setCode 56.1%; op: setTransient 54.9%; op: incrementNonce 54.4%; op: destroyAccount 53.8%; a move refused for the balance 48.2%; op: endTransaction 41.5%; a read of a word that differs from the word before the transaction 38.1%; a storage write of a word 38.1%; op: destroyStorage 36.9%; op: createEther 36.4%; op: markCreated 35.4%; op: rollback 33.7%; a transaction ends with a changed state 32.4%; op: touch 31.3%; op: destroyTouched 29.9%; a move to the sender itself 28.7%; a move that is made 27.0%; op: commit 25.4%; a rollback that undoes a write 24.1%; a storage write of zero to no word 23.0%; before Paris: a change leaves an empty account 21.1%; a rollback of no write 17.1%; fork: paris 15.4%; fork: fusaka 15.3%; fork: tangerineWhistle 14.8%; fork: spuriousDragon 14.7%; a transaction ends with transient storage 14.6%; fork: london 13.9%; fork: istanbul 13.1%; a rollback inside another snapshot 12.9%; fork: dencun 12.8%; snapshots: three deep or more 9.8%; a transaction ends with storage in the state 9.3%; a commit inside another snapshot 9.0%; a rollback that brings back a storage word 8.5%; an account destroyed with storage 7.7%; touched empty accounts destroyed 7.1%; a rollback that brings back an account 4.8% | from Paris: a change leaves the account empty, and destroys it 2.7%; a storage write that clears a word 2.2% |
| an answer of eth_getProof holds exactly when it is true | the account is absent 61.8%; accounts in the state: 2+ 47.0%; a false answer about an account that is absent 38.6%; the account exists 38.2%; no false answer to try 34.3%; accounts in the state: 1 30.2%; slots asked: 0 27.0%; slots asked: 2 26.3%; slots asked: 1 24.0%; a slot of an account with no storage 23.4%; accounts in the state: 0 22.8%; slots asked: 3 22.7%; a false answer: slotValue 15.8%; fork: tangerineWhistle 15.7%; fork: dencun 15.4%; fork: spuriousDragon 14.5%; fork: istanbul 14.2%; fork: paris 13.8%; fork: fusaka 13.3%; fork: london 13.1%; a false answer: codeHash 13.0%; a false answer: nonce 12.5%; a false answer: balance 12.3%; a false answer: storageHash 11.9%; a slot that is not set, in a storage with words 3.4% | a slot that is set 2.4%; a false answer: slotKey 0.2% |
| scenario: the tracker beside state.py at tangerine_whistle | op: setStorage 53.0%; op: snapshot 30.4%; op: setBalance 30.2%; op: endTransaction 25.2%; op: destroyStorage 19.6%; op: incrementNonce 19.3%; op: destroyAccount 18.9%; op: markCreated 18.4%; op: moveEther 17.3%; op: destroyTouched 16.2%; op: touch 16.2%; op: setTransient 15.6%; op: setCode 15.5%; a state root of a state with an account 10.2%; snapshots: two deep or more 4.4% | op: rollback 2.8%; op: commit 2.7%; a state root of a state with storage 1.6% |
| scenario: the tracker beside state.py at spurious_dragon | op: setStorage 52.2%; op: setBalance 33.2%; op: snapshot 32.4%; op: endTransaction 27.6%; op: moveEther 19.2%; op: setTransient 19.1%; op: touch 18.8%; op: incrementNonce 18.1%; op: destroyAccount 17.4%; op: destroyTouched 16.6%; op: markCreated 16.6%; op: setCode 15.4%; op: destroyStorage 15.1%; a state root of a state with an account 10.6%; snapshots: two deep or more 4.8%; op: rollback 3.4%; op: commit 3.3% | a state root of a state with storage 0.8% |
| scenario: the tracker beside state.py at istanbul | op: setStorage 51.6%; op: setBalance 32.1%; op: snapshot 31.5%; op: endTransaction 27.6%; op: touch 19.3%; op: setTransient 18.3%; op: markCreated 18.3%; op: destroyTouched 18.1%; op: destroyStorage 18.0%; op: moveEther 17.6%; op: setCode 17.4%; op: incrementNonce 17.0%; op: destroyAccount 16.2%; a state root of a state with an account 11.1%; snapshots: two deep or more 3.9%; op: rollback 3.6%; op: commit 3.3% | a state root of a state with storage 1.3% |
| scenario: the tracker beside state.py at london | op: setStorage 49.2%; op: setBalance 33.0%; op: snapshot 31.3%; op: endTransaction 29.8%; op: touch 20.0%; op: setTransient 19.2%; op: destroyTouched 19.1%; op: destroyStorage 17.9%; op: setCode 17.3%; op: markCreated 17.2%; op: incrementNonce 17.2%; op: destroyAccount 16.8%; op: moveEther 16.0%; a state root of a state with an account 11.9%; op: commit 4.3%; snapshots: two deep or more 3.6% | op: rollback 2.9%; a state root of a state with storage 1.4% |
| scenario: the tracker beside state.py at paris | op: setStorage 49.0%; op: snapshot 33.5%; op: setBalance 32.6%; op: endTransaction 25.5%; op: setCode 19.5%; op: markCreated 17.2%; op: moveEther 16.9%; op: destroyStorage 16.7%; op: destroyAccount 16.7%; op: incrementNonce 16.2%; op: setTransient 15.4%; a state root of a state with an account 6.2%; snapshots: two deep or more 4.1%; op: rollback 4.1%; op: commit 3.0% | a state root of a state with storage 0.6% |
| scenario: the tracker beside state.py at cancun | op: setStorage 52.3%; op: setBalance 33.8%; op: snapshot 32.1%; op: endTransaction 26.2%; op: markCreated 20.3%; op: destroyStorage 17.9%; op: setCode 17.2%; op: destroyAccount 16.9%; op: moveEther 16.7%; op: setTransient 16.6%; op: incrementNonce 15.9%; a state root of a state with an account 6.8%; snapshots: two deep or more 4.4%; op: commit 3.9%; op: rollback 3.1% | a state root of a state with storage 0.1% |
| scenario: the tracker beside state.py at osaka | op: setStorage 51.5%; op: setBalance 29.6%; op: snapshot 29.1%; op: endTransaction 27.6%; op: setCode 18.3%; op: moveEther 18.0%; op: destroyAccount 17.6%; op: setTransient 17.5%; op: incrementNonce 17.5%; op: markCreated 16.7%; op: destroyStorage 16.0%; a state root of a state with an account 7.9%; snapshots: two deep or more 4.5%; op: rollback 4.3%; op: commit 3.1% | a state root of a state with storage 0.3% |
| OPEN: the empty proof shows absence in the empty trie | - | - |
| OPEN: go-ethereum's answer for a slot of an empty storage holds | - | - |

What the shares showed:

- A transaction as bytes was valid with a sender in 5.1% of the cases, and with a type from 1 to 4 in 1.4% together.
  A blob transaction or a set code transaction was valid in one case of 1,000 each.
  So the verdict `true` of a typed transaction was not tested.
- The changed proofs of "an accepted proof does not lie" were never accepted: a changed node no longer has its hash.
  EthLib refused with `hashMismatch`, `missingNode` or `unusedNodes` only.
  `invalidNode`, `hexPrefix`, `emptyExtension` and `invalidReference` of `decodeNode` and `resolve` were never reached, in any property.
- 21% of the tries were empty, and 40% of the keys asked were the empty key.
  The root was an extension in 1.8% of the tries.
- The state machine of the trie reached nine keys in one sequence of 1,000.
- 42% of the cases of the logs bloom had no log, and a log had four topics in two cases of 1,000.
  Three addresses in four and three topics in four were one of seven fixed values, so few bits of the filter were ever set.
- A header after its parent had several faults at once, and the first check hid the others: seven of the checks were the first to fail in under 3% of the cases.
- Every pair of headers was at one fork.
  `checkHeader` takes two forks, and the first block of a fork was never generated.
- The answer of `eth_getProof` held a slot that is set in 2.4% of the cases, and the two changes of a slot were tried in 0.2% and 0%.
- The scenario beside `state.py` compared a state root of a state with storage in 0.1% to 1.6% of its sequences.
- The difficulty landed exactly on the minimum once, and on the third period of the bomb five times.
- The forks were the 20 of the reference: Constantinople (the driver ran Petersburg under that name), Phase 0, Altair, Bellatrix, BPO3 to BPO5, Glamsterdam and Hegotá were never passed to a function that takes a fork.

### Step 2: the generators, and the shares after

What changed:

- Forks: a fork is drawn by family, each family as often as another, from all 29 forks of EthLib.
  A fork with no module in the released reference runs beside the fork whose rules it keeps: Constantinople beside the reference's Constantinople, Phase 0 beside Muir Glacier, Altair beside London, Bellatrix beside Gray Glacier.
  BPO3, BPO4, BPO5, Glamsterdam and Hegotá are answered by `oracle/execution_amsterdam.py`, the branch `forks/amsterdam` of execution-specs at the revision that `oracle/requirements-evm.txt` names, with Hegotá beside Amsterdam.
  Without that branch the driver skips those five forks and says so.
- Transactions: a new property signs each transaction with eth-account, so the sender is recovered and the rules after it are reached.
  Its fields are valid or have one field at an edge: the gas limit at the least one and one beside it, at `2^24` and `2^32 - 1` and one above, the nonce at `2^64 - 2` and `2^64 - 1`, the priority fee at the maximum fee and one above, init code at 49152 bytes and one above, six and seven blobs.
- Tries: the keys of one trie are drawn in one of four styles: nested (the alphabet of round 1), under a common stem (the root is an extension), wide (any byte, so a branch has a child at every nibble), and deep (32 bytes that differ in the last nibbles, so leaves lie inside their branch).
  A key in 20 has 33 to 70 bytes, a value in 15 has 250 to 300 bytes, and a trie in 12 has 40 to 90 keys.
  The key asked is a key that is set, or beside one: a byte changed, cut by a byte or two, a byte longer.
  Half the tries of the proof property are secured.
- The state machine of the trie mostly adds a key while the trie is small, and runs in one of the four styles.
- Logs: each count of topics from 0 to 4 is as common as another, and half the addresses and topics are any bytes.
- A header after its parent is valid or has exactly one of 20 faults, each at the first value that its rule refuses.
  A valid child is at the edge of each rule: the gas limit as far from the parent's as it may be, the gas used equal to the limit, 32 bytes of extra data, one second after the parent.
  The property now also requires that a header with no fault is accepted and a header with a fault refused.
- Difficulty: each fork as often as another, the number near the periods of the bomb of that fork, one case in eight exactly on the minimum.
- Ommers: every fork before Paris (17, was 5), the same ommer twice, more ommers of blocks that are too old or that a block already holds.
- The answer of `eth_getProof`: the account mostly exists, half the states gain storage words at the end, and all three slots are asked.
- The tracker: a write is mostly to an account that the model holds.
  In the scenario the state holds the model, `next` moves it, and `buildIn` draws a command for it.

The shares of the classes that were under 3%, before and after, at 1,000 cases:

| Property | Class | Before | After |
| --- | --- | ---: | ---: |
| a transaction as bytes is the reference's | init code above the limit of EIP-3860 | 0.0% | 0.4% |
| a transaction as bytes is the reference's | blobs: 7+ | 0.1% | 1.6% |
| a transaction as bytes is the reference's | valid with a sender: type 4 | 0.1% | 0.2% |
| a transaction as bytes is the reference's | valid with a sender: type 3 | 0.1% | 0.2% |
| a transaction as bytes is the reference's | verdict: a transaction, invalid, noBlobData | 0.2% | 0.5% |
| a transaction as bytes is the reference's | verdict: a transaction, invalid, emptyAuthorizationList | 0.2% | 0.2% |
| a transaction as bytes is the reference's | verdict: a transaction, invalid, invalidBlobVersionedHash | 0.2% | 0.1% |
| a transaction as bytes is the reference's | valid with a sender: type 2 | 0.3% | 0.8% |
| a transaction as bytes is the reference's | blobs: 0 | 0.4% | 1.6% |
| a transaction as bytes is the reference's | authorizations: 1+ | 0.8% | 4.3% |
| a transaction as bytes is the reference's | valid with a sender: type 1 | 0.9% | 1.2% |
| a transaction as bytes is the reference's | verdict: a transaction, invalid, priorityFeeGreaterThanMaxFee | 2.0% | 7.3% |
| a transaction as bytes is the reference's | sender: recovered, on another chain | 2.2% | 1.5% |
| a transaction as bytes is the reference's | authorizations: 0 | 2.2% | 2.6% |
| a transaction as bytes is the reference's | blobs: 1 to 6 | 2.2% | 4.6% |
| the sender of a transaction passes the rules of its EIPs | a delegation indicator from Pectra | 2.6% | 16.2% |
| the root of a trie is the reference's | root: an extension | 1.8% | 7.6% |
| an accepted proof does not lie | accepted by both, a changed proof | 0.0% | 0.0% |
| an accepted proof does not lie | accepted by EthLib alone | 0.1% | 0.9% |
| state machine: a trie under writes, beside py-trie | reaches 9 keys or more | 0.1% | 7.3% |
| the logs bloom is the reference's | a log with four topics | 0.2% | 43.3% |
| the logs bloom is the reference's | distinct entries: 9+ | 2.0% | 44.3% |
| a header as bytes is the reference's | form: fewer fields | 2.7% | 2.8% |
| a header after its parent is valid as in the reference | verdict: invalid, wrongOmmersHash | 0.4% | 2.1% |
| a header after its parent is valid as in the reference | verdict: invalid, genesisNumber | 0.5% | 4.2% |
| a header after its parent is valid as in the reference | verdict: invalid, nonzeroDifficulty | 0.9% | 2.4% |
| a header after its parent is valid as in the reference | verdict: invalid, nonzeroNonce | 1.2% | 2.7% |
| a header after its parent is valid as in the reference | verdict: invalid, extraDataTooLong | 1.9% | 4.2% |
| a header after its parent is valid as in the reference | verdict: invalid, wrongParentHash | 2.5% | 4.0% |
| a header after its parent is valid as in the reference | verdict: invalid, wrongExcessBlobGas | 2.5% | 4.9% |
| the ommers of a block are valid as in the reference | verdict: invalid, parentMissing | 1.2% | 7.2% |
| the ommers of a block are valid as in the reference | verdict: invalid, numberOutOfRange | 1.8% | 5.6% |
| the ommers of a block are valid as in the reference | verdict: invalid, ommerAlreadyIncluded | 2.0% | 3.2% |
| the ommers of a block are valid as in the reference | verdict: invalid, duplicateOmmer | 2.0% | 11.1% |
| the ommers of a block are valid as in the reference | verdict: invalid, wrongAge | 2.9% | 9.9% |
| a receipt as bytes is the reference's | form: another first byte | 2.0% | 12.2% |
| the difficulty of a block is the reference's | result: exactly the minimum | 0.1% | 12.7% |
| the difficulty of a block is the reference's | bomb: 1, the third period | 0.5% | 8.2% |
| the difficulty of a block is the reference's | elapsed: 0 seconds | 1.3% | 0.9% |
| the difficulty of a block is the reference's | time factor: 2 | 1.9% | 5.0% |
| the root of a list is the reference's | values: 128 | 2.8% | 3.0% |
| the DAO Fork moves the accounts of EIP-779 | index: past the list | 1.3% | 11.1% |
| state machine: the tracker reads as a model that copies its state | a storage write that clears a word | 2.2% | 14.6% |
| state machine: the tracker reads as a model that copies its state | from Paris: a change leaves the account empty, and destroys it | 2.7% | 3.7% |
| an answer of eth_getProof holds exactly when it is true | a false answer: slotKey | 0.2% | 6.8% |
| an answer of eth_getProof holds exactly when it is true | a slot that is set | 2.4% | 44.9% |
| scenario: the tracker beside state.py at 7 forks | a state root of a state with storage | 0.1% to 1.6% | 7.1% to 12.8% |
| scenario: the tracker beside state.py at 7 forks | op: commit | 2.7% to 4.3% | 17.3% to 21.3% |
| scenario: the tracker beside state.py at 7 forks | op: rollback | 2.8% to 4.3% | 30.0% to 35.0% |

Notes on that table:

- "an accepted proof does not lie" still never has both verifiers accept a changed proof.
  That is the nature of a hash: the two new properties of tries built node by node reach those branches instead.
- "a transaction as bytes" keeps its near-invalid generator, where most cases stop at an early rule.
  The classes that it leaves low are those of "a signed transaction is valid as in the reference": valid with a sender 51.1%, of type 1, 2, 3 and 4 in 9.3%, 12.9%, 3.8% and 4.5%.

The shares of every property after the change, at 1,000 cases.
A minimum is a `cover` at about a third of the share, asked only of runs of 1,000 cases or more.

| Property | Classes, with the minimum of each where it has one | Still under 3% |
| --- | --- | --- |
| a transaction as bytes is the reference's | call data with a byte 49.3% (min 17%); verdict: no transaction, decoding 38.6%; form: legacy 31.5%; form: type 4 21.7%; sender: recovered 17.3% (min 5%); verdict: a transaction, invalid, insufficientGas 17.0%; form: type 2 15.7%; an access list with an entry 14.6% (min 3%); gas: further above the least 14.0%; form: type 3 13.6%; form: type 1 13.1%; legacy: signs a chain (EIP-155) 12.6%; gas: one above the least 10.3%; gas: further below the least 10.2%; gas: the least 10.1%; verdict: a transaction, invalid, nonceOverflow 10.0%; the floor of EIP-7623 is above the intrinsic gas 8.7% (min 1%); gas: one below the least 8.6%; a contract creation 8.3% (min 3%); verdict: no transaction, unsupportedType 8.2%; verdict: a transaction, valid but for its signature 7.6%; verdict: a transaction, invalid, priorityFeeGreaterThanMaxFee 7.3%; legacy: signs no chain 5.7%; verdict: a transaction, valid but for its chain 5.4%; blobs: 1 to 6 4.6%; verdict: a transaction, valid, with a sender 4.6%; form: another first byte 4.4%; legacy: signs a chain before Spurious Dragon 4.3% (min 1%); authorizations: 1+ 4.3%; form: a type that the fork does not have yet 3.8%; each of 12 fork families 4.9% to 15.5% | authorizations: 0 2.6%; valid with a sender: type 0 2.2%; legacy: another v 1.8%; blobs: 0 1.6%; blobs: 7+ 1.6%; sender: recovered, on another chain 1.5%; valid with a sender: type 1 1.2%; valid with a sender: type 2 0.8%; verdict: a transaction, invalid, noBlobData 0.5%; init code above the limit of EIP-3860 0.4%; verdict: a transaction, invalid, blobCountExceeded 0.4%; verdict: a transaction, invalid, emptyAuthorizationList 0.2%; valid with a sender: type 4 0.2%; valid with a sender: type 3 0.2%; verdict: a transaction, invalid, invalidBlobVersionedHash 0.1%; verdict: a transaction, invalid, gasLimitExceeded 0.1% |
| a signed transaction is valid as in the reference | call data with a byte 88.1% (min 17%); sender: recovered 81.8% (min 5%); verdict: a transaction, valid, with a sender 51.1%; gas: the least 40.4%; form: legacy 39.9%; a contract creation 25.4% (min 3%); legacy: signs a chain (EIP-155) 25.2%; gas: further above the least 24.6%; form: type 2 22.0%; an access list with an entry 21.0% (min 3%); valid with a sender: type 0 20.6%; verdict: a transaction, invalid, insufficientGas 15.5%; gas: one below the least 15.2%; legacy: signs no chain 14.7%; form: type 1 13.5%; valid with a sender: type 2 12.9%; gas: one above the least 12.4%; legacy: signs a chain before Spurious Dragon 11.9% (min 1%); verdict: a transaction, valid but for its chain 11.7%; form: type 4 10.6%; form: type 3 10.0%; authorizations: 1+ 9.6%; valid with a sender: type 1 9.3%; verdict: a transaction, invalid, nonceOverflow 7.7%; the floor of EIP-7623 is above the intrinsic gas 7.6% (min 1%); blobs: 1 to 6 7.5%; valid with a sender: type 4 4.5%; eth-account does not sign the fields 4.0%; sender: recovered, on another chain 4.0%; verdict: a transaction, invalid, priorityFeeGreaterThanMaxFee 3.8%; valid with a sender: type 3 3.8%; each of 12 fork families 6.8% to 9.8% | form: a type that the fork does not have yet 2.3%; verdict: no transaction, unsupportedType 2.3%; blobs: 7+ 2.3%; init code above the limit of EIP-3860 2.0%; verdict: a transaction, invalid, gasLimitExceeded 1.6%; gas: further below the least 1.1%; verdict: a transaction, invalid, invalidBlobVersionedHash 1.1%; verdict: a transaction, invalid, blobCountExceeded 0.7%; verdict: a transaction, invalid, initCodeTooLarge 0.5% |
| a transaction in a block body is the reference's | form: a typed transaction 60.8%; verdict: no transaction, decoding 29.9%; verdict: no transaction, unsupportedType 22.7%; form: the bytes of a list 17.3%; the bytes of a list, before Glamsterdam 14.2% (min 5%); form: a list 10.3%; verdict: a transaction of type 0 9.6%; verdict: a transaction of type 4 8.5%; form: no byte 8.0%; verdict: no transaction, emptyTransaction 8.0%; verdict: a transaction of type 1 7.8%; verdict: a transaction of type 2 7.3%; verdict: a transaction of type 3 6.2%; the bytes of a list that start with 0xff 4.9% (min 1%); form: another first byte 3.6%; the bytes of a list, from Glamsterdam 3.1%; each of 12 fork families 3.6% to 33.0% | - |
| a transaction of eth-account reads back | call data with a byte 93.4% (min 17%); chain: 2^63 or more 46.8% (min 16%); an access list with an entry 30.8% (min 3%); type 2 21.5%; type 3 20.9%; type 0 19.7%; type 1 19.6%; type 4 18.3%; legacy: signs a chain (EIP-155) 14.9% (min 4%); an authorization for a chain 13.0% (min 4%); a contract creation 10.5% (min 3%); an authorization for every chain 6.9% (min 3%); legacy: signs no chain 4.8% (min 1%) | - |
| the authority of an authorization is the reference's | no authority 53.8% (min 18%); fields at their edges, with a signature of no key 49.0%; an authority is recovered 46.2% (min 14%); an authorization that eth-account signed 34.6%; the other signature of the key, with a high s 16.4% | - |
| a transaction passes the rules that read no state, each at its edge | verdict: valid 50.3%; verdict: invalid, nonceOverflow 12.9%; a type that the fork does not have yet 10.6% (min 3%); verdict: invalid, unsupportedType 10.6%; an authorization, from Pectra 9.2% (min 3%); a priority fee above the maximum fee 6.9% (min 2%); a nonce of 2^64 - 1, from London 6.7% (min 2%); a nonce of 2^64 - 2, from London 6.5% (min 1%); init code of 49152 bytes, from Shapella 6.4% (min 1%); a gas limit of 2^24 + 1, from Fusaka 6.0% (min 1%); verdict: invalid, gasLimitExceeded 6.0%; no authorization, from Pectra 5.3% (min 1%); verdict: invalid, emptyAuthorizationList 5.3%; init code of 49153 bytes, from Shapella 4.7% (min 1%); a gas limit of 2^24, from Fusaka 4.7% (min 1%); verdict: invalid, initCodeTooLarge 4.7%; seven blobs or more, before Fusaka 3.7% (min 1%); no blob, from Dencun 3.6% (min 1%); verdict: invalid, noBlobData 3.6%; a hash of another version, from Dencun 3.0% (min 1%); each of 11 fork families 1.6% to 36.9% | verdict: invalid, invalidBlobVersionedHash 2.4%; verdict: invalid, priorityFeeGreaterThanMaxFee 2.2%; seven blobs or more, from Fusaka 2.0%; verdict: invalid, blobCountExceeded 2.0%; six blobs, from Fusaka 1.5% |
| the sender of a transaction passes the rules of its EIPs | nonce: the sender's 79.0%; the tip is capped by the fee 50.0% (min 16%); code: other 45.0%; balance: exact 40.5%; verdict: refused, senderNotEoa 31.1%; code: none 29.9%; balance: more 29.6%; verdict: may send 25.4%; code: a delegation indicator 25.1%; type 2 22.5%; verdict: refused, insufficientBalance 22.5%; balance: one wei short 21.9%; type 3 20.5%; type 1 19.0%; type 0 19.0%; type 4 19.0%; a delegation indicator from Pectra 16.2% (min 6%); verdict: refused, nonceTooLow 12.6%; nonce: below the sender's 12.6%; the tip is paid whole 12.0% (min 3%); a delegation indicator before Pectra 8.9% (min 3%); verdict: refused, nonceTooHigh 8.4%; nonce: above the sender's 8.4%; balance: further short 8.0%; each of 12 fork families 3.1% to 21.9% | - |
| the root of a trie is the reference's | trie: a node held by hash 73.0% (min 23%); root: a branch 68.6%; secured 47.8% (min 16%); keys: 3 to 8 37.8%; trie: a node held inside its parent 34.3% (min 11%); trie: nodes held both ways 31.1% (min 10%); trie: a value of 250 bytes or more 30.7% (min 9%); writes: a key written twice 25.9% (min 9%); trie: an extension 25.6% (min 8%); trie: a key of 33 bytes or more 23.5% (min 7%); trie: a key is a prefix of another 19.9% (min 6%); trie: a branch with a value 19.9% (min 6%); keys: 2 19.6%; keys: 9 or more 18.8%; writes: a delete of a key that is set 14.9% (min 4%); keys: 1 12.3%; root: a leaf 12.3%; keys: 0 11.5%; root: no node 11.5%; root: an extension 7.6% | - |
| the root of a trie under another hash is the reference's | trie: a node held by hash 75.7% (min 23%); root: a branch 71.3%; the key is absent 69.3%; proof: 1 node 52.3%; secured 51.0% (min 16%); hash: sha256 50.4%; hash: prefixed 49.6%; proof: 2 nodes or more 47.7%; keys: 3 to 8 39.2%; trie: a node held inside its parent 33.5% (min 11%); trie: nodes held both ways 30.8% (min 10%); the key is set 30.7%; trie: a value of 250 bytes or more 29.2% (min 9%); trie: an extension 26.5% (min 8%); trie: a key of 33 bytes or more 25.4% (min 7%); keys: 9 or more 20.5%; trie: a key is a prefix of another 19.7% (min 6%); trie: a branch with a value 19.7% (min 6%); keys: 2 18.7%; keys: 1 12.8%; root: a leaf 12.8%; keys: 0 8.8%; root: no node 8.8%; root: an extension 7.1% | - |
| the proof of a key is py-trie's | trie: a node held by hash 75.4% (min 23%); root: a branch 70.0%; the key is absent 69.8%; key: 1 to 4 bytes 65.6%; proof: 1 node 53.7%; secured 48.9% (min 16%); path: into a node held by hash 46.3% (min 14%); keys: 3 to 8 40.1%; trie: a node held inside its parent 35.4% (min 11%); trie: nodes held both ways 32.8% (min 10%); the key is set 30.2%; proof: 2 nodes 29.0%; trie: a value of 250 bytes or more 27.7% (min 9%); trie: an extension 27.5% (min 8%); path ends at: the leaf of the key 26.4%; path ends at: an empty slot of a branch 26.0%; path ends at: the leaf of another key 25.5%; trie: a key of 33 bytes or more 24.0% (min 7%); trie: a key is a prefix of another 21.0% (min 6%); trie: a branch with a value 21.0% (min 6%); keys: 9 or more 20.1%; keys: 2 17.8%; path: through an extension 17.6% (min 5%); proof: 3 nodes or more 17.3%; path: through a branch with a value 17.2% (min 5%); key: 32 bytes 14.8%; path: into a node held inside its parent 11.5% (min 3%); keys: 1 11.2%; root: a leaf 11.2%; keys: 0 10.8%; root: no node 10.8%; path ends at: the empty trie 10.8%; root: an extension 8.0%; key: empty 8.0%; key: 33 bytes or more 6.3%; key: 5 to 31 bytes 5.3%; path ends at: an extension that the key leaves 4.4%; path ends at: the value of a branch 3.8%; path ends at: a branch with no value 3.1% | - |
| an accepted proof does not lie | trie: a node held by hash 74.0% (min 23%); trie: a node held inside its parent 69.5% (min 11%); trie: nodes held both ways 65.2% (min 10%); root: a branch 63.4%; key: 1 to 4 bytes 61.1%; the proof is changed, and not the proof of the key asked 60.5% (min 19%); trie: an extension 50.0% (min 8%); path: into a node held by hash 46.0% (min 14%); trie: a key is a prefix of another 42.1% (min 6%); trie: a branch with a value 42.1% (min 6%); keys: 3 to 8 40.2%; the proof is the proof of the key asked 39.5% (min 14%); changes: 2 36.1%; EthLib: refuses, hashMismatch 35.9%; path: through a branch with a value 35.0% (min 5%); path ends at: the leaf of another key 33.0%; changes: 1 32.4%; path: through an extension 32.2% (min 5%); changes: 0 31.5%; trie: a value of 250 bytes or more 29.8% (min 9%); EthLib: accepts, the key is absent 29.4%; trie: a key of 33 bytes or more 26.4% (min 7%); path: into a node held inside its parent 22.1% (min 3%); change: a node dropped 20.7%; change: the tail of another proof 20.7%; keys: 9 or more 20.5%; change: a node repeated 20.0%; change: a node rewritten 19.2%; path ends at: the leaf of the key 19.0%; path ends at: an empty slot of a branch 18.7%; change: a byte 18.0%; keys: 2 17.6%; root: an extension 14.9%; key: 32 bytes 14.8%; EthLib: refuses, unusedNodes 13.4%; keys: 1 13.1%; root: a leaf 13.1%; EthLib: refuses, missingNode 11.2%; EthLib: accepts, the key is set 10.1%; key: empty 10.0%; keys: 0 8.6%; root: no node 8.6%; path ends at: the empty trie 8.6%; path ends at: the value of a branch 8.3%; key: 33 bytes or more 8.2%; path ends at: an extension that the key leaves 7.1%; key: 5 to 31 bytes 5.9%; path ends at: a branch with no value 5.3% | accepted by EthLib alone 0.9%; accepted by both, a changed proof 0.0% |
| state machine: a trie under writes, beside py-trie | write: a new key 100.0%; a write to a trie with nodes held both ways 69.0% (min 24%); write: a delete of a key that is set 66.8%; write: a new value of a key that is set 65.6%; a delete leaves its branch, or the trie had none 54.2%; a write to a trie where a key is a prefix of another 43.5% (min 14%); a write to a trie with a branch with a value 43.5% (min 14%); write: a delete of no key 43.3%; a delete turns a branch into a leaf 42.7%; a delete turns a branch into an extension 10.9%; reaches 9 keys or more 7.3% (min 2%) | - |
| the logs bloom is the reference's | an entry outside the seven fixed ones 87.1% (min 28%); another entry: the filter lacks a bit 77.3% (min 26%); a log with two topics or more 76.9% (min 25%); logs: 2+ 65.7%; distinct entries: 9+ 44.3%; an entry twice 43.9% (min 13%); a log with four topics 43.3% (min 13%); a log with one topic 42.4% (min 14%); a log with no topic 41.7% (min 13%); distinct entries: 4 to 8 28.6%; logs: 1 24.1%; another entry: the filter holds its bits 22.7% (min 7%); distinct entries: 1 to 3 16.9%; logs: 0 10.2%; distinct entries: 0 10.2% | - |
| a header as bytes is the reference's | form: the count of fields of the fork 90.1%; verdict: a header 59.9%; a header with a base fee 33.9% (min 10%); verdict: no header, inField 30.2%; a header with a withdrawals root 25.3% (min 7%); a header with blob gas 20.4% (min 5%); a header with a number of 2^64 or more 16.5% (min 4%); a header with a requests hash 16.3% (min 4%); verdict: no header, wrongFieldCount 9.9%; form: more fields 7.1%; a header with a block access list hash and a slot 5.2% (min 1%); each of 12 fork families 6.8% to 10.7% | form: fewer fields 2.8% |
| a header after its parent is valid as in the reference | parent gas: below the target 45.5%; parent gas: above the target 43.4%; fault: none 29.5%; verdict: valid 29.5%; the excess blob gas that EthLib expects is not zero 26.2% (min 6%); valid, before London 13.5% (min 1%); verdict: invalid, invalidGasLimit 12.5%; valid, the gas limit as far below the parent's as it may be 11.1% (min 3%); parent gas: at the target 11.1%; valid, the gas limit as far above the parent's as it may be 9.2% (min 3%); verdict: invalid, timestampNotAfterParent 8.8%; valid, from Dencun 8.2% (min 2%); valid, the gas used is the gas limit 7.4% (min 2%); valid, extra data of 32 bytes 7.4% (min 2%); verdict: invalid, wrongDifficulty 7.4%; verdict: invalid, wrongBaseFee 7.3%; valid, one second after the parent 7.1% (min 2%); verdict: invalid, wrongNumber 6.7%; fault: difficultyDown 5.3%; valid, Paris and Shapella 4.9% (min 1%); verdict: invalid, wrongExcessBlobGas 4.9%; fault: sameTime 4.6%; fault: difficultyUp 4.5%; fault: gasLimitDown 4.4%; fault: gasLimitFloor 4.3%; fault: extraData 4.2%; verdict: invalid, extraDataTooLong 4.2%; verdict: invalid, genesisNumber 4.2%; fault: earlier 4.2%; fault: baseFeeDown 4.1%; fault: genesis 4.1%; fault: parentHash 4.0%; verdict: invalid, wrongParentHash 4.0%; fault: gasLimitUp 3.8%; fault: numberSame 3.4%; fault: numberUp 3.4%; fault: gasUsedAbove 3.3%; verdict: invalid, gasUsedAboveLimit 3.3%; fault: baseFeeUp 3.2%; fault: excessUp 3.0%; each of 11 fork families 7.2% to 10.8% | valid, London to Gray Glacier 2.9%; fault: nonce 2.7%; verdict: invalid, nonzeroNonce 2.7%; verdict: invalid, nonzeroDifficulty 2.4%; fault: ommersHash 2.1%; verdict: invalid, wrongOmmersHash 2.1%; fault: excessDown 1.9% |
| the first header of a fork is valid as the sources say | parent gas: below the target 45.7%; parent gas: above the target 43.1%; fault: none 28.0%; verdict: valid 28.0%; the excess blob gas that EthLib expects is not zero 20.0% (min 6%); the first block of a fork after Dencun 19.1% (min 6%); the first block of Paris 18.0% (min 5%); the first block of London 16.3% (min 5%); the first block of Dencun 15.9% (min 5%); verdict: invalid, invalidGasLimit 12.3%; parent gas: at the target 11.2%; verdict: invalid, wrongBaseFee 11.2%; valid, from Dencun 9.8% (min 2%); valid, the gas limit as far above the parent's as it may be 9.5% (min 3%); valid, the gas limit as far below the parent's as it may be 9.0% (min 3%); verdict: invalid, timestampNotAfterParent 7.5%; valid, extra data of 32 bytes 7.3% (min 2%); verdict: invalid, wrongDifficulty 6.9%; valid, before London 6.8% (min 1%); fault: baseFeeDown 5.9%; valid, London to Gray Glacier 5.8%; verdict: invalid, wrongNumber 5.8%; valid, Paris and Shapella 5.6% (min 1%); the two forks have one name in the reference 5.5% (min 1%); fault: baseFeeUp 5.3%; valid, one second after the parent 5.2% (min 2%); fault: gasLimitUp 5.2%; verdict: invalid, wrongExcessBlobGas 5.1%; valid, the gas used is the gas limit 5.0% (min 2%); fault: difficultyUp 4.9%; fault: difficultyDown 4.7%; fault: earlier 4.5%; verdict: invalid, genesisNumber 4.1%; fault: gasLimitDown 4.0%; fault: ommersHash 3.7%; verdict: invalid, wrongOmmersHash 3.7%; fault: numberSame 3.6%; fault: genesis 3.6%; fault: gasUsedAbove 3.4%; verdict: invalid, gasUsedAboveLimit 3.4%; fault: extraData 3.4%; verdict: invalid, extraDataTooLong 3.4%; fault: gasLimitFloor 3.1%; fault: parentHash 3.0%; verdict: invalid, wrongParentHash 3.0%; fault: excessUp 3.0%; fault: sameTime 3.0%; each of 10 fork families 0.9% to 24.5%; each of 23 steps between two forks 0.9% to 18.0% | fault: nonce 2.9%; verdict: invalid, nonzeroNonce 2.9%; verdict: invalid, nonzeroDifficulty 2.7%; fault: numberUp 2.7%; fault: excessDown 2.1% |
| the ommers of a block are valid as in the reference | pick: a fresh ommer in range 61.5%; ommers: 2 42.5%; verdict: valid 39.1%; ommers: 1 34.7%; valid, with an ommer 25.6% (min 7%); pick: a fresh ommer out of range 21.5%; pick: an ommer of a recent block 17.9%; pick: a block of the chain 15.5%; ommers: 0 15.2%; verdict: invalid, duplicateOmmer 11.1%; verdict: invalid, wrongAge 9.9%; verdict: invalid, wrongOmmersHash 9.2%; valid, with two ommers 8.4% (min 1%); ommers: 3 7.6%; verdict: invalid, parentMissing 7.2%; pick: a wrong difficulty 7.2%; verdict: invalid header, wrongDifficulty 6.1%; verdict: invalid, numberOutOfRange 5.6%; verdict: invalid, ommerInChain 4.8%; verdict: invalid, tooManyOmmers 3.8%; verdict: invalid, ommerAlreadyIncluded 3.2%; each of 6 fork families 14.8% to 19.2% | - |
| a receipt as bytes is the reference's | form: legacy 44.7%; verdict: no receipt, inField 37.9%; a log with a topic 30.3% (min 10%); logs: 2+ 23.5%; verdict: a receipt with status 0 18.5%; form: type 1 16.5%; verdict: no receipt, unsupportedType 16.1%; verdict: a receipt with status 1 14.7%; form: type 2 13.1%; verdict: a receipt with a state root 12.8%; form: another first byte 12.2%; logs: 0 11.9%; logs: 1 10.6%; form: type 3 7.4%; form: type 4 6.1%; each of 12 fork families 5.2% to 9.4% | - |
| the receipts of a block count its gas | two transactions or more 70.8% (min 23%); a status, from Byzantium 69.2% (min 22%); gas before the list 45.1% (min 14%); a state root, before Byzantium 21.5% (min 7%); no transaction 9.3% (min 3%) | - |
| the difficulty of a block is the reference's | result: above the minimum 76.3%; rule: Byzantium on 68.3%; time factor: below 0 47.0%; bomb: 2 or more 41.5%; bomb delay: 0 31.7%; the parent has ommers, from Byzantium 29.5% (min 10%); bomb: none, in the first two periods 25.7%; rule: Homestead to Spurious Dragon 24.9%; bomb: the number is below the delay 24.6%; bomb delay: 5000000 18.3%; time factor: -99, the least 17.8%; time factor: 1 16.9%; bomb delay: 9000000 15.8%; time factor: 0 13.3%; result: exactly the minimum 12.7%; bomb delay: 9700000 11.4%; result: the minimum, by the rule 11.0%; bomb delay: 11400000 10.6%; bomb: 1, the third period 8.2%; bomb delay: 3000000 6.9%; rule: Frontier 6.8%; bomb delay: 10700000 5.3%; time factor: 2 5.0% | elapsed: 0 seconds 0.9% |
| the rewards of a block are the reference's | reward: 2 ether 66.3%; ommers: 1 35.6%; ommers: 0 32.6%; ommers: 2 31.8%; reward: 5 ether 26.8%; age: 4 15.5%; age: 1 15.0%; age: 7 14.8%; age: 2 14.4%; age: 3 13.9%; age: 6 13.8%; age: 5 12.6%; reward: 3 ether 6.9% | - |
| the requests hash is EIP-7685's | requests: 2+ 74.3%; a request with data 66.4% (min 21%); a request of its type alone 40.5% (min 12%); a request of no byte 39.9% (min 12%); a request of two bytes 38.3% (min 13%); requests: 1 17.6%; every request is left out 12.3% (min 4%); requests: 0 8.1% | - |
| the deposit request of a log is the reference's | size: 576 81.2%; verdict: a deposit request 35.2%; verdict: no request, wrongOffset 25.7%; verdict: no request, wrongSize 20.3%; verdict: no request, wrongLength 18.8%; size: below 576 11.3%; size: above 576 7.5% | - |
| the root of a list is the reference's | withdrawals: 2 to 16 55.1%; every value is below 32 bytes 48.3% (min 15%); values: 2 to 16 44.0%; a value of 32 bytes or more 40.4% (min 13%); values: 129 to 256 16.4%; withdrawals: 0 15.0%; values: 0 11.3%; values: 257+ 10.6%; withdrawals: 1 9.3%; withdrawals: 129 to 256 9.0%; values: 1 8.1%; withdrawals: 17 to 127 7.5%; values: 17 to 127 6.6%; withdrawals: 128 4.1%; values: 128 3.0% | - |
| the DAO Fork moves the accounts of EIP-779 | the recovery contract holds ether before 97.2% (min 32%); index: in the list 88.9%; funded accounts: 2+ 55.5%; funded accounts: 0 26.6%; funded accounts: 1 17.9%; index: past the list 11.1%; an account funded twice 5.3% (min 1%) | - |
| state machine: the tracker reads as a model that copies its state | a storage write to no account 56.3%; a read of a word that differs from the word before the transaction 55.4% (min 11%); a storage write of a word 55.4%; a move refused for the balance 38.7%; a move that is made 36.0%; a storage write of zero to no word 29.9%; a transaction ends with a changed state 29.2% (min 8%); a move to the sender itself 28.5%; a rollback that undoes a write 25.4%; a rollback of no write 17.2%; before Paris: a change leaves an empty account 15.4%; a storage write that clears a word 14.6%; a rollback inside another snapshot 14.4% (min 3%); a rollback that brings back a storage word 13.0% (min 2%); a transaction ends with transient storage 12.1% (min 3%); a transaction ends with storage in the state 12.0% (min 2%); snapshots: three deep or more 10.3% (min 2%); a commit inside another snapshot 10.0% (min 2%); an account destroyed with storage 9.6% (min 3%); touched empty accounts destroyed 6.9%; a rollback that brings back an account 4.0% (min 1%); from Paris: a change leaves the account empty, and destroys it 3.7%; each of 7 fork families 13.3% to 15.4%; each of 16 operations 27.8% to 79.7% | - |
| hex-prefix writes the bytes of the reference, at every length | a nibble of 8 or more 91.0% (min 29%); length: above 66 28.4% (min 8%); flag: a leaf, odd 26.8% (min 8%); flag: a leaf, even 26.2% (min 8%); flag: an extension, even 25.1% (min 9%); flag: an extension, odd 21.9% (min 7%); length: odd, 3 to 61 19.1% (min 6%); length: even, 4 to 60 16.4% (min 5%); length: 62, 64 or 66 13.0% (min 4%); length: 63 or 65 9.2% (min 3%); length: 1 5.7% (min 1%); length: 2 4.2% (min 2%); length: 0 4.0% (min 2%) | - |
| hex-prefix reads exactly the encodings | verdict: the first nibble is above 3 38.6% (min 11%); verdict: an encoding with the first nibble 3 13.2% (min 4%); verdict: an encoding with the first nibble 1 12.1% (min 4%); verdict: an encoding with the first nibble 0 12.0% (min 4%); an encoding of one nibble 11.2% (min 4%); verdict: an encoding with the first nibble 2 9.7% (min 4%); an encoding of the empty path 9.0% (min 3%); verdict: empty 8.4% (min 2%); verdict: the padding is not zero 6.0% (min 2%) | - |
| a proof of a trie built node by node shows what its nodes say | EthLib: accepts 65.9%; secured 53.0% (min 16%); model: absent 33.3% (min 11%); py-trie answers, absent 32.5% (min 10%); model: a value 29.4% (min 8%); py-trie answers, a value 29.4% (min 8%); path: a child by hash 26.4% (min 8%); model: an item that is no node 23.5% (min 8%); path: a child inside its parent 21.6% (min 8%); proof: 2 nodes 18.5% (min 5%); path: a leaf of an even length 15.3% (min 5%); EthLib: refuses, invalidNode 15.1%; path: an extension of an odd length 14.4% (min 5%); path: a long child inside its parent 13.1% (min 4%); path: an extension of an even length 12.1% (min 4%); path: an empty slot of a branch 12.1% (min 3%); path: a leaf of an odd length 11.7% (min 2%); a node after the last one of the path 10.6% (min 3%); proof: 3 nodes or more 7.9% (min 2%); EthLib: refuses, unusedNodes 7.6%; path: an extension that the key leaves 6.6% (min 2%); path: ends at the value of a branch 5.1% (min 1%); path: ends at a branch with no value 4.9% (min 1%); EthLib: refuses, hexPrefix 4.9%; EthLib: refuses, emptyExtension 4.3%; path: a leaf of no nibble 4.0% (min 1%); path: a short child by hash 3.3%; model: a leaf with no value 3.2% (min 1%); a leaf with no value: EthLib answers - 3.2%; a leaf with no value: py-trie answers absent 3.2%; each of 17 items that are no node 0.3% to 4.3% | path: a child inside a child inside its parent 2.7%; py-trie accepts an item that is no node 2.7%; EthLib: refuses, invalidReference 1.5%; EthLib: refuses, missingNode 0.6%; EthLib: refuses, hashMismatch 0.1% |
| a proof whose path meets an item that is no node is refused | EthLib: refuses, invalidNode 60.3%; place: the root 34.1% (min 11%); place: under an extension 33.6% (min 11%); place: under a branch 32.3% (min 10%); EthLib: refuses, hexPrefix 24.3%; EthLib: refuses, invalidReference 11.0%; a branch whose value is a list 7.0% (min 3%); a path that is a list 6.9% (min 3%); a list of one item 6.8% (min 3%); a first nibble of 4 6.8% (min 3%); a hash of no node 6.7% (min 3%); a padding that is not zero 6.7% (min 3%); a list of three items 6.4% (min 3%); a list of no item 6.3% (min 3%); a list of 18 items 6.3% (min 3%); a list of 16 items 6.2% (min 3%); a leaf whose value is a list 6.1% (min 3%); a reference of 31 bytes 6.0% (min 3%); a path of no byte 5.7% (min 3%); a reference of 1 byte 5.5% (min 3%); a reference of 33 bytes 5.5% (min 3%); a first nibble of 15 5.1% (min 3%); EthLib: refuses, missingNode 4.4% | - |
| a range of a trie is accepted exactly when it is true | trie: an extension 57.0% (min 8%); node change: none 51.4%; trie: a node held inside its parent 50.6% (min 11%); EthLib: accepts, no key follows 44.7%; claim change: none 43.4%; trie: 2 to 4 keys 42.4%; claim: true, and a part of the trie 40.4% (min 13%); trie: 5 keys or more 38.6%; refused, a false claim 38.1% (min 12%); claim: 2 entries or more 37.9%; trie: a root that is an extension 35.7% (min 12%); claim: no entry 32.1%; claim: 1 entry 30.0%; start: a key of the trie 27.1% (min 9%); EthLib: refuses, mismatch 23.6%; start: between two keys 23.2% (min 6%); start: below every key 23.1% (min 7%); accepted, after a change of the nodes 21.9% (min 7%); start: above every key 16.8% (min 5%); accepted, after a change of the claim 16.0% (min 5%); node change: clear 15.1%; claim: true, with no entry in a trie with keys 14.5% (min 4%); EthLib: accepts, a key follows 10.6%; trie: 0 keys 9.8%; trie: 1 key 9.2%; claim change: fake 8.3%; claim change: start 8.0%; claim: the whole trie, with nodes 7.5% (min 2%); claim change: clear 7.5%; claim change: emptyValue 7.2%; claim change: drop 7.2%; accepted, with a node missing 7.0% (min 2%); claim change: swap 6.7%; refused, a true claim with a node missing 6.6% (min 2%); claim change: value 6.6%; EthLib: refuses, beforeStart 6.4%; node change: reverse 6.2%; EthLib: refuses, unsorted 6.0%; node change: junk 5.8%; node change: twice 5.5%; EthLib: refuses, emptyValue 5.5%; node change: drop 5.5%; node change: lastOnly 5.3%; node change: startOnly 5.2%; claim change: twice 5.1%; claim: the whole trie, with no node 5.0% (min 1%); EthLib: refuses, proof, missingNode 3.2% | - |
| an answer of eth_getProof holds exactly when it is true | the account exists 82.9%; slots asked: 3 75.9%; accounts in the state: 1 52.3%; a slot that is set 44.9% (min 15%); a slot that is not set, in a storage with words 41.6% (min 14%); accounts in the state: 2+ 36.2%; no false answer to try 31.5%; the storage of the account holds one word 28.5% (min 9%); a slot of an account with no storage 26.2% (min 8%); the storage of the account holds two words or more 25.6% (min 8%); a false answer: slotValue 18.4%; the account is absent 17.1%; accounts in the state: 0 11.5%; a false answer: balance 11.0%; a false answer about an account that is absent 10.0% (min 3%); a false answer: codeHash 10.0%; a false answer: nonce 9.4%; slots asked: 0 9.1%; a false answer: storageHash 9.0%; slots asked: 1 7.6%; slots asked: 2 7.4%; a false answer: slotKey 6.8%; a false answer: swapSlotProofs 3.9%; each of 7 fork families 12.9% to 15.8% | - |
| OPEN: the empty proof shows absence in the empty trie | - | - |
| OPEN: go-ethereum's answer for a slot of an empty storage holds | - | - |
| scenario: the tracker beside state.py at 7 forks | a storage write to no account 58.7% to 66.8%; a read of a word that differs from the word before the transaction 37.4% to 47.4% (min 11%); a storage write of a word 37.4% to 47.4%; a transaction ends with a changed state 26.9% to 32.8% (min 8%); a move refused for the balance 23.9% to 25.7%; a state root of a state with an account 23.4% to 31.3% (min 7%); a rollback that undoes a write 16.9% to 21.6%; a storage write of zero to no word 16.8% to 24.4%; a rollback of no write 16.3% to 22.0%; a move that is made 14.9% to 18.9%; a move to the sender itself 13.7% to 15.8%; an account destroyed with storage 13.6% to 16.8% (min 3%); a rollback inside another snapshot 10.8% to 13.7% (min 3%); a transaction ends with transient storage 10.6% to 12.6% (min 3%); snapshots: three deep or more 7.5% to 10.2% (min 2%); a transaction ends with storage in the state 7.1% to 12.8% (min 2%); a state root of a state with storage 7.1% to 12.8% (min 2%); a rollback that brings back a storage word 6.6% to 11.1% (min 2%); a storage write that clears a word 6.2% to 10.3%; a commit inside another snapshot 5.5% to 8.6% (min 2%); a rollback that brings back an account 4.6% to 6.6% (min 1%); a state root of a state with two accounts or more 4.0% to 12.9% (min 1%); each of 15 operations 17.3% to 77.3% | from Paris: a change leaves the account empty, and destroys it 0.0% to 5.8%; before Paris: a change leaves an empty account 0.0% to 31.1%; touched empty accounts destroyed 0.0% to 9.1% |

Classes that are still under 3%, and why they were left:

- The verdicts `noBlobData`, `emptyAuthorizationList`, `blobCountExceeded`, `initCodeTooLarge` and `gasLimitExceeded` of a transaction as bytes, at 0.1% to 1.8%.
  eth-account signs no blob transaction without a blob and no empty list of authorizations, and the three others need a fork from Shapella or from Fusaka.
  "a transaction passes the rules that read no state, each at its edge" reaches each of them from a model, at 2% to 7% on each side of its bound.
- `elapsed: 0 seconds` of the difficulty: no valid block has it.
- "from Paris: a change leaves the account empty, and destroys it" of the tracker, at 2.6% of all sequences: three forks of seven are from Paris.
- The refusal `missingNode` of a range, at 2.0%: a node is missing in more cases, and most of them are refused for another reason first.
- Each of the 23 steps between two forks of "the first header of a fork", at 0.6% to 10%: the four classes of step that change a rule are at 14% to 21% each.

### Step 3: every parameter

For each general function of `EthLib/Execution/Trie/`, `Transactions/` and `Blocks/`, its parameters and case splits, and the property that generates each.

| Definition | Parameters and case splits | Generated by |
| --- | --- | --- |
| `nibbleListToCompact` | the path: every length from 0 to 9, 62 to 66, 67 to 130, every nibble; the leaf flag; odd and even | "hex-prefix writes the bytes of the reference", against execution-specs and a writer from the text of the Yellow Paper |
| `compactToNibbleList` | every first byte; the three errors `empty`, `invalidFirstNibble`, `nonZeroPadding`; the four flags; the empty path and one nibble | "hex-prefix reads exactly the encodings" |
| `root`, `rootM`, `patricialize`, `encodeInternalNode` | the hash: Keccak-256, SHA-256, Keccak-256 of a prefixed input; secured or not; 0, 1, 2, 3 to 8, 9 to 90 keys; keys of 0 to 70 bytes; values of 1 to 300 bytes; a root that is no node, a leaf, an extension, a branch; a branch with a value; a child held inside and by hash; an entry with an empty value (`emptyValue`) | "the root of a trie is the reference's", "the root of a trie under another hash is the reference's" |
| `trieSet`, `trieGet` | a new key, a new value of a key, a delete of a key that is set and of no key; a delete that turns a branch into a leaf and into an extension | "state machine: a trie under writes, beside py-trie" |
| `getProof`, `proofBelow` | the hash (three); secured or not; a path that ends at the leaf of the key, the leaf of another key, an extension that it leaves, the value of a branch, a branch with no value, an empty slot, the empty trie | "the proof of a key is py-trie's", "the root of a trie under another hash" |
| `verifyProof`, `walk`, `resolve`, `decodeNode` | the same paths; secured or not; a leaf and an extension of odd and even length and of no nibble; a child inside its parent though long, by hash though short, inside a child inside its parent; every error: `missingNode`, `hashMismatch`, `rlp`, `hexPrefix`, `invalidNode`, `invalidReference`, `emptyExtension`, `unusedNodes`; 16 items that are no node, at the root, under an extension and under a branch | "a proof of a trie built node by node shows what its nodes say", "a proof whose path meets an item that is no node is refused", "an accepted proof does not lie" |
| `verifyRange`, `checkSubtree`, `rangePlace`, `lookupNode`, `strictlyIncreasing` | the trie: 0, 1, 2 to 4, 5 to 20 keys, spread, layered, and clustered under one extension, with leaves inside their branch; the start: a key, between two keys, below every key, above every key, both ends of the key space; the claim: no entry, one, several, the whole trie with and without nodes; the nodes: whole, none, one missing, another order, one twice, a stranger, one path only; the errors `unsorted`, `beforeStart`, `emptyValue`, `proof (missingNode)`, `mismatch`; the answer true and false | "a range of a trie is accepted exactly when it is true" |
| `decodeTransaction`, `decodePayload`, `typeFork`, the five codecs, `Codec Access`, `Codec Authorization` | 29 forks; the first byte: a list, 1 to 4, a type that the fork lacks, another byte, no byte; every field at the edges of its range | "a transaction as bytes is the reference's", "a signed transaction is valid as in the reference" |
| `decodeBodyTransaction`, `bodyItem` | 29 forks; a list, the bytes of a typed transaction, the bytes of a list before and from Glamsterdam, a first byte of `0xff`, no byte | "a transaction in a block body is the reference's" |
| `encodeTransaction`, `transactionHash`, the five signing hashes, `signingInput` | the five types; a legacy transaction with and without a chain; chains up to `2^64 - 1` | "a transaction of eth-account reads back" |
| `legacyRecovery`, `parityRecovery`, `validS`, `recoverSender`, `checkChainId`, `Transaction.chainId` | 29 forks; `v` of 27, 28, `35 + 2c`, `36 + 2c` and beside each; a chain signed before Spurious Dragon; `r` and `s` at 0, half the order, the order; the high `s` at Frontier and from Homestead | the three properties of a transaction as bytes and of eth-account |
| `intrinsicGas`, `calldataFloor`, `minimumGas`, `baseCost`, `dataCost`, `accessListCost`, `accessListDataCost`, `authorizationCost`, `createCost`, `floorTokens` | 29 forks, with the sender from Glamsterdam; a creation or a call; zero and other bytes of data; an access list; authorizations; init code around its limit | the same |
| `validateTransaction`, `checkContents`, `checkTransaction` | 29 forks; each error but `encoding` and `intrinsicGasAboveLimit`; the gas limit one below, at and one above the least, at `2^24` and `2^32 - 1` and one above; init code of 49151, 49152 and 49153 bytes; 0, 1, 6, 7 and 9 blobs; a hash of another version; 0, 1 and 2 authorizations; a nonce of `2^64 - 2`, `2^64 - 1` and `2^64`; `lifted` at its default only | the same, and "a transaction passes the rules that read no state, each at its edge", against a model in `Nat` from the EIPs |
| `recoverAuthority`, `authorizationHash` | a signed authorization, its other signature with a high `s`, a parity above 1, `r` and `s` out of range, a chain of 0, of the network, of `2^256 - 1` | "the authority of an authorization is the reference's" |
| `checkSender`, `maxGasFee`, `effectiveGasPrice` | 29 forks; the five types; the nonce below, at and above the sender's; the balance one wei short, exact, more; no code, a delegation indicator before and from Pectra, other code | "the sender of a transaction passes the rules of its EIPs" |
| `Codec (Header fork)`, `Header.hash`, `Header.fieldCount` | 29 forks, so each of the eight fields since London absent and present; the fields of another fork; numbers at `2^64` and `2^256` | "a header as bytes is the reference's" |
| `checkHeader`, `headerChecks`, `expectedBaseFeeAcross`, `expectedExcessBlobGas`, `expectedDifficulty`, `parentExcessBlobGas`, `checkGasLimitAcross` | `fork`: 24 forks; `parentFork`: the same fork, or the fork before (23 steps); the first block of London, of Paris, of Dencun and of each fork after it; 13 of the 15 errors of a header, without `parentBeforeLondon` and `encoding`; the gas of the parent below, at and above the target; `schedule` at its default only | "a header after its parent is valid as in the reference", "the first header of a fork is valid as the sources say" |
| `validateOmmers`, `checkOmmerHeader` | 17 forks before Paris; 0 to 3 ommers; every error but `encoding` and `wrongDaoExtraData`; `checkSeal` false only | "the ommers of a block are valid as in the reference" |
| `decodeReceipt`, `encodeReceipt`, `Codec (Receipt fork)`, `Outcome` | 29 forks; a state root before Byzantium, a status from it; the type byte 0 to 4, a type that the fork lacks, another byte; the three errors | "a receipt as bytes is the reference's" |
| `makeReceipts`, `makeReceiptsFrom`, `makeReceipt`, `Outcome.make` | 29 forks; 0 to 5 transactions; gas before the list | "the receipts of a block count its gas", against a sum in `Nat` |
| `logsBloom`, `Bloom.ofLogs`, `ofEntry`, `bits`, `toBytes`, `mayContain` | 0, 1, 2 to 6 logs; 0 to 4 topics; any address and topic; an entry that the filter holds and one that it lacks | "the logs bloom is the reference's" |
| `blockDifficulty`, `bomb`, `bombDelay`, `timeFactor` | 17 forks before Paris, and zero at each of the 12 from Paris; the three rules of the time; each factor from -99 to 2; the bomb below its delay, zero, one, more; the result below, at and above the minimum | "the difficulty of a block is the reference's" |
| `blockReward`, `minerReward`, `ommerReward` | 17 forks; 0 to 2 ommers; ages 1 to 7 | "the rewards of a block are the reference's" |
| `indexedRoot`, `withdrawalsRoot`, `Codec Withdrawal` | 0, 1, 2 to 127, 128, 129 to 256, 257 to 259 items; values below and from 32 bytes | "the root of a list is the reference's" |
| `requestsHash`, `depositRequestOfEvent`, `applyDaoFork`, `DAO_ACCOUNTS` | as in round 1, with fewer empty cases | their three properties |

### What was tested in round 3

Each row ran 1,000 cases.
The shares of the labels of each row are in the table of step 2.

| Property | EthLib definitions | Parameters varied | Reference | Result |
| --- | --- | --- | --- | --- |
| a signed transaction is valid as in the reference | `decodeTransaction`, `transactionHash`, `recoverSender`, `checkChainId`, `intrinsicGas`, `calldataFloor`, `validateTransaction`, `checkContents`, `checkTransaction` | 29 forks, 5 types, one field at an edge | eth-account 0.14.0 for the signature; execution-specs 2.20.0 and its branch `forks/amsterdam` for the verdict | pass |
| a transaction in a block body is the reference's | `decodeBodyTransaction`, `bodyItem` | 29 forks, the four forms of an item | execution-specs `decode_transaction` | pass |
| a transaction passes the rules that read no state, each at its edge | `validateTransaction`, `checkContents` | 27 forks before Glamsterdam, five rules, each value beside its bound | a model in `Nat` from EIP-1559, 2681, 3860, 4844, 7594, 7702 and 7825 | pass |
| the authority of an authorization is the reference's | `recoverAuthority`, `Codec Authorization` | signed, the high twin, fields at their edges | execution-specs `recover_authority` of Prague | pass |
| the root of a trie under another hash is the reference's | `root`, `getProof`, `verifyProof` with a hash that is not Keccak-256 | two hashes, secured or not, four styles of keys | execution-specs `trie.root` with its hash replaced; the entries for the proof | pass |
| hex-prefix writes the bytes of the reference, at every length | `nibbleListToCompact`, `compactToNibbleList` | lengths 0 to 130, both flags | execution-specs `nibble_list_to_compact`; a writer here from Appendix C | pass |
| hex-prefix reads exactly the encodings | `compactToNibbleList` | every first byte, encodings changed in a byte | the two rules of Appendix C; execution-specs for what is read | pass |
| a proof of a trie built node by node shows what its nodes say | `verifyProof`, `walk`, `resolve`, `decodeNode` | nodes along a path of up to five levels, three ways to hold a child, items that are no node, a node too many | a model here that reads the generated nodes; py-trie 4.0.0 where it answers | pass |
| a proof whose path meets an item that is no node is refused | `verifyProof`, `decodeNode`, `resolve` | 16 items at three places | the rule | pass |
| a range of a trie is accepted exactly when it is true | `verifyRange`, `checkSubtree`, `rangePlace`, `lookupNode` | three styles of trie, the start, the claim and eight changes of it, the nodes and seven changes of them | the trie itself, for the truth of a claim; py-trie for the nodes of the two paths | pass |
| the first header of a fork is valid as the sources say | `checkHeader` with two forks | 23 steps between two forks, 20 faults | execution-specs `validate_header` of the fork of the child, with two rules of the EIPs added | pass |
| the receipts of a block count its gas | `makeReceipts`, `makeReceiptsFrom`, `Outcome.make` | 29 forks | a sum in `Nat` | pass |

Checks added to the properties of round 1:

- `checkTransaction` gives the sender and the intrinsic gas of the answer exactly when the parts pass.
- `encodeReceipt` writes back the bytes that `decodeReceipt` read.
- `Bloom.mayContain` of an entry that no log has is what the bytes of the reference say.
- A trie with an empty value has no root and no proof.
- A withdrawal reads back.
- The difficulty is zero at each fork from Paris.

### The finding of round 1: the empty proof of the empty trie

The two properties of the group `execution: findings (each must fail)` still fail on this branch, as they must:

    ✗ OPEN: the empty proof shows absence in the empty trie failed after 1 test and 2 shrinks.
    ✗ OPEN: go-ethereum's answer for a slot of an empty storage holds failed after 1 test and 2 shrinks.

The finding was reported upstream as issue #3386, and upstream fixed it in pull request #3405.
This branch is not yet rebased on that fix, so `verifyProof` here still refuses the proof with no node.
After the next rebase both properties pass, and the `mustFail` group then reports that the finding is gone.
They then move to the passing groups: "the empty proof shows absence in the empty trie" beside the proof properties, and the answer of go-ethereum beside "an answer of eth_getProof holds exactly when it is true".

### Notes of round 3, none a finding

#### A leaf with an empty value reads as a value

- Definition: `walk`, `EthLib/Execution/Trie/Proof.lean:166`.
- A proof whose path ends at a leaf with the empty byte string as its value gives `some` of the empty byte string.
  A branch with an empty value gives `none`.
  py-trie reads both as absent.
- No trie of the Yellow Paper holds such a leaf, so no root that `root` computes has such a proof, and EIP-1186 says nothing of it.
  `AccountProof.verifySlot` decodes the value as RLP, which fails on no byte, so the answer of `eth_getProof` is refused either way.
- It is recorded because a caller of `verifyProof` that reads `some` as "the key is set" reads this proof differently from py-trie.

      import EthLib.Execution.Trie
      import EthLib.Cryptography.Hash.Keccak
      open EthLib.Execution.Trie EthLib.Cryptography.Hash.Keccak

      -- A leaf of no nibble with an empty value: the list `[0x20, ""]`.
      def leaf : ByteArray := ⟨#[0xc2, 0x20, 0x80]⟩
      -- A branch of 17 empty items.
      def branch : ByteArray := ⟨#[0xd1] ++ Array.replicate 17 0x80⟩

      -- `Except.ok (some 0)`: a value of no byte.
      #eval (verifyProof keccak256 (keccak256 leaf) false .empty [leaf]).map (·.map (·.size))
      -- `Except.ok none`.
      #eval (verifyProof keccak256 (keccak256 branch) false .empty [branch]).map (·.map (·.size))

#### The reference at the first block of a fork

`validate_header` of execution-specs 2.20.0 is not the EIPs at two places, and EthLib follows the EIPs at both.
The oracle command `headeracross` adds the two rules, and its docstring says so.

- At the first London block, execution-specs checks the gas limit inside `calculate_base_fee_per_gas`, which it does not call for that block.
  So it accepts any gas limit there.
  EIP-1559 bounds it by twice the gas limit of the parent, and `checkGasLimitAcross` does that.
- From Pectra, `calculate_excess_blob_gas` reads the blob gas of the parent only when the parent has the header type of the fork itself.
  At the first block of Pectra, Fusaka, BPO1 and BPO2 the parent has the type of the fork before, and execution-specs counts its blob gas as zero.
  EIP-4844 defines the excess from the parent's header, and `expectedExcessBlobGas` reads every parent from Dencun on.

With the two rules added, EthLib and the reference agree on all 1,000 cases, at each of the 23 steps.

#### py-trie accepts items that are no node

py-trie reads 2% to 3% of the proofs whose path reaches an item that is no node, where EthLib refuses each.
It is a leniency of the reference, as its `ValidationError` of round 1 is a strictness.

### Harness mistakes of round 3, for the record

- A fault "one below" of a base fee or an excess of zero is no fault: Lean subtracts to zero.
  The property that a header with a fault is refused caught it at once, and those faults now go to 2.
- A label made from `repr` of an error held a line break where the value was long, and showed as two classes.
  The name of an error is now cut at its first character that is no letter.
- `cover` in a helper that takes its minimum as an argument was not rewritten with the others, and failed a run of 100 cases.

### Not covered after round 3

Round 3 covers three items of the list of round 1: `Trie/Range.lean`, a proof of a trie that is not canonical, and Glamsterdam for the bytes of a transaction, a header and a receipt.
What remains:

- `validateTransaction` with lifted rules (`LiftedRules`), and its errors `intrinsicGasAboveLimit` and `encoding`.
- `checkHeader` with a blob schedule that is not that of the fork, and with a parent more than one fork back: the reference defines no such header.
  So `parentBeforeLondon` is not reached.
  `checkHeader` at Glamsterdam, Hegotá and BPO3 to BPO5 against a reference: only the bytes of their headers were compared.
  The transition driver runs whole blocks at those forks.
- `verifyRange` on nodes that are no node (`branchValue`, `proof (invalidNode)`, `rlp`), and with another hash than Keccak-256.
- `Blocks/BlockAccessList.lean` and `AccessListBuilder.lean`: the branch of the reference has them, and no property here calls them.
- `Transactions/Authorization.lean` beyond the authority: `authorizationInScope`, `authorityAccepts`, `delegate`, `applyAuthorizations`.
- `Transactions/Network.lean`, `Process.lean`, `Settlement.lean` beyond the price, `Inclusion.lean` beyond `checkSender`, `Blocks/Transition.lean`, `SystemCall.lean`, `Genesis.lean`, `ProofOfWork.lean`, `Block.lean`: as in round 1; the transition driver of this round runs the first seven as wholes.
- `transactionsRoot` and `receiptsRoot`: they are `indexedRoot` of bytes that other properties compare, and were not called.
- `Transaction.unsigned`, `calculateTotalBlobGas`, `calculateDataFee`, `isDepositLog`, `depositRequests`, `daoExtraDataValid`, `payRewards`, `processWithdrawals`.
- The tracker and `AccountProof` on more than four accounts and three slots: the state trie of a case has at most four leaves.
- Tries of more than 90 keys, keys of more than 70 bytes, values of more than 300 bytes.
- Hegotá has no reference of its own: it ran beside Amsterdam, whose rules EthLib gives it.

## Notes on lean-hedgehog 0.3.0

These are of real use in this round, on the branch that `lakefile.toml` pins.

What helped:

- `classify`, `label` and `cover`.
  This is the piece that changed the result: 57 classes in 22 of the 27 passing properties were under 3%, and several were at zero.
  Nothing else in the library would have shown that the verdict `true` of a blob transaction was tested once in 1,000 cases.
- The context first in `check`, `apply` and `next`.
  The 15 command types of the tracker each held the oracle and the fork, copied in by `build`.
  They now hold an operation alone, and one function builds every instance:

      def stepCommand {κ : Type} (op : κ → Op) (gen : TrackerModel → Gen κ) :
          Command κ Beside BesideContext IO where
        check ctx c s := opAllowed (s.modelAt ctx) (op c)
        apply ctx c := runBeside ctx (op c)
        label c := reprStr (op c)
        build ctx := gen { fork := ctx.fork.1 }
        next ctx c s := { s with model := (s.modelAt ctx).step (op c) }
        buildIn ctx s := gen (s.modelAt ctx)

  An instance is then two lines, which answers the complaint of round 1 about five repeated lines.
- `next` and `buildIn`.
  The scenario state now holds the model, so a storage write is drawn for an account that exists.
  A state root of a state with storage went from 0.1% to 1.6% of the sequences to 7.6% to 13.0%.
- `scenario` with a range and a setup.
  The range `.linear 1 60` replaced the fixed 1 to 15, and the setup starts the state of the reference, which removed the `started` flag that every command checked.
- `applySut` with the model state before.
  The labels of a write need it: a delete of a key that is set, a rollback that undoes a write, a change that empties an account.
  Before, the system would have had to keep a copy of the model.
- `Selection.fromEnv`.
  `HEDGEHOG_ONLY="trie,proof"` was used at every step of this round, since one property is rebuilt and rerun far more often than the driver.
- `mustFail`: the two properties of the finding sit in a group that says so, and that will say when the rebase makes them pass.

What was awkward:

- The minimum of `cover` depends on the number of cases, as USAGE says, and a driver takes that number as an argument.
  A minimum set at 1,000 cases fails at the default 100.
  The driver keeps an `IO.Ref Bool` that `main` sets, and a helper `coverMin` that is `cover` in a long run and `classify` otherwise.
  That forced every labelled test into `IO`: four pure properties were split into a generator and a test.
  A `cover` that takes the least number of cases from which it applies, or a test that can read its own configuration, would remove all of it.
- `label` and `collect` take no minimum, and a `cover` that is not reached is not counted at all, so a class that never occurs has no line and fails nothing.
  A family of names needs one `cover` for each name in every case.
  The driver has `coverOne minimum names name` for that; the library could.
- The report lists the labels in the order of their first case, not by share and not by name.
  A property with 40 labels cannot be read that way, and a script sorted them.
  A name with a line break is printed as it is, with a blank line after it.
- The report of a group that must fail marks each expected failure with the same `✗` as a real one.
  A search for `✗` in the output of a run always finds two lines.
- A share of a state machine or of a scenario is the share of sequences with at least one such step.
  That is right, and it is not said where one would look: 94% "a new key" says little about how many writes were new keys.
- Nothing in a report says how long a property ran.

What is still missing:

- A way to ask a generator for its distribution without a property: the labels live in the test.
- Weights for the commands of a scenario: a weight is still a command listed several times.

No bug of the library was met.
On shrinking, this round has little to say: no new property failed on EthLib.
The two that must fail shrink in one to three steps to the least case, the empty key.
The harness mistakes were found by the counterexamples, which were small: a header pair with every field of the valid child but one.

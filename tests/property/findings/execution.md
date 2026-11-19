# The execution chain: what the property tests found

The driver is `Property/Execution.lean`, with its modules under `Property/Execution/`.
The oracle is `oracle/execution.py`, and `oracle/requirements-execution.txt` lists what it needs.

    cd tests/property
    lake build execution-property
    lake exe execution-property 1000

The scope is `EthLib/Execution/` without `Evm/`, `Fees/`, `Proofs/` and `Exports/`.
The main reference is execution-specs 2.20.0 (EELS), which has every fork from Frontier to BPO2.
It has no Glamsterdam, so no rule that starts there was compared.

No property found a place where EthLib computes another value than its source.
One finding stands: EthLib refuses the answer that go-ethereum gives for a slot of an account with no storage, a case that EIP-1186 does not define.
Three places where EthLib and the reference decode differently, with the same verdict on the transaction, are listed as notes.

## What was tested

Each row ran 2,000 cases in the last run, unless it says otherwise.

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

- Glamsterdam and Hegotá: EIP-2780, 7976, 7981, 8037, 8038, 7954, 7928 (block access lists), 8246, 8282.
  No reference was at hand; `Blocks/BlockAccessList.lean` and `Blocks/AccessListBuilder.lean` were not tested.
- `Transactions/Process.lean`, `Transactions/Settlement.lean` beyond the price, `Blocks/Transition.lean`, `Blocks/SystemCall.lean`, `Blocks/Genesis.lean`: they run the EVM, and need whole blocks beside EELS `state_transition`.
  This is the largest gap, and the next round should start there, with the fixtures of `ethereum/tests` or a block builder in the oracle.
- `checkInclusion` as a whole: only `checkSender` and the rules without state were compared; the order of its checks and `checkBlockGas` were not.
- `applyAuthorizations` and `delegate`: only `recoverAuthority` and `authorizationHash` were compared.
- `Blocks/ProofOfWork.lean` (Ethash): too slow for a property, and it needs the cache of an epoch.
- `Transactions/Network.lean` (blobs with their proofs): it needs KZG, which another layer tests.
- `Trie/Range.lean` (`verifyRange`, the range proofs of snap): no reference; its boundary cases deserve a model.
- A proof for a trie that is not canonical (a leaf with an empty value, a branch with one child, a child of fewer than 32 bytes held by its hash): a forged root is needed, and EIP-1186 does not say what to do.
- `History/Era1.lean`: it needs a writer of era1 files written apart from EthLib (e2store, Snappy frames, the SSZ root).
- `Network/` (eth and snap messages) and `Rpc/`: only read; the message identifiers agree with devp2p.
  Their codecs stand on the RLP layer, which another driver tests.
- `daoExtraDataValid` and the rule of the DAO Fork on the extra data.
- `payRewards` and `processWithdrawals` on a state: only their amounts and the tracker under them.

## Notes on lean-hedgehog

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

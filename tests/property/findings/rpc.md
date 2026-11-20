# The RPC, the wire messages and the history files of the execution layer: what the property tests found

The driver is `Property/Rpc.lean`, with its modules under `Property/Rpc/`.
The oracle is `oracle/rpc.py`, which loads `oracle/rpc_fees.py`, `rpc_logs.py`, `rpc_call.py`, `rpc_state.py`, `rpc_wire.py` and `rpc_era.py`; `rpc_txs.py` signs.
`oracle/requirements-rpc.txt` lists what they need, which the earlier drivers installed already.

    cd tests/property
    lake build rpc-property
    lake exe rpc-property 1000
    HEDGEHOG_ONLY="fee history" lake exe rpc-property 1000
    HEDGEHOG_ONLY="finding" lake exe rpc-property 100

The scope is `EthLib/Execution/Rpc/`, `Network/`, `History/` and `ErrorFormat.lean`, which no earlier round tested.
A run of 1,000 cases takes 105 seconds: 18 properties pass, and the findings fail by design in their own group: one in that run, and two since the property of finding 2 was added.

No property found a place where EthLib computes another value than its source.
One answer differs from what EthLib's own text says, and one point is open against a client that was not run.
So a bug that remains is not in what these properties reach, and "Not covered" says what they do not reach.

## The references

- `rpc_fees.py`: `eth_feeHistory` from `src/eth/fee_market.yaml` of execution-apis, with EIP-1559, EIP-4844, EIP-7691, EIP-7892 and EIP-7918 written out.
  The blob price is checked against EELS (`calculate_blob_gas_price`) at each fork that has a module.
  The percentile rule is `processBlock` of go-ethereum's `eth/gasprice/feehistory.go`, once with an exact comparison and once with its floats.
- `rpc_logs.py`: the objects of `src/schemas/block.yaml`, `receipt.yaml`, `transaction.yaml` and `filter.yaml`, and the texts of `src/eth/*.yaml` and `src/debug/getters.yaml`.
  Headers, blocks and receipts are encoded with the `rlp` package, the Bloom filter is `eth-bloom`'s, and coincurve signs.
- `rpc_call.py`: EELS (`ethereum-execution` 2.20.0) at 20 forks.
  `process_transaction` of the fork runs with the checks of a signed transaction replaced by the sender and the price of the request.
  The choices that `execute.yaml` leaves to the node are taken from the text of `Rpc/Call.lean`.
  For an estimate, a signed transaction of the request also runs through the unchanged `process_transaction`.
- `rpc_state.py`: the state getters of `src/eth/state.yaml` and the proofs of EIP-1186, with py-trie.
- `rpc_wire.py`: a reader of every message of `caps/eth.md` and `caps/snap.md` of devp2p, with the `rlp` package; EIP-2124 with zlib's CRC-32; account ranges and their proofs with py-trie.
- `rpc_era.py`: a writer of era1 files from `formats/era1.md` of e2store-format-specs, with cramjam (Snappy frames) and eth-remerkleable (the accumulator).

Each model was mutated by hand, 28 mutants in all, and the properties were run again.
26 were refused, three of them only after a generator was made to reach the rule: a flag of 2, BlockRangeUpdate on eth/68, and headers that do not chain.
Two were not: one is equivalent, and one needs a `v` of 35 or 36, which no signer writes.
The bound of `FORK_NEXT` inside a Status was refused after 338 cases, which is why the message properties run 5,000.

## What was tested

Each row is 1,000 cases unless it says otherwise.

| property | EthLib definitions | parameters varied | reference | result |
|---|---|---|---|---|
| fee history: eth_feeHistory is the model's | `ChainView.call`, `feeHistory`, `feeHistoryBlocks`, `percentile`, `percentilesIncreasing`, `Percentile.lt`, `tipAt`, `rewards`, `sortedTips`, `gasUsedList`, `nextFork`, `nextBaseFee`, `nextBlobBaseFee`, `blobGasRatio`, `blobGasPrice`, `ratioJson`, `feeHistoryJson` | 23 forks on a timeline of one to four, activations by block and by time at, before and after the head, a blob schedule of the chain, 1 to 7 blocks of 0 to 5 transactions of every type of the fork, tied tips, the count 0 to 1024, the newest block by number and by each tag, percentiles as JSON text with exponents, repeated, unsorted, out of range | `rpc_fees.py` | pass |
| logs: eth_getLogs is a scan of the receipts | `filterOfJson`, `filterAddress`, `filterTopic`, `Filter.selects`, `takesTopic`, `filterBlocks`, `boundNumber`, `aboveHead`, `matchingLogs`, `getLogs`, `logInfos`, `logInfoJson` | 23 forks, 1 to 6 blocks, blocks off the chain, logs of 0 to 4 topics, addresses as null, one, a list, an empty list, upper case; topics of 0 to 5 positions with null, one, alternatives, an empty list; bounds by number and tag, reversed, past the head, below the lowest; by hash with and without a bound | `rpc_logs.py` | pass |
| getters: blocks, transactions, receipts and raw forms | `blockJson`, `headerFields`, `blockFields`, `transactionInfoJson`, `transactionFields`, `typedFields`, `receiptInfoJson`, `receiptInfo`, `receiptInfos`, `gasBefore`, `transactionInfo`, `findTransaction`, `resolve`, `byTag`, `blockNumberOrTag`, `blockNumberOrTagOrHash`, `rawHeader`, `rawBlock`, `rawReceipts`, `rawTransaction`, 16 methods of `ChainView.call` | 23 forks, a chain of one or two forks, transactions of types 0 to 4 signed by 4 keys, with and without a chain ID, creations, access lists, blobs, authorizations; receipts with a status or a state root; blocks by number, tag, hash and the objects of EIP-1898 | `rpc_logs.py` | pass |
| call: eth_call leaves what the message leaves in EELS | `genericTransaction`, `GenericTransaction.kind`, `namesFee`, `toTransaction`, `prepareCall`, `headerEnvironment`, `transactionStart`, `CallSetup.run`, `callAnswer`, `revertError`, `haltError`, `runCall`, `ethCall`, `optionalBlock` | 23 forks; a chain of 1 to 3 blocks and the call on any of them; 13 contracts, precompiles, a delegated account, creations; every field of the call object absent or present; gas at, below and above the intrinsic gas and the block limit; fees at, below and above the base fee; balances at the cost and one wei around it | `rpc_call.py` | pass |
| estimate: eth_estimateGas is the binary search on EELS | `estimateGas`, `searchGas`, `Completes` | the same, three in four a call that a funded sender can make | `rpc_call.py`: the search of the method on EELS, the limit and the one below it, a signed transaction at both | pass |
| state: the state getters and eth_getProof | `balance`, `nonce`, `code`, `storageAt`, `storageValues`, `storageRequests`, `accountProof`, `accountProofJson`, `storageProofJson`, `bytesMax32`, `wordJson` | 23 forks, accounts with and without storage, an absent account, keys of 0 to 65 digits, the block absent, by tag, by number, unknown | `rpc_state.py` | pass |
| eth: a message reads as eth.md says, at every version (5,000) | `Message.decode`, `ofItem`, `encode`, `toItem`, `id`, `Status.ofItem`, `Announcement.ofItem`, `lengthsAgree`, `HeaderRequest`, `BlockId`, `BlockRange`, `readEnvelope`, `readWithPart` | eth/68 to eth/72, every message ID and IDs with no message; a tree of the shape, one with one part off its shape, one changed at random | `rpc_wire.py` | pass |
| snap: a message reads as snap.md says, at both versions (5,000) | `SnapMessage.decode`, `ofItem`, `encode`, `usesId`, `RangeEntry` | snap/1 and snap/2, every message ID; the same three kinds of tree | `rpc_wire.py` | pass |
| eth: the fork identifier of a head is EIP-2124's | `Schedule.forkId`, `blocks`, `times`, `forks`, `passed`, `checksum` | forks by block at 0, twice at one block, forks by time at and after the genesis time, a merge fork block, heads around each fork | `rpc_wire.py` | pass |
| eth: a Status is accepted as the rules say | `checkStatus`, `Schedule.validate`, `passedNext`, `BlockRange.Valid` | eth/68 to eth/72, the announced version, the peer at another head, its next fork changed, another hash, ranges in and out of order | `rpc_wire.py` | pass |
| eth: headers answer a GetBlockHeaders | `checkHeaders`, `followsIn`, `followAll`, `isStart`, `HeaderRequest.next`, `headerHash`, `headerNumber`, `headerParent` | the start by number and by hash, in and out of the chain, a limit of 0 to 8, a skip of 0 to 3, both directions; the true answer, and one changed in 8 ways | `rpc_wire.py` | pass |
| eth: transactions answer a GetPooledTransactions | `checkPooled`, `wireHash` | legacy lists, typed bytes, blob transactions in both forms, empty bytes; a part of the request in order, shuffled, with one more | `rpc_wire.py` | pass |
| snap: the value of a slim account | `fullAccount`, `ofSlimAccount`, `slimAccount` | slim and full forms, roots and code hashes absent, written out, of other lengths, lists for fields | `rpc_wire.py` | pass |
| state machine: the walk of snap over account ranges (`StateMachine`, 1 to 12 steps) | `verifyAccountRange`, `RangeAnswer` | tries of 1 to 14 accounts with shared prefixes, ranges of 1 to 5 accounts from where the walk is, 4 kinds of changed range | py-trie through `rpc_wire.py`, and a model of the walk | pass |
| scenario: a node under commands (`Command`, madhouse, 1 to 30 commands, 500 sequences) | what the three getter properties and the fee history name | a chain that the commands grow; the commands SEAL, MARK, LOGS, GET and FEES, each made for the chain so far | `rpc_logs.py`, `rpc_fees.py` | pass |
| era1: a file reads back, and a fault is refused | `decodeEra1`, `takeBlocks`, `splitLastTwo`, `readBlock`, `readBlocks`, `accumulatorRoot`, `bytes32Of` | the first number 0, 1, 8192, 2^40; 0 to 6 blocks; difficulties and totals to 2^255; 12 faults of the bytes, 3 of the chain, and other records | `rpc_era.py` | pass |
| era1: the limit of 8192 blocks (6) | `MAX_ERA1_BLOCKS`, `accumulatorRoot` | 8192 and 8193 blocks | `rpc_era.py` | pass |
| errors: an error shows its constructor and its named values | `namedArg`, `constructorFormat`, the `ErrorArg` instances, `Era1Error.reprPrec` | bytes, a hash, a word, an option, both precedences | the text itself | pass |
| finding: a precompile that lacks gas gets code 801 (`mustFail`) | `haltError` | 23 forks, precompiles 1 to 4, a gas limit of 21000 to 21010 | `rpc_call.py` | **fails: finding 1** |
| finding: an AccountRange with a nested account body is read (`mustFail`) | `SnapMessage.decode`, `RangeEntry.ofItem` | one account, its body as a byte string and as a nested list | go-ethereum, Besu and reth, as read | **fails: finding 2** |

### The shares of the labels, at 1,000 cases

| property | shares |
|---|---|
| fee history | answered 67%; refused -32602 19%, -32001 14%; the view crosses a fork 50%; blocks before and from London 13%, before and from Dencun 13%; the chain sets a blob schedule 24%; three blocks or more in the range 26%; no block in the range 8%; the count above the blocks held 37%; percentiles asked 60%; tied tips 15%; the next blob fee above 1 6%; go-ethereum's floats give another reward 1.3% |
| logs | answered 76%; refused -32602 17%, -32001 7%, 4444 0.1%; the filter selects a log 38%, some and not others 28%, two or more 29%; by hash 16%; topics select a log 10%; addresses select a log 5% |
| getters | found 73%, null 21%, refused 6%; each of the 16 methods found 1% to 9%; a chain before Byzantium 18%, before London 47%, from Dencun 22%, of two forks 28% |
| call | returns 38%, with data 12%, with a log 3%; error 809 18%, -32602 9%, 4 9%, 800 7%, 801 6%, 3 4%, 806 3%, -32000 3%, 804 2%; before London 26%, from Dencun 29%; names a fee 48%, no gas 35%, no sender 29%; a creation 15%; not on the head 9% |
| estimate | an estimate 85%; one below it fails 85%; a lower limit completes 5% (the limits form no interval); the estimate is the intrinsic gas 7%, above 60000 11%; a signed transaction at the estimate succeeds 50%, is invalid for another rule 4%; errors 15% |
| state | answered 76%, refused -32602 15%, -32001 9%; eth_getProof 18%, with a storage slot 13% |
| eth messages | read as generated 53%, changed and still read 8%, refused 39%, of which an ID with no message 7%; each of the 18 messages read 0.4% to 5% of 5,000 |
| snap messages | read as generated 55%, changed and still read 5%, refused 40%; each of the 10 messages read 3.5% to 8% |
| fork identifier | forks by block and by time 36%; some forks passed 29%; all passed 47% |
| Status | accepted 60%; a peer on an earlier fork 12%, on a later fork 15%; refused: incompatible 14%, version 10%, range 10%, stale 6% |
| headers | answer 84%, do not 16%; three headers or more accepted 28%; empty 22%; by hash 49%; falling 52%; with a skip 43% |
| pooled transactions | answer 71%, do not 29% |
| slim account | has a value 60%, has none 40% |
| snap walk | a range accepted 92%, of three accounts or more 40%, with no account 48%, the last of a trie 78%, a second range 62%, the whole trie walked 57%; a changed range refused 37% |
| node scenario | a block added 74%, a third 32%; marked 54%; a filter answered 66%, selects a log 42%, of an added block 29%; a getter finds 68%, after an added block 41%; a fee history 42%, over an added block 26% |
| era1 | reads 58%, refused 42%; three blocks or more 30%; no block 12%; other records 9%; from the genesis block 23%; a total of 2^64 or more 38%; each of the 15 faults 1.5% to 5.5% |

## Findings

### 1. A precompile that lacks gas gets -32000, where `Call.lean` says 801 (DOC)

- Definition: `haltError`, `EthLib/Execution/Rpc/Call.lean:319`, and the sentence at line 105: "Here it is code 801 for a lack of gas and 4 for an invalid opcode."
- Counterexample: Frontier, `eth_call` of `{"to": "0x0000000000000000000000000000000000000001", "gas": "0x5208"}`.
  The gas limit is the intrinsic gas, so ECRECOVER has no gas for its 3000.
- EthLib: the error `-32000`, "execution failed".
- EELS: `process_message_call` ends with `OutOfGasError`, at every fork and for each precompile.
- Why: `EvmError.precompile` is one error for a precompile that "rejects its input, or lacks gas" (`Evm/Errors.lean:59`), and `haltError` gives 801 to `outOfGas` only.
- The source decides nothing: `execute.yaml` fixes the answer of a revert only, and go-ethereum answers -32000 for every halt.
  So the answer is defensible, and the text of `Call.lean` is what does not hold.
- `git log --all -i --grep` for `801` and for `ran out of gas`, and the CHANGELOG, show no note of it.
- Share: 0.3% of the calls of the property, which accepts both codes there and counts them.
- Reproduction:

      import EthLib.Execution.Rpc
      open EthLib.Execution.Evm EthLib.Execution.Rpc
      #eval (haltError (.precompile 1)).code   -- -32000
      #eval (haltError .outOfGas).code         -- 801

      HEDGEHOG_ONLY="finding" lake exe rpc-property 100

### 2. The body of an account in AccountRange is read as a byte string (OPEN, no client was run)

- Definition: `RangeEntry.ofItem`, `EthLib/Execution/Network/Snap.lean:142`, and `fullAccount`, which decodes the bytes of that string.
- `caps/snap.md` writes `[[accHash: B_32, accBody: B], ...]`, and EthLib follows that letter: the body is a string that holds the RLP of the slim account.
- As I remember go-ethereum's `eth/protocols/snap/protocol.go`, `AccountData.Body` is an `rlp.RawValue`, which the encoder writes as it is.
  The slim account would then cross the wire as a list inside the entry, `[accHash, [nonce, balance, root, code]]`, and EthLib would refuse it with `listAsBytes`.
  `StorageData.Body` is a `[]byte` there, which agrees with `slotData: B`.
- I did not run go-ethereum and have no capture of a real message, so this is a question and not a result.
- What would decide it: one AccountRange message of a client, or the encoder of two clients.
- The property "snap: a message reads as snap.md says" follows the letter of `snap.md`, so it passes.
- The property "finding: an AccountRange with a nested account body is read" builds one account in both forms.
  EthLib reads the byte string and refuses the nested list, so the property fails, in the group that must fail.
  It was added after the coordinator's check below.

### Choices that EthLib writes down, seen by the properties and not findings

- The reward at a percentile compares exactly, where go-ethereum rounds `float64(gasUsed) * p / 100` down.
  The two differ in 1.3% of the cases; two transactions of 21000 and 21001 gas at the percentile 50 are the smallest.
  `Fees.lean` says "the comparison is exact".
- A count of 0 answers an empty range whose oldest block is the one after the newest; go-ethereum answers no data.
- "A monotonically increasing list" of percentiles is read as strictly increasing, as go-ethereum reads it.
- A fee of `2^256` or more is an invalid parameter, though the gas error group has the codes 807 and 808 for it.
- A second Version record makes a file no era1 file, though the grammar has `other-entries`.

### Small points of text, by reading and by the harness

- `Rpc/Account.lean:54` says that a member name written twice "is one member, the last, as the JSON text is read".
  `Lean.Json.parse`, which the export of the node calls, refuses such a text with "duplicate object key"; the request is then a parse error.
- `nextBlobBaseFee` (`Rpc/Fees.lean:180`) gives 0 after a block before London whose child is at Dencun, where EIP-4844 gives the price 1 of an excess of 0.
  No chain that passes London first has such a block, and the generator made none as the newest block.
- `fullAccount` gives a value for a slim account whose nonce is `2^64` or more; no state trie holds one.

## What failed first and was the harness

- A group of no block and a block of no transaction were both `-`.
- A view that starts above block 0 has fewer than 256 hashes, and EELS indexes them without a check.
- A balance at the cost of `2^256` gas does not fit a word.
- A transfer to a full balance: EELS has no rule, and EthLib aborts the call with -32603, which the model now expects.
- A request with two faults is refused by EthLib for one and by the model for another; the model now answers every code.
- A range of one account less, of a trie of one account with no proof, is the reply of a peer without the state.
- A total difficulty changed at the first block of a file breaks the second.
- The command that adds a block moved the state in `next` only; see the notes below.

## Not covered

- `Rpc/Simulate.lean` and `Rpc/Simulate/Blocks.lean` (`eth_simulateV1`): nothing.
  This is the largest gap of the scope: overrides, validation, moved precompiles, the transfer logs, the limits and the error codes.
- `Rpc/Trace.lean` and `Rpc/TraceView.lean` (the struct logs of `debug_trace*`): nothing.
- `Rpc/AccessList.lean` and `createAccessList`, `Rpc/Submit.lean` (`eth_sendRawTransaction`), `Rpc/Config.lean` (`eth_config`), `eth_baseFee` as a method, the block access list getters.
- `Rpc/Request.lean` and `serve`: the envelope of a request, its identifier, batches and notifications.
- The readers `headerOfJson`, `transactionOfJson`, `accountProofOfJson`, `authorization`.
- `eth_call`: a request of type 4 with authorizations, the fields `blobs`, `commitments` and `proofs`, a block by hash or tag, a pending block, a block off the chain, other `CallChoices` than the default, Glamsterdam (no reference), init code above the size limit.
- `eth_estimateGas`: the search was mirrored in the model with the same midpoint, so a search that is consistent and wrong in both would pass; the limit and the one below it are checked on their own.
- The getters run on receipts that the generator writes, not on receipts that a block leaves.
  The transition round compared receipts with EELS; no property here runs a block and then asks the node.
- Withdrawals and ommers in a block object: every block has none.
- `Network/Receipts.lean` (`consensusOfItem`, `receiptsMatch`, `checkPartialReceipts`), `Network/Bodies.lean` (`checkBody`), `Network/Cells.lean`, `Network/Session.lean` (`receiveEth`, `sendEth`), `accessListsResponse`, `codesAnswer`, `trieNodesAnswer`, `readPath`, `readGroups`, `verifyStorageRanges`, `capabilityLength`.
- The response size limits of snap: EthLib has no definition of them that I found.
- The file name of an era1 file: EthLib has no definition of it that I found.
- Era1 files of mainnet beyond what EthLib's own tests read, and Snappy streams of more than one chunk: the blocks here are small.

## Notes on lean-hedgehog 0.3.0

What helped:

- `classify` and `cover` found five weak tests that passed.
  NewPooledTransactionHashes was read in 0.0% of 5,000 cases because the shape table lacked its row.
  The node scenario answered every query on the first chain only (see below).
  Two generators refused 40% of their requests before the rule under test.
  The estimate never met a case where the limits form no interval until a label asked for one.
- `cover` in a `Command`, with the minimum switched by a flag of the context for short runs, reads well.
- `Selection.fromEnv` with `HEDGEHOG_ONLY` made the loop of 20 properties bearable: one property, 1,000 cases, a few seconds.
- `mustFail` on a second group: the finding stays in the driver, the exit code stays 0, and the report shows the counterexample each run.
- `applySut sut before after t`: the range of the snap walk starts at `before.next`, and the answer is checked against `after`; no field had to be copied into the transition.
- `scenarioFrom` with a generator of the start chain: the scenario shrinks the chain too.
- `Gen.subsequence` and `Gen.shuffle` for "a part of the request, in order" against "out of order".
- The shrunk counterexamples were small enough to read: a request of one field, one block, four accounts.

What was awkward:

- `next` and `apply` must both move the state, and nothing says so when they disagree.
  My SEAL moved the chain in `next` and returned `s` from `apply`, so every later command was generated for a chain of three blocks and ran on a chain of one.
  The scenario passed; only the label "after a command added a block" at 0.0% showed it.
  A default `apply` that calls `next`, or a check in debug runs that the two agree on a field, would have caught it.
- `build` is required even when `buildIn` is the only generator that makes sense; each of my five commands has a `build` that returns a dummy.
- The coverage of a `Command` scenario counts sequences, so "30% of sequences added a block" is easy to meet and says little about the share of commands.
  A count of commands by label in the report would help.
- A property that draws a symbolic request and resolves hashes inside the test (they come from the oracle) cannot shrink or show the request as it was sent; `annotate` covers it, with care.
- `Hedgehog.Status` clashes with a `Status` of the code under test when both namespaces are open.
- `forAll` needs `Repr`, and a `Repr` of a nested structure with 20-byte vectors fills a screen; I wrote `Repr` instances by hand for every case type.
- The report prints the labels in an order that changes from run to run.

What is missing:

- Weights for `Command.gen` in a scenario; I listed a command twice to make it twice as likely.
- A way to state a `cover` over the cases that reach a line, and not over all cases.
- A label of a command's outcome for free (ran, skipped by `check`).

No bug of the library was met.

## A second check of the account body of snap, by the coordinator

The finding on `RangeEntry.ofItem` above was left open, since no client was run.
Three clients were then read at the head of their repositories on 2026-11-20, and they agree with each other and not with EthLib.

- go-ethereum, `eth/protocols/snap/protocol.go`: `AccountData` has `Body rlp.RawValue`, which the encoder writes as it is, so the body is a nested list.
  `StorageData` has `Body []byte`, a byte string, so only accounts differ.
- Besu, `AccountRangeMessage.java`: it writes the body with `writeRLPBytes(toSlimAccount(...))` and reads it with `readAsRlp()`.
- reth, `crates/net/eth-wire-types/src/snap.rs`: "Account fields encoded as a nested RLP list with default hashes elided."

`snap.md` of devp2p writes `[accHash: B_32, accBody: B]`, a byte string, and EthLib follows that text.
So EthLib refuses the AccountRange that these clients send, and writes one that they refuse.
This is a BUG of interoperability, of the kind of the proof of no nodes in the first round: the text is not what the network speaks.

```lean
import EthLib.Execution.Network.Snap
import EthLib.Base.Hex

open EthLib EthLib.Execution.Network

def bytes (hex : String) : ByteArray := (Base.hexBytes? hex.toList).getD .empty

def verdict (hex : String) : String :=
  match SnapMessage.decode .snap1 0x01 (bytes hex) with
  | .ok _ => "read"
  | .error _ => "refused"

-- One account, its body a nested list, as the three clients write it.
#eval verdict
  "ea01e7e6a01111111111111111111111111111111111111111111111111111111111111111c401028080c0"
-- "refused"

-- The same with the body as a byte string that holds the list, as snap.md reads.
#eval verdict
  "eb01e8e7a0111111111111111111111111111111111111111111111111111111111111111185c401028080c0"
-- "read"
```

Both lines were run.
No client was run, and no captured message was read: the evidence is the three sources.

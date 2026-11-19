# Engine API and JSON: property tests

Driver `Property/Engine.lean` (modules under `Property/Engine/`), oracle `oracle/engine.py` and `oracle/engine_payload.py`.
The specification is execution-apis at commit `3284ee8`: `src/engine/*.md` and `src/schemas/base-types.yaml`.

    cd tests/property
    .venv/bin/pip install --no-deps -r oracle/requirements-engine.txt
    lake exe engine-property 1000

The last run was at 1,000 cases: 16 properties passed, and the 2 of the group `engine: findings` failed, as they must.
An earlier run at 2,000 cases gave the same result for the properties that existed then.

## What was tested

| Property | EthLib definitions | Reference | Cases | Result |
| --- | --- | --- | --- | --- |
| a base type reads as base-types.yaml says | `JsonRpc.uint`, `quantity`, `uint64`, `bytes`, `bytesMax`, `fixed`, `address` | the patterns of `base-types.yaml` in Python `re`, on near-valid text | 1,000 | pass |
| a quantity is written as both patterns ask | `quantityJson`, `quantity` | the same patterns, and those of `common.md` | 1,000 | pass |
| data is written as both patterns ask | `dataJson`, `bytes` | the same | 1,000 | pass |
| a token passes as the Engine profile says | `Jwt.authenticate`, `Jwt.check`, `Jwt.Json.fields`, `Jwt.Json.within` | a model from `authentication.md` and RFC 7515, 7518, 7519, 8259, with `hmac` and Python `json`; PyJWT 2.15.1 must verify each token the model accepts | 1,000 | pass |
| a built token verifies under PyJWT | `Jwt.build` | PyJWT | 1,000 | pass |
| newPayload answers as its specification says | `checkNewPayload`, `newPayloadWithoutState`, `newPayloadParams`, `anyPayload`, `payloadV4`, `AnyPayload.atFork`, `validRequests`, `acceptsFork`, `ExecutionPayload.toBlock`, `toHeader`, `blobVersionedHashes` | a model of versions 1 to 5 from the six fork files; the header hash from `rlp` 5.0.0 and Keccak, checked again with the `Header` classes of execution-specs 2.20.0 for Paris to Prague; transactions signed with eth-account | 1,000 | pass |
| forkchoiceUpdated chooses the head as its model does (`StateMachine`) | `forkchoiceUpdated`, `chainOf`, `latestValidHash`, `chainPassesTerminalCheck`, `belowFinalized`, `zeroAfterTransition`, `isTerminalPowBlock` | a tree of blocks by index, from steps 1 to 5, 7 and 9 of `engine_forkchoiceUpdatedV1` and the payload validation of `paris.md` | 1,000 sequences of up to 40 steps | pass |
| forkchoiceUpdated answers payload attributes as its specification says | `forkchoiceUpdatedCall`, `forkchoiceUpdatedParams`, `payloadAttributesOfVersion`, `checkAttributes`, `forkchoiceUpdatedResponse` | a table of version, fork, structure and time from the fork files; the structures by the oracle's schema | 1,000 | pass |
| payload bodies are read as their model reads them (`StateMachine`) | `getPayloadBodiesByRangeV1/V2`, `getPayloadBodiesByHashV1/V2`, `bodiesByRange`, `rangeLength`, `StoredBody.toV1/toV2`, `payloadBodiesV1Json/V2Json` | a list of blocks by number, from `shanghai.md` and `amsterdam.md`; JSON written by hand | 1,000 sequences of up to 40 steps | pass |
| getBlobs reads the pool as its specification says | `getBlobsV1` to `getBlobsV4`, `PooledBlob.toV1/toV2/toV4`, `selectedCells` | a list model from `cancun.md`, `osaka.md` and `amsterdam.md` | 250 | pass |
| a method name carries its version | `isVersionedMethod` | a regular expression | 1,000 | pass |
| the methods are those of the specification | `specifiedMethods`, `methodVersion` | the method headings of the eight files | 1 | pass |
| a structure of a response reads as its fields say | `payloadStatusOfJson`, `transitionConfigurationOfJson`, `clientVersionOfJson` | the oracle's schema | 1,000 | pass |
| an error has the code and the message of common.md | `EngineError.toRpcError`, `UNDECIDED_TERMINAL_TOTAL_DIFFICULTY` | the table of Errors | 1 | pass |
| a node answers its calls, in madhouse mode (`Command`, `scenario .madhouse`) | `newPayloadWithoutState`, `forkchoiceUpdatedCall`, `payloadId`, `getPayload`, `acceptsGetPayloadFork`, `payloadOfBlock`, `ExecutionPayload.ofBlock`, `getPayloadResultJson`, `getPayloadResultOfJson` | the forkchoice model, the oracle's payloads, and tables from the fork files | 1,000 sequences of 1 to 15 commands | pass |
| a node answers long sequences of calls (the same `Command`s, run with `executeCommands`) | the same | the same | 250 sequences of up to 60 commands | pass |
| a base type reads as the Encoding of common.md says | the readers of `JsonRpc` | the two patterns of the section Encoding of `common.md` | 1,000 | **fails: finding 1** |
| each error code of common.md is an error of EthLib | `EngineError` | the table of Errors | 1 | **fails: finding 2** |

The state machine tests are the two marked `StateMachine` and the two marked `Command`.
The three commands are `NewPayloadCmd`, `ForkchoiceCmd` and `GetPayloadCmd`, in `Property/Engine/Node.lean`.
A build that an update begins is written by the oracle, stored under the ID that EthLib gives, read back with `engine_getPayload`, compared with the oracle's JSON, and sent back through `engine_newPayload`.

Each state machine was checked to bite: a deliberate error in its model made it fail, with a shrunk sequence of three steps for the forkchoice machine.
A trace of one run of the node scenario showed a build returned by every version of `engine_getPayload`, 1 to 6, and a payload accepted by every version of `engine_newPayload`.

## Findings

### 1. BUG (low severity; OPEN on which text rules): upper-case hex digits are refused

- Definition: `EthLib/Serialization/JsonRpc.lean:57` (`hexValue`), used by `bytesOf` (line 72), `uint` (line 100) and every reader of `Engine/Json.lean`.
- Counterexample: `fixed "x" 4 (.str "0x00000A00")`, and the same for `bytes`, `uint64`, `uint256` and each fixed size other than an address.
- EthLib: rejects, so a method answers `-32602`.
- Reference: accepts.
- Source: `common.md`, section Encoding: "Values of a field of `DATA` type **MUST** be encoded as a hexadecimal string with a `0x` prefix matching the regular expression `^0x(?:[a-fA-F0-9]{2})*$`", and for `QUANTITY` "`^0x(?:0|(?:[a-fA-F1-9][a-fA-F0-9]*))$`".
- EthLib cites `base-types.yaml` instead, whose patterns are lower case (`^0x[0-9a-f]*$`), and keeps them; the docstring of `JsonRpc.lean` says so.
- The two texts of one repository disagree, and the Engine API's own prose is the one that says MUST.
- EthLib does not follow the schema either where the schema is looser: `bytes` in the schema matches `0x0`, half a byte, and EthLib refuses it, as `common.md` does.
- So EthLib takes the stricter of the two texts on each point, and refuses a request that `common.md` allows.
- What would decide it: a statement by the maintainers of which text governs the Engine API.
- Command: `lake exe engine-property 1000`, property "a base type reads as the Encoding of common.md says".

### 2. DOC (an omission): no error `-38006: Too deep reorg`

- Definition: `EthLib/Engine/Payload.lean:141` (`EngineError`) and `EthLib/Engine/Json.lean:267` (`EngineError.message`), which says it is "from the table of Errors in `common.md`".
- The table has seven Engine rows, and `EngineError` has six constructors: `-38006` is missing.
- Source: `common.md`, Errors: "| -38006 | Too deep reorg | Reorg depth exceeds limitation. |"; `paris.md`, `engine_forkchoiceUpdatedV1`, step 6: "Client software **MUST** return `-38006: Too deep reorg` error if the depth of reorg to `forkchoiceState.headBlockHash` exceeds the limitation specific to the client software."
- `forkchoiceUpdated` has no such limit, and the module docstring lists "steps 2 to 5, 7, 8 and 9", so step 6 is left out knowingly; the error type and its table are still incomplete, and a client of the C exports cannot name the code.
- Command: `lake exe engine-property`, property "each error code of common.md is an error of EthLib".

### Notes that are not findings

- `engine_forkchoiceUpdatedV3` with attributes in Osaka: `prague.md` says "doesn't fall within the time frame of the Cancun *or Prague* forks", which read alone refuses Osaka; EthLib takes Osaka, and says why in its docstring (no later version takes it, and `amsterdam.md` ends version 3 at Amsterdam). The model follows EthLib here.
- Where the source names two errors and no order (`-32602` and `-38005` in `engine_newPayload`; `-38003` and `-38005` in `engine_forkchoiceUpdated`), the model allows either. EthLib's order was never outside that set.
- `exp` and `nbf` claims are ignored, as `authentication.md` asks ("these **MUST** be ignored"); PyJWT refuses an expired token, so the oracle turns those checks off. HARNESS, fixed.
- A block below the Paris block with a time past Shanghai is of Shanghai by `ChainConfig.activeFork`; my first model said London. HARNESS, fixed.
- PyJWT refuses a header whose `kid` is not a string; the generator no longer writes one. HARNESS, fixed.

## Not covered

- `newPayloadOnChain`, `passesTerminalCheck`, `buildPayload`, `buildPayloadOnChain`, `executionEngine`: they need a `BlockChain` with a real state and a block that passes the state transition; no fixture.
- `PreparePayload.lean`: needs a `BeaconState`; `getPowBlockAtTerminalTotalDifficulty` could be compared with eth2spec and was read against the Bellatrix validator guide only.
- `BeaconApiEvents.lean`: read, not tested.
- `getPayload` with blob transactions: the bundle is always empty, so `validateBlobs` and the KZG checks are not reached, and neither are `blobsBundleOfJson` and `lengthsHold` with a non-empty bundle.
- The JSON readers of the answers of `engine_getBlobs` and `engine_getPayloadBodies` (`blobAndProofV1OfJson`, `blobCellsOfJson`, `bodyV1OfJson`, ...) and `forkchoiceUpdatedResponseOfJson`, `rpcErrorOfJson`, `integer`: not tested.
- JWT: an unpaired surrogate escape in a JSON string (EthLib refuses it, Python accepts it, and RFC 8259 leaves it open), nesting deep enough to exhaust the reader's fuel, and non-ASCII bytes in a token.
- The Glamsterdam header has no second reference: execution-specs 2.20.0 has no Amsterdam fork, so the order "block access list hash, then slot number" is the oracle's reading of EIP-7928 and EIP-7843 and agrees with EthLib.
- The block access list is `0xc0` or plainly not RLP; a list that is RLP and not an access list was not sent.
- Transactions are six fixed ones and three that are not transactions; their decoding by fork belongs to the execution layer.
- The total difficulty rule is tested through the forkchoice tree only, with totals near 100.

## Notes on lean-hedgehog

- `StateMachine` worked well: `transitions` reads the model state, so a step can name a block that exists, and the shrunk counterexample of a fault put into the code on purpose was minimal (one block, two updates).
- `applySut` receives the state after the transition, which let the model carry its expected answer (`last`) to the comparison; this is a convention one has to find, and an `expected` output of `apply` would say it directly.
- `Command.build` takes only the context, not the state, so a command cannot name an existing block when it is generated; the commands carry selectors (a number taken modulo the size of the tree at run time). This works, and it shrinks well, but the label of a command shows the selector, not the block it resolved to; `annotate` inside `apply` fills the gap.
- `scenario .madhouse` fixes the length at 1 to 15 commands and gives each command the same weight. A chain needs more calls to cross its forks, so the long test calls `executeCommands` on its own `Gen.list (.linear 1 60) (Gen.choice …)`, and the weights are set by listing a command twice. A range and weights as parameters of `scenario` would remove both workarounds.
- `scenario` needs `Inhabited σ` and starts from `default`, so an oracle handle cannot live in the state; it lives in each command, put there by `build` from the context.
- There is no `classify`, `cover` or `collect`. Three times a property passed while its generator did not reach the interesting branch (builds past Shanghai, payloads with transactions that pass); I found out only by writing counts to a file from the oracle and to stderr from `apply`. This is the feature I missed most.
- `Gen.sample` in a scratch `#eval` was useful to look at the spread of outcomes of a generator.
- `Gen.zip`, `Gen.frequency`, `Gen.subsequence`, `Gen.shuffle` and `forAllWith` did what the manual says; shrinking through `Gen.frequency` to its first alternative gave readable minimal cases (`"0x00000A00"`, a token with `{"iat":0,"exp":1}`).
- `tripping` wants `BEq` on the decoder's whole result, so it does not fit a decoder into `Except String α` without an instance; I compared `toOption` with `===` instead.
- A failing case whose value is a large JSON object (a 256-byte bloom) prints at full width; a way to cap the shown value would help, and `forAllWith` was the workaround.
- No bug of the library was hit.

# Serialization: property tests

Driver: `Property/Serialization.lean` and `Property/Serialization/*.lean`.
Oracle: `oracle/serialization.py`, with the packages of `oracle/requirements-serialization.txt`.

    cd tests/property
    lake exe serialization-property 1000

The last full run was at 1,000 cases: every property below passed.
A state machine ran 200 sequences (a fifth of the cases), and the madhouse scenarios 1,000.

## References

- SSZ: the Python of [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs) at the revision that `oracle/requirements-serialization.txt` names, the head of the repository on 2026-11-19.
  `EthLib/Serialization/Ssz.lean` names the repository as its source without a revision, and `tests/sources.toml` pins its release v0.1.0, an earlier one.
- SSZ, second: `eth-remerkleable` 0.1.31, which knows the progressive shapes and the compatible union.
- SSZ nodes: a tree written in the oracle from the text of the specification, which must agree with both.
- Merkle proofs: the functions of `consensus-specs` `ssz/merkle-proofs.md`, as written there, and those of `ssz-specs`.
- RLP: `rlp` 5.0.0 in strict mode, and a decoder written in the oracle from Appendix B of the Yellow Paper; the two must agree.
- DER: `cryptography` 50.0.2 for a signature of two integers, and a model of X.690 written in the oracle.
- JSON-RPC: the patterns of `execution-apis` `base-types.yaml`, by Python `re`.
- E2store: a reader written in the oracle from the format document.

The oracle answers `references differ` where two references disagree, so a property fails there too.

## What was tested

42 properties at 1,000 cases each, 11 `StateMachine` properties and 3 `Command` scenarios.

| Property | EthLib definitions | Reference | Cases | Result |
| --- | --- | --- | --- | --- |
| RLP encodes as the reference | `Rlp.encode`, `lengthPrefix`, `encodeBytes` | `rlp` | 1,000 | pass |
| RLP decodes the canonical encodings only | `Rlp.decode`, `decodeItem`, `readPrefix` on mutated encodings | `rlp` strict and the Yellow Paper model | 1,000 | pass |
| RLP decodes inputs at the edge of each form | `Rlp.decode` behind the first bytes `7f` to `ff` | the same | 1,000 | pass |
| RLP scalars are canonical | `Rlp.decodeScalar`, `Item.toScalar` | `rlp` `big_endian_int` | 1,000 | pass |
| typed RLP reads back within its range | `Rlp.Codec` of `Nat`, `UInt8` to `UInt64`, `U256`, `Bool`, `Vector UInt8 n`, `Option`, `List` | arithmetic on `Nat` | 1,000 | pass |
| SSZ serializes and roots as the reference | `Ssz.serialize`, `hashTreeRoot`, `Desc.wellFormed` over generated types | `ssz-specs` and `remerkleable` | 1,000 | pass |
| SSZ deserializes what the reference does | `Ssz.deserialize` on mutated encodings, with the name of the fault of a refusal (`Err.reason`) | `ssz-specs`; `remerkleable` for acceptance | 1,000 | pass |
| SSZ lists far below their limit | the same and `nodeRoot`, at limits `2 ^ 10` to `2 ^ 62 + 1` | `ssz-specs`, `remerkleable`, the tree model | 1,000 | pass |
| SSZ limits of progressive shapes bound the count only | `progressiveList` and `progressiveBitList` with `some limit` | the same type without a limit | 1,000 | pass |
| SSZ sizes are within the bounds of the type | `Desc.minSize`, `maxSize`, `fixedSize` | `remerkleable` `min_byte_length`, `max_byte_length` | 1,000 | pass |
| SSZ defaults are the reference's | `Desc.default`, `isZero`, `Value.fits` | `ssz-specs` `default`, `is_zero`; `remerkleable` | 1,000 | pass |
| SSZ compatibility is the reference's | `isCompatible`, both ways, and `wellFormed` of the union of the two | `ssz-specs` `is_compatible`; `remerkleable` `CompatibleUnion` | 1,000 | pass |
| SSZ declarations are legal as the specification says | `Desc.wellFormed` on near types and illegal ones, with the fault name | `ssz-specs` class creation | 1,000 | pass |
| SSZ refuses a declaration that breaks a rule | `Desc.wellFormed` on 26 illegal declarations inside legal ones | the rules of the specification and the EIPs | 1,000 | pass |
| SSZ layouts are at most 256 positions wide | `Desc.wellFormed`, `maxActiveFields` | EIP-7495 | 255 | pass |
| SSZ paths have the index of the specification | `getGeneralizedIndex`, `resolveStep`, `chunkPosition`, `progressiveChunkGindex`, with the fault name | `ssz-specs` `get_generalized_index`; `merkle-proofs.md` in the oracle | 1,000 | pass |
| SSZ nodes are those of the reference tree | `nodeRoot`, `boundedNode`, `progressiveNode`, `spineWalk`, with the fault name | `ssz-specs` `node_root`, `remerkleable` backing, the tree model | 1,000 | pass |
| SSZ proofs verify, and only for their leaf | `buildProof`, `verifyMerkleProof` | the root of the value | 1,000 | pass |
| SSZ multiproofs of a value rebuild its root | `buildMultiproof`, `verifyMerkleMultiproof` | `calculate_multi_merkle_root` of `consensus-specs` | 1,000 | pass |
| SSZ helper indices are the specification's | `getHelperIndices`, `rejectRelated`, with the fault name | `ssz-specs`; `consensus-specs` | 1,000 | pass |
| SSZ multiproofs rebuild the specification's root | `calculateMultiMerkleRoot` on random nodes | `ssz-specs` and `consensus-specs` | 1,000 | pass |
| SSZ proof requests are answered as the specification does | `calculateMerkleRoot`, `calculateMultiMerkleRoot` with wrong counts, index 0 and 1, with the fault name | `ssz-specs` | 1,000 | pass |
| SSZ branches by depth and index | `isValidMerkleBranch`, `computeMerkleBranchRoot`, `isValidNormalizedMerkleBranch` | `is_valid_merkle_branch` of phase0, in the oracle | 1,000 | pass |
| SSZ documents are those the specification writes | `jsonOf` without a spelling mark | `ssz-specs` `json_writer` | 1,000 | pass |
| SSZ documents under the byte alias | `jsonOf`, `valueOf` with `Spelling.byte` | `ssz-specs` with `Byte` | 1,000 | pass |
| SSZ documents are those of the mapping | `jsonOf` | a writer in the driver | 1,000 | pass |
| SSZ documents read back under every spelling | `jsonOf`, `valueOf`, `Spelling` marks, `Json.parse` | round trip | 1,000 | pass |
| SSZ documents hold integers as digits | `valueOf`, `readNat` on texts near digits | rule | 1,000 | pass |
| SSZ documents near a valid one read as the specification reads them | `valueOf` on mutated documents | `ssz-specs` `validate_json`, one way (see Findings 1) | 1,000 | pass |
| typed SSZ, five types | `SszType.container`, `progressiveContainer`, `SszFields`, `decodeStruct`, `encodeStruct`, `summaryRoot`, `SszList`, `Bitlist`, `Bitvector`, `ProgressiveList`, `ForkList`, `ForkBitlist`, `Since`, `Until` | `ssz-specs`, `remerkleable`, and the untyped decoder | 5 x 1,000 | pass |
| DER reads one tag, length and value | `Der.read` | the X.690 model | 1,000 | pass |
| DER integers are minimal | `Der.exact`, `integer`, `natural` | the model | 1,000 | pass |
| DER signatures read as the reference reads them | `Der.exact`, `children`, `natural` | `cryptography` `decode_dss_signature` | 1,000 | pass |
| DER values are valid as X.690 says | `Der.validate`, `boolean`, `oid`, `validBits`, `fixedString` | the model | 1,000 | pass |
| JSON-RPC readers accept the patterns of the schema | `bytes`, `fixed`, `address`, `uint`, `uint64`, `quantity` | `re` on `base-types.yaml` | 1,000 | pass |
| JSON-RPC writers write the patterns | `quantityJson`, `dataJson` | the same | 1,000 | pass |
| JSON-RPC integers are the integral numbers | `integer` behind `Json.parse` | `decimal.Decimal` | 1,000 | pass |
| JSON-RPC error objects read back | `rpcErrorJson`, `rpcErrorOfJson` | round trip and rule | 1,000 | pass |
| StateMachine: fork-chosen lists, ten machines | `RootedForkList.push`, `set`, `ofData`, its `root`, `encode`, `decode`; `updateLevels`, `raiseLevels`, `spineWrite`, `spineRoot`, `packedChunk` | `ssz-specs` and `remerkleable` on the model list, after every write | 10 x 200 sequences of up to 50 | pass |
| StateMachine: an RLP stream is read in the order written | `Rlp.decodeItem` at a position, `lengthPrefix`, `decode` | the queue of items | 1,000 sequences of up to 40 | pass |
| Command, madhouse: rooted vectors keep their trees | `RootedVector.set`, `shift`, `ofVector`, its `root`, `decode` | the references on the model | 1,000 sequences | pass |
| Command, madhouse: an e2store file grows by records | `E2store.encode`, `decode`, `decodeFile`, `readHeader`, `recordStarts`, `readIndex` | the reader in the oracle and the model | 1,000 sequences | pass |
| Command, in order: an e2store file as a writer makes it | the same | the same | 1 | pass |

The ten list machines are `List[T, n]` before the switch fork and `ProgressiveList[T]` after it, for `uint64`, `uint16` or `boolean`, `uint256`, `Bytes32` and a container of two fields.
Their transitions are `push`, `pushMany` (up to 40 elements, to cross the runs of 1, 4 and 16 nodes) and `set`.
The vector scenario has seven command types: `SetWord`, `SetPair`, `ShiftWords`, `ShiftPairs`, `Reload`, `CheckRoots` and `SetOutside`, whose check must refuse it.
The file scenario has six: `AppendVersion`, `AppendRecord`, `AppendIndex`, `CheckFile`, `CutFile` and `SetReserved`; the last two test a copy that must be refused and leave the file as it was.

## Findings

No property found a place where EthLib computes something other than its cited source.
Every refusal of the SSZ decoder, of a path, of a node request, of a proof request and of a declaration carries the fault name that `ssz-specs` raises for the same input.
The three notes below are differences from another text, each stated by a docstring.

### 1. DOC (deliberate): the JSON reader is stricter than the reader of `ssz-specs`

- Definition: `Ssz.ofHex`, `EthLib/Serialization/Ssz/Codec/Json.lean:123`.
- Shrunk counterexample: the type `Vector[Vector[ByteList[0], 1], 1]`, the document `[[""]]`.
- EthLib: `Err.hexPrefix`.
- The specification: `json_writer(T).validate_json` reads it as the empty byte list, bytes `0400000004000000`; it also reads `"0102"` as `0x0102`.
- What decides it: `src/ssz/byte_arrays.py` says `"0x0102"  hex digits, the prefix optional`, while the vector format of the same repository (`packages/testing/src/ssz_testing/json_mapping.py`) lists `HEX_PREFIX = "a hex byte string opens with 0x"` among the faults a reader must refuse with.
  EthLib's docstring says the same: "Every hex string the mapping writes carries the marker, so one without it is refused."
  So the code follows the vectors, not the lenient constructor.
- To see it: `printf 'sszjsonread\t["blist",4]\t"0102"\n' | .venv/bin/python -I oracle/serialization.py` answers `0102`, and `Ssz.valueOf (.byteList 4) .opaque (.str "0102")` is an error.
- The property therefore checks one way only: what EthLib reads, the specification reads as the same value.
  I did not classify every document that the specification reads and EthLib refuses; the missing marker is the one class I saw.

### 2. OPEN (no reachable effect): a branch longer than its depth

- Definition: `Ssz.isValidMerkleBranch`, `EthLib/Serialization/Ssz/Merkle/Branch.lean:30`.
- Input: a branch of `depth + 1` nodes whose first `depth` nodes climb to the root.
- EthLib: `false`, since it asks for `depth == branch.length`; its docstring says "a branch of exactly `depth` nodes".
- `is_valid_merkle_branch` of `consensus-specs` phase0 reads `for i in range(depth)` and ignores further nodes, so it answers `true`.
- Every caller in EthLib (`Consensus/Transition/Operations.lean:513`, `DataAvailability/Blob.lean:82`, `Column.lean:209`, `LightClient/Sync.lean:356`) passes a vector whose length is the depth, so no input of the protocol reaches the difference.
- Not shown by a failing property: the driver tests exact lengths only.

### 3. Not a bug: the root as a claim

- `Ssz.calculateMerkleRoot leaf [] 1`, `getHelperIndices [1]` and a multiproof of `[1]` are refused with `rootHasNoBranch`.
- `consensus-specs` `ssz/merkle-proofs.md` answers them (`get_generalized_index_length(1)` is 0, so the root of an empty branch is the leaf).
- `ssz-specs`, the source EthLib cites, refuses them with `ROOT_HAS_NO_BRANCH` ("index one is refused as a claim"), and the property "SSZ proof requests" checks that agreement.

### Harness mistakes, for the record

- `remerkleable` accepts a first offset that leaves a gap; the oracle now requires its encoding to write back.
- `remerkleable` keeps zero subtrees collapsed, so a node inside one was an error; the oracle now has a tree model, held to both references.
- The pattern `bytes` of `base-types.yaml` admits an odd count of digits; the oracle refuses it, as two digits make a byte.
- `decode_dss_signature` takes no negative integer; the property reads naturals.
- The oracle refused a field index out of range by itself, before the specification saw an earlier step of the path that it refuses under another name; it now passes a name the type lacks.
- A pip cache served another commit of `eth-ssz-specs` under the same version 0.1.0; install with `--no-cache-dir`.

## Not covered

- `Serialization/Proofs/` and `Serialization/Exports/` (out of scope).
- Payloads of `2 ^ 32` bytes or more: `offsetOverflow` of SSZ, `dataTooLong` of e2store, `payloadTooLong` of RLP (`2 ^ 64`).
  Too large to generate.
- Zero subtrees deeper than 64 (`maxZeroDepth`): the largest limit generated is `2 ^ 62 + 1`.
- `hashTreeRootM` with another hasher, `Hasher.ofHash`, `hashTreeRootAt` with a low budget.
- `Spelling.digits` and `Spelling.text` against a reference: only the round trip covers them, since `ssz-specs` has no such marks; `SszString` is not tested.
- The full set of documents that `ssz-specs` reads and EthLib refuses (Finding 1).
- `Der.validate` against a second implementation: the X.690 model is mine, and only `INTEGER` inside a `SEQUENCE` is checked against `cryptography`.
  `Der.bitString` (the octet-aligned reader) is not called.
- `E2store` against a real era file; the layout of the header is EthLib's own statement, and the oracle reader was written from the same sentence.
- `Rlp.Codec` fields that a fork adds (`Item.readSince`, `Item.ofSince`) and `RlpError.inField`.
- `instSszTypeIte`, `SszType.forkContainer`, `During` fields, `RootedVector` and `RootedForkList` of `UInt8`, `Rooted`.
- `JsonRpc.fields`, `hasExactly`, `hasOnly`, `nullable`, `array`, `bytesMax`.
- `isCompatible` between unions nested in unions more than one deep: the generator makes few.
- The oracle fails `ruff` rule BLE001 in three places, where it must answer one line whatever a reference raises.

## Notes on lean-hedgehog

What worked well:

- `Gen.frequency` with a list of edges made every structured generator short: a length at 31, 32, 33, a limit at `2 ^ 32 + 1`, a prefix byte at `0xb7`, `0xb8`.
- A recursive generator on a depth (`Gen.sized fun size => genDescOf (min 3 (size.log2 / 2 + 1))`) generates an SSZ type, and a second generator, dependent on the type, a value of it.
  Shrinking of the pair was good: counterexamples came out as `["list",["vec",["bool"],1],0] []` and `["bool"] false` at index 0, which are the least ones.
- `StateMachine.property` shrinks a sequence by dropping transitions and keeps the preconditions, so no shrunk sequence was ever invalid.
- `scenario .madhouse` with the oracle handle as the context: a command that asks the reference (`CHECK`) is a command like any other, so a shrunk failure keeps one write and one check.
- `forAllWith` with the JSON that the oracle reads: the report of a failure is the line to paste into the oracle.
- `annotate` before a comparison (what the specification answered, what EthLib read) made every failure readable without a second run.

What was awkward or missing:

- No `BEq (Except ε α)` in core, so `x === .ok y` does not elaborate; each driver defines the instance or goes through `toOption`.
- `Gen α` has no `Inhabited` instance, so a `partial def` generator (over a nested inductive type, where structural recursion is painful) needs `instance : Inhabited (Gen T) := ⟨pure default⟩` for each `T`.
- `scenario` starts from `default` only: the first state cannot be generated, where `Model.initState` is a generator.
  The madhouse length is fixed at 1 to 15 and the commands are drawn uniformly (`Gen.choice`), so a weight is a command listed twice and a long run is not possible without copying `scenario`.
- `Command.check` is the only place to say that a command must not run.
  A near-valid command that the system must refuse and that must leave the state unchanged has to be written as a command whose `apply` tests a copy and returns the state as it was; a `refused` outcome in the class would say it directly.
- `StateMachine.invariants` sees the system and the model but not the transition, so a check that belongs to one transition (the item a read returned) goes into `applySut`.
- `Model.transitions` generates from the model state alone, which is right, but the state must then carry everything a generator needs (the count of elements for an index); `Repr σ` and `Repr τ` are required by `property` even when `forAllWith` would do.
- The report names a failure as `recheck size seed <property>`: it does not say which property of the group, and a driver has no flag to run one property, so a replay means editing `main`.
- `checkGroup` prints nothing until a property ends, and under a pipe nothing until the group ends: a slow property looks like a hang.
- `at` is a keyword in `do` blocks (`let at ← ...` fails with a parse error far from obvious).

Bugs in the library: none met.

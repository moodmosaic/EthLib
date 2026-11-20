# Serialization: property tests

Driver: `Property/Serialization.lean` and `Property/Serialization/*.lean`.
Oracle: `oracle/serialization.py`, with the packages of `oracle/requirements-serialization.txt`.

    cd tests/property
    lake exe serialization-property 1000

The last full run of the first two rounds was at 1,000 cases: every property below passed.
Round 3 measured what those runs reached, and added to them: see "Round 3: the coverage audit" at the end.
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

In the first two rounds: In the first two rounds: In the first two rounds: In the first two rounds: In the first two rounds: In the first two rounds: In the first two rounds: In the first two rounds: 42 properties at 1,000 cases each, 11 `StateMachine` properties and 3 `Command` scenarios.

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
- In the first two rounds no failing property showed it.
  Round 3 has one, in the group `serialization: findings`, which must fail.

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

This is the list of the first two rounds.
Round 3 covers a part of it, named under "Not covered, after round 3".

This is the list of the first two rounds.
Round 3 covers a part of it, named under "Not covered, after round 3".

This is the list of the first two rounds.
Round 3 covers a part of it, named under "Not covered, after round 3".

This is the list of the first two rounds.
Round 3 covers a part of it, named under "Not covered, after round 3".

This is the list of the first two rounds.
Round 3 covers a part of it, named under "Not covered, after round 3".

This is the list of the first two rounds.
Round 3 covers a part of it, named under "Not covered, after round 3".

This is the list of the first two rounds.
Round 3 covers a part of it, named under "Not covered, after round 3".

This is the list of the first two rounds.
Round 3 covers a part of it, named under "Not covered, after round 3".

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
- The oracle catches every exception in three places, where it must answer one line whatever a reference raises.
  `ruff check` passes on it at the version of the brief of round 3.

## Notes on lean-hedgehog

These are the notes of the first round, on the library of that time.
Version 0.3.0 answers several of them: `BEq` for `Except`, a scenario from a generated state, a range of lengths, the selection of a property from the environment.
The notes on 0.3.0 are at the end of round 3.

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

## Round 3: the coverage audit

The first two rounds wrote the properties above before lean-hedgehog had coverage, and all of them passed.
This round measured what they reached, fixed the generators, and applied the rule of round 3: every general function at every value of its parameters.

    cd tests/property
    lake build serialization-property
    lake exe serialization-property 1000
    HEDGEHOG_ONLY="RLP scalars" lake exe serialization-property 1000
    HEDGEHOG_ONLY=OPEN HEDGEHOG_RECHECK="0 13978334490332751324 1240995187049201753" \
        lake exe serialization-property

The third command runs the properties whose name holds "RLP scalars".
The fourth replays the one case of the finding that a report named, by its size and its seed.

### The result

The driver has 101 properties in five groups: `serialization` (42), `serialization: state machines` (14), `serialization: every parameter` (27), `serialization: rooted values at every length and fork` (17), and `serialization: findings` (1, which must fail).
The first two groups are the 56 properties of the first two rounds, with their generators changed; the next two are new.
At 1,000 cases a run makes 88,657 test cases: a state machine runs 200 sequences, and two typed properties 3,000 cases.
All 100 properties that must pass do, each with the minimums of its classes, and the one finding fails as it must.
1,485 classes are counted, and 1,308 of them have a minimum.
The shares of this section are of the last whole run, `lake exe serialization-property 1000`, which took 22 minutes and ended with the exit code 0.
It was the fourth run of every property in a row with no failure; the three before it ran the driver in thirteen parts side by side.

No property found a place where EthLib computes something other than its cited source.
The new classes found eight faults of the harness or of a reference, listed under "Harness mistakes of round 3".
The run on the pinned release gave two notes on documentation, listed under "Findings of round 3".

### Step 1: what the passing properties did not reach

Every property now names its classes with `classify`: one per form of an RLP prefix, constructor of an SSZ type, size of a tree and reason of a refusal.
A class that no case has is listed at 0.0%, so an unreached branch shows.
The classes are read from the code under test, and the helpers are in `Property/Serialization/Classes.lean`.

The shares below are of 1,000 cases with the generators as the first two rounds left them.
A state machine ran 200 sequences.
The complete tables are at the end of this section, and a share under 3% is in bold there.

What a passing property did not test:

- RLP, the decoder: an input whose first byte announces a length on three to eight bytes was 0.0% to 0.3% of the cases for each count, and 1.7% for a list on eight.
  "Long form for a short length" was refused in 0.0% of the cases, "leading zero in a length" in 0.2%.
  No string and no list payload had 65,536 bytes or more, so no encoder case wrote a length on three bytes.
- RLP, scalars: no input was a list (0.0%), and 0.5% had a leading zero.
- Typed RLP: no scalar reached `2 ^ 256`, so the bound of `U256` was never tested; 2.2% of the byte strings had the 20 bytes of the type.
- SSZ, merkleization: in the main property no tree had a zero subtree deeper than 7 levels (0.0% for 8 to 31, 32 to 63, 64, and 65 or more).
  The dedicated property stopped at a limit of `2 ^ 62 + 1`, so no case asked for a zero root at depth 64, the last of the table, or past it.
  No progressive value had five runs or more (86 leaves): 0.0% in the two properties that generate them.
- SSZ, bitfields: each of the lengths 7, 8, 9, 255, 256 and 257 was in under 3% of the cases (0.9% for 9).
- SSZ, the decoder: of the 16 reasons of refusal that it can reach, 11 were under 3%.
  `OFFSET_BELOW_TABLE` 0.0%, `TRAILING_ZEROS` 0.1%, `NO_DELIMITER` 0.2%, `NO_SELECTOR` 0.3%, `OFFSET_UNALIGNED` 0.4%, `EMPTY_ENCODING` 0.8%.
  The typed decoders were worse: the fixed container was refused for `SCOPE` and `PADDING_BITS` only.
- SSZ, proofs: "proofs verify, and only for their leaf" checked nothing in 67.7% of its cases.
  35.4% had no node at the index and 32.3% asked for the root, which has no proof; both passed in silence.
- SSZ, multiproofs of a value: 21.4% of the cases built a proof, 20.1% for one index and 1.3% for two.
  No case had three indices: the property named for multiproofs tested single proofs.
  49.0% had no node at an index and checked nothing.
- SSZ, helper indices: 39.3% of the requests were empty, since `Gen.list (.linear 0 6)` gives no element at a small size.
  No request held the index 0, and 0.6% repeated an index.
- SSZ, proof requests: a proof had the right count of nodes in one case of eight, so 8.6% of the single requests and 7.1% of the multiple ones were answered.
  The weights of the generator were the wrong way round: one node short in six draws of eight.
- SSZ, compatibility: two different vectors, lists or containers that merkleize alike were 0.6%, 0.8% and 0.4% of the pairs.
- SSZ, paths: a step into a byte vector, a byte list, a bit vector, a bitlist or a progressive bitlist was under 3% each.
- SSZ, documents: of the refusals of the reader, `BITFIELD_PADDING`, `BITFIELD_DELIMITER`, `ELEMENT_KIND` and `EMPTY_ENCODING` were at 0.0%.
- DER, signatures: 1.3% of the signatures were read; 72.5% were refused for the form of a length.
  DER integers: the integer 0 was 0.1% of the cases.
- JSON-RPC: a hash of 32 bytes was read in 0.2% of the cases, an address in 1.3%, a `bytes8` in 1.8%.
  A quantity over `2 ^ 256` that `uint` reads was 0.1%.
- E2store: a cut of a file fell between two records in 0.8% of the sequences.
- The list machines: no progressive list reached 342 nodes (six runs), and one reached 86 nodes (five runs) in 0.0% to 4.5% of the sequences, by its element type.

Of the 1,101 classes counted in that run, 447 were under 3%, and 210 of those had no case at all.
With the generators of round 3, 133 of the 447 are at 3% or more, and 77 are still under it.
The other 237 are no longer counted: a class that the code cannot reach in that property, the kind of the root where three properties drew from one generator, or a family that is now counted by constructor.
The driver now counts 1,486 classes in 101 properties, and 128 are under 3%; they are explained under Step 2.

The share of a class that the code cannot reach is not a gap, and such classes were taken out of the lists as they were found:

- `TRUNCATED` of the SSZ decoder: `deserialize` checks the size of a struct before it reads its fixed part.
  The two readers that give it (`readSlots`, `readByteSlots`) now have a property that calls them directly.
- A proof that ends at the root or under a mixed-in word, a byte array "compatible, not the same" with another byte array, a tag 4 that is not valid, a `value` or `trailing` verdict of `Der.read`.
- The reasons that a typed container cannot give: each typed property lists those that the parts of its type can give (`reachableReasons` in `Near.lean`), and the decoder property checks that no refusal is outside that list.

### Step 2: the generators, and the minimums

The generators were changed until each class that the code can reach is common.
No property was weakened: where a check changed, it became stricter.
The bound of `U256` is checked, an ancestor of an index is found at any distance, and a refusal of the decoder must be one that the parts of the type can give.

- RLP items (`genRlpBytes`, `genItemOf`): strings of 259 to 65,535 bytes and of 65,536 to 70,000 bytes, lists of 250 items, and five levels of nesting.
  A long string is one byte repeated (`genRun`), since a list generator of 65,536 elements with their shrinks is slow.
- RLP inputs (`genRlpNear`, `genHeaded` in `Params.lean`): the three forms that the encoder never writes, at the root and inside a list, an item that runs past the end of its list, and a first byte of every form with its length bytes built directly.
- RLP scalars: lists, scalars behind zero bytes.
- SSZ types (`genLeaf`, `genDescOf`): limits of `2 ^ 10` to `2 ^ 80`, and one more, on lists, byte lists and bitlists (`genHugeLimit`); bit shapes twice as often.
- SSZ values: bit counts at 0, 1, 7, 8, 9, 255, 256 and 257 (`genBitCount`); progressive values of 85, 86, 341 and 342 nodes; now and then 65,536 bytes or more, so that an offset takes three bytes.
  A struct value keeps a value for each field when it shrinks (`Gen.sequence` with `atLeast`).
- SSZ near-encodings (`Property/Serialization/Near.lean`): a fault made for the type, at the root or inside a part at any depth.
  The parts are cut from a valid encoding and joined again by `splitParts` and `joinParts`, written there from the specification.
  The property checks that the parts of the valid encoding join to it again.
- SSZ indices: `genNodeIndex` and `genNodeIndices` draw several indices and keep those at which the value has a node, so a proof is built in most cases; `genGindex` also draws indices 17 to 70 levels down.
- SSZ requests (`genIndices`): one to six indices, then a sibling, a parent, a child, a repeat or the index 0.
- SSZ near types (`genNear`): `respelled`, the same tree with every byte array under its other spelling.
- SSZ paths: `genShallow`, a type with bytes or bits at its root or one step under it.
- SSZ documents (`genJsonNear`): a byte more, a byte fewer, no byte, a zero byte, an array in the place of a string, a member fewer.
  `genDocumentFault` makes a fault for the type, at any depth: an integer one over its width, a bitfield without its delimiter, a list one over its limit, a selector the union lacks.
- DER: signatures of two natural numbers in the shortest form three times in four; integers of one octet; `genBadContent`, a content that breaks one rule of its tag.
- JSON-RPC (`genHexText`): five texts in nine hold digits of the pattern only, and the counts 16, 40 and 64 are drawn three times in eight.
- E2store: `CutFile` and `SetReserved` are built for the state (`buildIn`), with `next` on the three commands that append.
- The list machines: a push of 60 to 300 elements, one transition in seventeen, and now and then a start at the end of a run of the spine or at the limit (`startsOf`).
- The two typed properties that cross element types, collections, lengths and forks run three times the cases.

The minimums are one table, `Property/Serialization/Minimums.lean`, made from the reports of two runs of 1,000 cases.
A class has a third of the lesser of its two shares as its minimum, a fifth in a property of fewer than 1,000 cases, and none under 3%.
`covering` in `Classes.lean` sets them on the journal of a property, so a class is named where it is counted and its minimum is data.
The driver asks them of a run of 1,000 cases or more only: at 100 cases a class of 3% has three cases, and a minimum of 1% would fail one run in twenty.

Classes that stay under 3%, and why:

- The kind of the root in "SSZ serializes and roots" and in the decoder: a root is one type of 27 kinds, so most kinds are under 3% there (0.4% to 2.4%).
  A kind is counted where the code meets it, at any depth, under "holds", and each is at 8% or more.
- The classes of the tree of the root that need a great limit or a long spine, in the properties that draw any type (`genTyped`): a zero subtree of 8 levels or more, the zero root of depth 64, a spine of four runs or more (0.3% to 2.9%).
  Each has a property of its own where it is common: "SSZ lists far below their limit", "SSZ limits of progressive shapes bound the count only", "SSZ merkleizes under every capacity and hasher", "SSZ progressive spines from every level" and "SSZ zero subtrees of every depth".
- An RLP input whose first byte announces a length on four to eight bytes, in "RLP decodes the canonical encodings only" (0.9% to 2.3% each) and in "RLP decodes inputs at the edge of each form": 16 forms share the inputs that are built from a first byte.
  "RLP reads a length on every count of bytes" has each form at 4% or more, and runs the whole decoder on them.
- One fork of 29, one element type of 12, one collection of 10, in the two typed properties that cross them (2.2% to 2.9%).
  These two run 3,000 cases, so a class of 2% has 60 cases.
- A count of nodes that an element type cannot reach in a machine: 342 nodes of booleans are 87,552 elements, and a start above 3,000 elements is left out.
- "Command, in order": one test, so a share is 0% or 100%.
- Refusals at 1% to 3%, which were at 0.0% to 2.0%: `OFFSET_UNALIGNED`, `OFFSET_UNORDERED`, `NOT_A_BIT`, `NO_SELECTOR` and `UNKNOWN_SELECTOR` of the SSZ decoder; seven reasons of the reader of documents; four reasons of a declaration; two of a multiproof of a value.
  Each has 10 to 29 cases of 1,000, and its share moves by a point from run to run, so it has no minimum.
- A handful of classes within a point of 3%, named in the tables.

### Step 3: every general function at every value of its parameters

The new properties are in `Params.lean` (RLP, merkleization), `Shapes.lean` (SSZ) and `Formats.lean` (DER, e2store, JSON-RPC).
Their references are in `oracle/serialization_params.py`, written from the texts, with no package.

| Function | Parameters and case splits | Property that generates each |
| --- | --- | --- |
| `Rlp.lengthPrefix kind length` | both kinds; a length in the first byte, on 1 to 8 bytes, and `2 ^ 64` or more, which has no prefix | RLP prefixes of every length |
| `Rlp.readPrefix input first pos stop` | the four forms of the first byte; a length on 1 to 8 bytes; bytes missing, a leading zero, a length below 56 | RLP reads a length on every count of bytes |
| `Rlp.decodeItem input pos stop`, `decodeItems`, `decodeItemsFrom` | a position past the start, a stop before the end, each refusal | RLP reads an item between every two positions; the stream machine |
| `Rlp.bigEndian n`, `bigEndianAux`, `ofBigEndian`, `readBigEndian input pos k acc` | numbers of 0 to 75 bytes; a value before the digits; a position inside other bytes | RLP numbers of every size in base 256 |
| `Rlp.encode`, `encodeBytes`, `joinEncodings` | each class of string and of list payload, five levels | RLP encodes as the reference |
| `Item.toScalar`, `decodeScalar` | a list, a leading zero, 0, numbers up to 65,535 bytes | RLP scalars are canonical |
| `Item.toScalarBelow bits`; `Codec` of `Nat`, `U256`, `UInt64`, `UInt32`, `UInt16`, `UInt8`, `Bool` | every count of bits from 0 to 300, at `2 ^ bits - 1`, `2 ^ bits` and around | RLP scalars below every power of two |
| `Codec (Vector UInt8 n)`, `Codec (Option α)`, `Codec ByteArray`, `Codec Item`, `Codec (List α)` | every length from 0 to 64; a list in the place of bytes | typed RLP: byte strings of every length, fields of every fork |
| `Item.fields count`, `Item.readField count`, `Item.field index` | counts 0 to 6; the index of a field that holds no value | the same |
| `Item.ofSince`, `Item.sinceCount f fork`, `Item.readSince` | every pair of the 29 forks | the same |
| `Ssz.uintBytes width n`, `readUint data start width`, `uintFits`; `serialize`, `deserialize`, `hashTreeRoot` at `.uint width`; `SszType.encodeUint`, `decodeUint`, `ofUint`, `pushUintBytes`, `readUintBytes` | every width from 0 to 70 bytes, not the six that name a type only; a start inside other bytes; a value that does not fit | SSZ integers of every width |
| `packBits`, `packByte`, `packBitsDelimited`, `unpackBits`, `unpackDelimited`, `highestBit` | 0, 1, 7, 8, 9, 255, 256, 257 bits and any count up to 22,271; a delimiter at each bit of a byte | SSZ serializes and roots; SSZ deserializes; typed SSZ: collections |
| `serialize`, `deserialize`, `assemble`, `headOf`, `bodiesOf`, `vectorSlices`, `listSlices`, `structSlots`, `structBodies`, `unpackDelimited`, `deserializeOption` | each of the 13 constructors, at the root and nested; fixed and variable parts; each of the 17 refusals that `deserialize` reaches | SSZ serializes and roots; SSZ deserializes |
| `readSlots fields data position`, `readByteSlots`, `structBudget fields scope`, `offsetSpans offsets scope` | any position; bytes that end inside the fixed part (`TRUNCATED`, which `deserialize` never meets); offsets in order, back, past the end | SSZ slots and spans of every layout |
| `depthFor`, `nextPow2`, `lengthWord count`, `activeFieldsWord active` | counts up to `2 ^ 256`; layouts of 0 to 256 positions | SSZ zero subtrees of every depth |
| `zeroSubtree depth`, `zeroRoots`, `zeroRoot`, `zeroRootM` | every depth from 0 to 100: in the table, 64 (its last entry), 65 and more (folded) | SSZ zero subtrees of every depth |
| `Hasher`, `Hasher.ofHash hash`, `sha256Hasher`, `combineM hash`, `subtreeAtM hasher chunks depth start`, `merkleizeBoundedUncheckedM hasher chunks limit` | four hashers (the table of SHA-256, SHA-256 folded, SHA-256 twice, a toy hash); no limit, under the count, the count, a power of two up to `2 ^ 80`, one over | SSZ merkleizes under every capacity and hasher |
| `progressiveWindows chunks level`, `merkleizeProgressiveUncheckedM hasher chunks level`, `merkleizeProgressiveFrom chunks width`, `spineM` | levels 0 to 4; none to four runs and more; a last run that is full | SSZ progressive spines from every level |
| `hashTreeRootM hasher`, `hashTreeRootAtM budget`, `layoutChunksAtM` | three hashes in a monad that counts its calls; every budget from 0 to past the nesting | SSZ roots under every hasher; SSZ roots with every budget of nesting |
| `merkleLayout`, `sequenceLayout`, `layoutSlots`, `placeSlots`, `merkleizeBoundedUnchecked` | limits 0, 1, the count, not a power of two, `2 ^ 10` to `2 ^ 250` and one over | SSZ serializes and roots; SSZ lists far below their limit |
| `nodeRootAt`, `boundedNode`, `progressiveNode`, `spineWalk`, `buildProof`, `buildMultiproof` | indices at the root, the word, under the word, on a spine, inside the tree, under a leaf, down to 71 levels; each refusal | SSZ nodes; SSZ proofs verify; SSZ multiproofs of a value |
| `gindexDepth`, `gindexLength`, `gindexConcat outer inner`, `gindexRebase index depth`, `getSubtreeIndex`, `getPathIndices`, `getBranchIndices` | indices up to `2 ^ 70`; the index 0; the root | SSZ generalized indices of every spine, path and join |
| `progressiveChunkGindex chunk depth spine` | chunks at the ends of the first six runs and up to `2 ^ 40`; a spine from any node and any run | the same |
| `rejectRelated`, `claimPositions`, `getHelperIndices`, `calculateMultiMerkleRoot` | none, one to seven indices; a repeat, a parent, a child, a sibling, the index 0, the root | SSZ helper indices; SSZ multiproofs rebuild; SSZ proof requests |
| `climbBranchM hash index level node branch`, `calculateMerkleRoot`, `computeMerkleBranchRoot leaf branch depth index`, `isValidMerkleBranch`, `isValidNormalizedMerkleBranch` | three hashes; a level above the leaves; depths 0 to 70; a branch longer than its depth; an index of `2 ^ depth` or more | SSZ branches under every hash and depth |
| `Desc.wellFormed`, `maxActiveFields` | each of the 12 reasons, at the root and nested; layouts of 256 and 257 positions | SSZ refuses a declaration; SSZ declarations; SSZ layouts |
| `isCompatible`, `compatibleAt`, `layoutsAgree`, `unionOptionsAgree` | the same type, a byte array against its sequence, each composite constructor with a part respelled | SSZ compatibility |
| `Desc.minSize`, `maxSize`, `fixedSize`, `default` | every constructor; limits up to `2 ^ 80` | SSZ sizes; SSZ defaults |
| `Desc.isZero`, `Value.beq` | the default, the default with one part changed, a value of zero content that is not the default, any value; a type with no default | SSZ values of every type are zero or are not |
| `Value.fits`, and `serialize`, `hashTreeRoot`, `jsonOf` on a value that does not fit | a count, a width or a selector off by one, at the root or inside a part; a struct with a value too few or too many | SSZ values of every near count fit or do not |
| `chunkCount`, `elementType`, `positionCount`, `resolveStep`, `getGeneralizedIndex`, `SszType.getGeneralizedIndex` | a step into each of the 11 composite shapes, each of the seven mixed-in words, each refusal | SSZ paths |
| `Desc.chunkPosition shape step`, `Desc.chunkCount`, `Desc.itemLength` | the chunk, and the first and last byte inside it, which no generalized index reads; positions 0 to 600; elements that start a chunk, start inside one, end one, or are a bit | SSZ chunk positions of every element |
| `jsonOf shape spelling`, `valueOf`, `readNat`, `ofHex`, `readBitfield` | the three marks of a spelling where they change the document; each refusal of the reader | the six properties of SSZ documents |
| `SszType` of `Bool`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `BitVec 128`, `U256`; `Vector UInt8 n`, `Vector α length`, `SszList α limit`, `SszList UInt8 limit`, `Bitvector length`, `Bitlist limit`, `ProgressiveList α`, `ProgressiveBitlist`, `Rooted α`, `instSszTypeIte` | twelve element types; lengths and limits 0, 1, 2, 7, 8, 9, 31, 32, 33, 255, 256, 257 | typed SSZ: collections of every element and length |
| `SszString limit` | the same limits; bytes that spell no text | typed SSZ: texts of every limit |
| `ForkList switch fork α limit`, its `UInt8` instance, `ForkBitlist switch fork limit`, `SszType.forkContainer switch fork`, `Since`, `Until`, `During first last fork`, `sinceNames`, `untilNames`, `duringNames` | every triple of the 29 forks: before, at and after the first and the last | typed SSZ: every pair of forks |
| `RootedVector α length`, `set`, `shift`, `ofVector`; `sequenceLeaves`, `packedChunk`, `perChunk`, `leafCapacity`, `buildLevels`, `updateLevels` | ten element types; lengths 1 to 257, at each edge of a node and of a power of two | rooted vectors of every length |
| `RootedForkList switch fork α limit`, `push`, `set`, `ofData`; `forkListLevels`, `spineLevels`, `spineWrite`, `spineRoot`, `raiseLevels` | seven element types; every pair of forks; limits 1 to 100, `2 ^ 10` to `2 ^ 70` and one over | rooted lists at every pair of forks |
| `Der.read` | each of the 256 tags; the short form, the long form on 1 to 126 octets, `0x80` and `0xff`; what a refusal says is missing | DER reads a value of every tag |
| `Der.readTag tag`, `Der.exact tag`, `Der.children` | the tag of the value and another; bytes after the value | the same; DER signatures |
| `Der.validate`, `boolean`, `integer`, `natural`, `bitString`, `oid`, `validBits` | each of the 13 tags that validation reads, valid and not; every other tag | DER validates a value of every tag; DER values are valid |
| `Der.fixedString width bytes`, `unicodeScalar n` | code points on 1 to 5 octets | DER validates a value of every tag |
| `E2store.encodeHeader type length`, `readHeader bytes offset`, `decodeFrom bytes offset acc`, `recordStarts pos` | every type; a length on each of its four bytes, up to `2 ^ 32 - 1`; an offset past the start; each reserved byte | e2store headers of every type and length |
| `E2store.readIndex`, `readInt64 data pos` | 0 to 5 entries; offsets at the ends of 64 bits; a count that is wrong, or huge | e2store index records of every count |
| `JsonRpc.fixed what n upper`, `bytesOf what upper`, `hexValue upper c`, `bytesMax what n` | every count of bytes from 0 to 96; both cases of the digits | JSON-RPC readers at every width |
| `JsonRpc.quantity what bits`, `uint` | every count of bits from 0 to 300, at `2 ^ bits - 1`, `2 ^ bits` and around; a leading zero | the same |
| `JsonRpc.array`, `paramsArray`, `nullable`, `fields`, `hasExactly`, `hasOnly`, `field`, `bool`, `string`, `listJson`, `optionJson`, `integer` | each kind of JSON value; members that are null; a number of any mantissa and exponent | JSON-RPC readers of every structure |

The model of an integer of any width was held once to `ssz-specs` at its release v0.1.0, which takes any width: 70 widths, four values each, no difference.
The script is not part of the driver, since the driver runs on the head, which takes six widths.

### The reference of SSZ: the head and the pinned release

`pip freeze` in `tests/property/.venv` shows `eth-ssz-specs` installed from the Git revision that `oracle/requirements-serialization.txt` names.
That revision is the head of the repository, 114 commits after the release v0.1.0 that `tests/sources.toml` pins.
The two differ in 41 files under `src/` and `packages/`.

The SSZ properties were run a second time, at 200 cases, on an interpreter with the release v0.1.0 (`ETHLIB_ORACLE_PYTHON`).
That interpreter is a second virtual environment with the packages of `oracle/requirements-serialization.txt`, and `eth-ssz-specs` from `git+https://github.com/ethereum/ssz-specs@v0.1.0`.
Where a property passes on the head and fails on the release, the two differ in behaviour:

| Behaviour | Release v0.1.0 | Head | EthLib |
| --- | --- | --- | --- |
| A zero subtree deeper than 64 levels, as under `List[T, 2 ^ 65]` | refused, `ZERO_TREE_WIDTH` ("a power of two up to 2**64 leaves") | folded from the last root of the table | folded, as the head |
| A struct on fewer bytes than its fixed part | `TRUNCATED` | `SCOPE` | `SCOPE`, as the head |
| The index 0 in a request for several nodes | an assertion fails | `NOT_A_GINDEX` | `NOT_A_GINDEX`, as the head |
| An integer of three bytes | a type | refused, `UINT_WIDTH` | refused, `UINT_WIDTH`, as the head |
| The JSON mapping | absent | `json_writer` | as the head |

So EthLib follows the head in each, and no property disagrees with the head only.
Every disagreement seen is with the pinned release only, and each is a place where the head has moved on.
It is not a finding against EthLib; it does say that `tests/sources.toml` pins an older text than the one the code follows.

### Findings of round 3

No BUG.

#### DOC: an error that nothing raises, with the bound of the pinned release in its docstring

- Definition: `Err.zeroTreeWidth`, `EthLib/Serialization/Ssz/Error.lean:111`.
- Its docstring: "A zero subtree asked for at a width that is no power of two, or past the table."
- No definition under `EthLib/` raises it.
  `zeroSubtree` (`Merkle/Tree.lean`) folds a root past the table, and its comment says "The cache is a shortcut, not a bound".
- The release v0.1.0 of `ssz-specs` raises `ZERO_TREE_WIDTH` past depth 64; the head does not.
  The constructor and its docstring are of the release, the code is of the head.
- To see it, in a file under `tests/property` read with `lake env lean`:

      import EthLib.Serialization.Ssz
      open EthLib.Serialization
      #eval (Ssz.hashTreeRoot (.list (.uint 8) (2 ^ 70)) (.seq [])).toOption.isSome
      #eval Ssz.zeroSubtree 65 == Ssz.zeroRoot Ssz.combine Ssz.zeroChunk 65

  Both are `true`, and the root is `6d157452…3097`, the one the head gives:

      printf 'sszenc\t["list",["uint",8],1180591620717411303424]\t[]\n' |
          .venv/bin/python -I oracle/serialization.py

  The same command on an interpreter with the release v0.1.0 answers "a zero subtree spans a power of two up to 2**64 leaves".

#### DOC: `tests/sources.toml` pins a release that the code has left

- The table of the section above: five behaviours where EthLib is the head and not the release v0.1.0.
- What would decide it: the revision that `EthLib/Serialization/Ssz.lean` means by "the SSZ specification in `ethereum/ssz-specs`"; it names none.

#### OPEN, now shown by a property: a branch longer than its depth

Finding 2 of the first round is now a property of the group `serialization: findings`, which must fail.

    HEDGEHOG_ONLY=OPEN lake exe serialization-property

- Shrunk counterexample: depth 0, index 0, a leaf of 32 zero bytes, a branch of one node of 32 zero bytes, the root equal to the leaf.
- EthLib: `Ssz.isValidMerkleBranch` is `false`; `is_valid_merkle_branch` of phase0 is `true`.
- Nothing changed in the analysis: EthLib's docstring asks for "a branch of exactly `depth` nodes", and every caller passes one.

### Harness mistakes of round 3

Each was found by a class that the first two rounds did not generate.

- The reference of scalars: `rlp.sedes.big_endian_int.deserialize` takes the empty list for 0.
  The first list sent to the scalar decoder (`c0`) showed it; EthLib refuses it with `listAsScalar`, as the Yellow Paper has a scalar a byte string.
  The oracle now refuses a list itself.
- Python refuses to print an integer of more than 4,300 digits; a scalar of 65,535 bytes has more.
  The oracle lifts the limit.
- `unrelated` in the driver looked for an ancestor up to 64 levels up; the index `2 ^ 65` has the index 2 above it.
  EthLib refused the request, rightly, and the helper is now exact.
- `remerkleable` has no tree deeper than 256 levels: a limit of `2 ^ 256 + 1` raises `IndexError`.
  The limits stop at `2 ^ 250 + 1`.
- A struct value shrank to fewer values than fields, which is no value of its type, and a counterexample then showed that fault and not the first one.
  `Gen.sequence` now keeps every field.
- The property of well-formed multiproof requests let the index 0 through, once requests held it.
  `consensus-specs` fails an assertion there and `ssz-specs` answers `NOT_A_GINDEX`; the property now keeps to indices above 1, and "SSZ helper indices" has the index 0.
- `remerkleable` takes no elements for the default vector, so the oracle answered for a vector of one element given none.
  The oracle now holds a vector to its count; EthLib refused the value, rightly.
- A list machine under a limit of 1 or 2 started with up to three elements, and `initSut` threw.
  An exception in `initSut` is not a failed test: it ends the driver with "uncaught exception" and no report (see the notes on the library).

### Not covered, after round 3

Of the list above, these are now covered: `payloadTooLong` of RLP through `lengthPrefix`; zero subtrees deeper than 64; another hasher, `Hasher.ofHash` and a low budget; `SszString`; the fork fields of `Rlp.Codec` and `RlpError.inField`; `instSszTypeIte`, `SszType.forkContainer`, `During`, `RootedVector` and `RootedForkList` of `UInt8`, `Rooted`; `JsonRpc.fields`, `hasExactly`, `hasOnly`, `nullable`, `array`, `bytesMax`; `Der.bitString`.

Still not covered:

- `Serialization/Proofs/` and `Serialization/Exports/`.
- An encoding of `2 ^ 32` bytes or more: `offsetOverflow` of SSZ and `dataTooLong` of e2store.
  `E2store.encodeHeader` is tested up to `2 ^ 32 - 1` directly; above it the header has no meaning.
- An RLP payload of `2 ^ 24` bytes or more that is all there.
  A length on four to eight bytes is read exactly, and the refusal names it, but no such item is decoded whole.
- SSZ trees deeper than 250 levels, and progressive values of seven runs (1,366 leaves) or more.
- The reasons of refusal of the JSON reader against a reference: `ssz-specs` reads more documents than its vectors allow (Finding 1 of the first round), so only the values are compared.
- `Der.validate` against a second implementation: the model of X.690 is the driver's.
- E2store against a real era file.
- `RpcError.invalidParams` and `invalidRequest`, which are constants.
- The integer model above 32 bytes has one source, the release v0.1.0; the head names no such type.

### Notes on lean-hedgehog 0.3.0

The driver ran on the branch for 0.3.0 that `lakefile.toml` pins.

Coverage (`classify`, `label`, `cover`):

- It is the piece that made this round.
  Fifty-six properties had passed twice; the first labelled run showed a proof property that checked nothing in two cases of three, and a multiproof property with no multiproof.
  None of that showed without the shares.
- `classify name false` lists the name at 0.0%.
  This matters more than it looks: the class that no case has is the one to see, and a `label` alone would hide it.
- The labels work inside `StateMachine.applySut`, `invariants` and `Command.apply`, where a share reads "of the sequences, how many reached this".
  That is the right measure for a machine: "reached 342 nodes: 0.0%" said at once that the list machines never filled a fifth run.
- A partition is the common case: one class of several for each case, with the others at zero.
  I wrote `classifyOne kind names name` and `classifyAny kind names found` for it; the library could have them.
- `cover` takes its minimum where the class is counted.
  With a hundred properties and some 1,500 classes I wanted the minimums as data, made from a run: `covering table property` rewrites the minimum of the journal entries by name.
  It needs the constructor `JournalEntry.label` to stay public.
  A library function for it, and a mode that prints "a third of what this run saw" as a table, would save the script.
- USAGE is right that a minimum depends on the run length.
  In practice the driver must switch the minimums off under 1,000 cases, and a property of 200 sequences needs a lower fraction.
  A `cover` that scaled with the number of tests, or the confidence of Haskell's `verifiedTermination`, would remove that.
- A property that fails prints no shares.
  When a new generator met a harness fault at case 299, the shares of the 298 cases before would have been useful.
- The report is text only.
  To compare two runs I parsed it; a `Report.coverage` printed as JSON or CSV by `checkGroup` on request would do.
- The classes print in the order of first use, so those counted only in a late branch come last and out of their group.

`Selection.fromEnv`:

- `HEDGEHOG_ONLY` was used at every step.
  A new group is selected by one word that its names share (`every`).
  A rerun of three properties after a change takes a minute where the driver takes thirty.
  It also splits the driver into processes that run side by side, each with its own oracle: thirteen parts took seven minutes on a loaded machine.
- It selects by the name of a property only.
  The name of a group would be a natural part to match too, and a way to list the names without running would help.
- `HEDGEHOG_RECHECK` with the three numbers of a report replays the case: tried on the finding, same counterexample.
  The report still prints `recheck 0 ⟨a, b⟩ <property>`; printing the line to paste, `HEDGEHOG_ONLY=... HEDGEHOG_RECHECK="0 a b"`, would close the loop.
  A bad value ends the driver with an uncaught exception, which is clear enough.

`mustFail`:

- The finding of the first round that no property showed ("a branch longer than its depth") is now a property in a group that must fail, and its group is part of the exit code.
- The report of such a group reads as any failure, with the cross.
  A line that says "failed, as it must" would keep a reader from taking it for a regression.

The context first in `check`, `apply`, `next`:

- Three commands (`CheckFile`, `CutFile`, `CheckRoots`) held the oracle in a field that `build` copied from the context.
  They now read it as the first argument of `apply`, and two of the three structures have no field left.
- Nothing was awkward; the old form was.

`buildIn` and `next`:

- Used for the e2store file: `CutFile` draws a cut between two records of the file that the commands before lead to, and `SetReserved` a record that the file has.
  "A cut that reads" went from 0.8% of the sequences to 30.6%, and `SET_RESERVED` ran in 43.3% where it ran in 14.0%.
- `next` must be written for every command that moves what `buildIn` reads (three here), and it is easy to forget one: the state then lags and nothing says so.
  A `next` that defaulted to running `apply` on a model is not possible in general, so a sentence in USAGE on this trap is what I would add.

`scenario` with a range:

- Both scenarios now run up to 30 commands (`.linear 1 30`).
  The setup argument was not needed here: the oracle is started once in `main`.

`StateMachine.applySut` with the state before:

- Not needed in this driver; the stream machine reads the state after and subtracts one.

`Property.lift`:

- Four new pure properties are `Property Id` and are lifted in `main`.
  It works, and `covering` applies after it since the labels of a pure property are in the outer journal.

`===` on `Except`:

- The driver had its own `BEq (Except ε α)` from the first round; it is deleted, and the scoped instance of the library serves.

Shrinking:

- Counterexamples were minimal where the generator allowed it.
  `c0` for the scalar reference; `["list",["uint",32],2^256+1] []` at index 1; the pair of indices `[2^65, 2]` under a vector of three empty lists, after 48 shrinks.
- `Gen.sequence` drops elements when it shrinks, as USAGE says.
  For a list of different generators (the fields of a struct) that makes values of no type.
  A failure then shrinks into another failure: "a value of the type was refused" in place of the disagreement that started it.
  `atLeast := fields.length` fixes it, and I would make that the default, or add a `Gen.tuple` that never drops.
- A value drawn with `Gen.element` shrinks to the first element, so a list of lengths should start with the smallest.

Still missing, or awkward:

- `checkGroup` writes each report when its property ends, and through a pipe or a file nothing appears until a buffer fills.
  On a loaded machine the driver looked hung for ten minutes; a flush after each report would do.
- No time per property in the report, which would say which generator to make cheaper.
- `show` and `at` are keywords: `let show ...` and `fun (x, at) => ...` fail far from the cause.
- `Gen.frequency` takes a weight of 0, which is a handy way to switch an alternative off by a condition; USAGE does not say whether that is meant.

One fault of the library, or a gap in USAGE:

- An exception thrown by `StateMachine.initSut` in `IO` is not caught: the driver ends with `uncaught exception: ...`, after the reports of the properties before, and prints no counterexample.
  The same exception inside `applySut` through `evalIO` is a failed test with a shrunk sequence.
  To see it: a machine over `IO` whose `initSut` is `fun _ => throw (IO.userError "no")`, checked with `checkGroup`.
  Here the cause was mine (a start state that did not fit a limit), but the report gave no state and no seed to find it with.

### Every share, before and after

A share is of 1,000 cases, or of the count its heading names.
"Before" is with the generators of the first two rounds, "After" with those of round 3.
A share under 3% is in bold.
"new" marks a property of round 3, and "-" a class that was not counted before.
"Minimum" is what `Minimums.lean` asks of a run of 1,000 cases.

#### Group `serialization`

**RLP encodes as the reference** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| root: a byte below 0x80 | 12.2% | 5.1% | 1% |
| root: string of 0 | 5.7% | 4.1% |  |
| root: string of 1, 0x80 or more | 11.2% | 5.4% | 1% |
| root: string of 2 to 55 | 12.3% | 5.6% | 1% |
| root: string of 56 to 255 | 7.2% | 4.1% | 1% |
| root: string of 256 to 65535 | **2.6%** | 4.4% | 1% |
| root: string of 65536 or more | **0.0%** | 3.5% | 1% |
| root: list payload of 0 | 13.2% | 17.5% | 5% |
| root: list payload of 1 to 55 | 19.1% | 17.6% | 6% |
| root: list payload of 56 to 255 | 13.3% | 13.6% | 5% |
| root: list payload of 256 to 65535 | 3.2% | 14.6% | 3% |
| root: list payload of 65536 or more | **0.0%** | 4.5% | 1% |
| holds: a byte below 0x80 | 18.9% | 9.4% | 3% |
| holds: string of 0 | 30.8% | 43.1% | 14% |
| holds: string of 1, 0x80 or more | 16.9% | 10.3% | 3% |
| holds: string of 2 to 55 | 19.6% | 10.6% | 3% |
| holds: string of 56 to 255 | 11.4% | 7.9% | 2% |
| holds: string of 256 to 65535 | 4.2% | 9.1% | 2% |
| holds: string of 65536 or more | **0.0%** | 6.7% | 2% |
| holds: list payload of 0 | 17.3% | 25.1% | 8% |
| holds: list payload of 1 to 55 | 23.8% | 23.7% | 8% |
| holds: list payload of 56 to 255 | 14.1% | 19.9% | 7% |
| holds: list payload of 256 to 65535 | 3.2% | 15.8% | 4% |
| holds: list payload of 65536 or more | **0.0%** | 4.5% | 1% |
| depth: 0 | 51.2% | 32.2% | 10% |
| depth: 1 | 35.1% | 46.4% | 14% |
| depth: 2 | 8.0% | 12.1% | 4% |
| depth: 3 | 5.7% | 4.3% | 1% |
| depth: 4 or more | **0.0%** | 5.0% | 1% |

**RLP decodes the canonical encodings only** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| input: no byte | 10.2% | 4.9% | 1% |
| input: a byte below 0x80 | 20.1% | 5.6% | 2% |
| input: short string | 20.7% | 8.7% | 2% |
| input: short list | 24.9% | 19.3% | 5% |
| input: long string, length on 1 | 6.4% | 6.8% | 2% |
| input: long string, length on 2 | 3.0% | 6.5% | 2% |
| input: long string, length on 3 | **0.0%** | 3.4% | 1% |
| input: long string, length on 4 | **0.1%** | **1.4%** |  |
| input: long string, length on 5 | **0.0%** | **1.9%** |  |
| input: long string, length on 6 | **0.1%** | **1.8%** |  |
| input: long string, length on 7 | **0.0%** | **2.1%** |  |
| input: long string, length on 8 | **0.3%** | **1.4%** |  |
| input: long list, length on 1 | 9.1% | 11.1% | 3% |
| input: long list, length on 2 | **2.9%** | 11.1% | 3% |
| input: long list, length on 3 | **0.2%** | 4.4% | 1% |
| input: long list, length on 4 | **0.0%** | **1.9%** |  |
| input: long list, length on 5 | **0.0%** | **1.1%** |  |
| input: long list, length on 6 | **0.0%** | **2.3%** |  |
| input: long list, length on 7 | **0.3%** | **1.6%** |  |
| input: long list, length on 8 | **1.7%** | **2.7%** |  |
| verdict: accepted | 40.8% | 20.7% | 6% |
| verdict: input too short | 35.3% | 41.7% | 13% |
| verdict: a byte below 0x80 with a prefix | **1.6%** | 4.4% | 1% |
| verdict: long form for a short length | **0.0%** | 6.7% | 2% |
| verdict: leading zero in a length | **0.2%** | 14.1% | 3% |
| verdict: trailing bytes | 22.1% | 12.4% | 3% |
| the encoding of an item, unchanged | 17.0% | 4.2% | 1% |

**RLP scalars are canonical** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 72.4% | 41.4% | 14% |
| verdict: input too short | 11.6% | 11.1% | 3% |
| verdict: a byte below 0x80 with a prefix | **0.2%** | 3.6% | 1% |
| verdict: long form for a short length | **0.0%** | 3.2% |  |
| verdict: leading zero in a length | **0.0%** | 4.7% | 1% |
| verdict: trailing bytes | 15.3% | 7.4% | 2% |
| verdict: leading zero in a scalar | **0.5%** | 16.4% | 5% |
| verdict: a list as a scalar | **0.0%** | 12.2% | 3% |
| scalar: none | 27.6% | 58.6% | 19% |
| scalar: 0 | 9.9% | 5.3% | 1% |
| scalar: 1 to 127 | 4.0% | 8.2% | 2% |
| scalar: 128 to 2^64 - 1 | 20.6% | 10.7% | 3% |
| scalar: 2^64 or more | 37.9% | 17.2% | 5% |

**SSZ serializes and roots as the reference** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| root: boolean | **1.9%** | **1.1%** |  |
| root: uint8 | **0.5%** | **0.6%** |  |
| root: uint16 | **1.0%** | **1.2%** |  |
| root: uint32 | **0.7%** | **1.0%** |  |
| root: uint64 | **1.1%** | **0.6%** |  |
| root: uint128 | **0.9%** | **0.8%** |  |
| root: uint256 | **1.1%** | **0.5%** |  |
| root: ByteVector | **2.6%** | **1.1%** |  |
| root: ByteList | **2.4%** | 3.7% | 1% |
| root: Bitvector | **2.3%** | **2.0%** |  |
| root: Bitlist | 3.1% | 5.5% | 1% |
| root: ProgressiveBitlist | **2.7%** | **1.9%** |  |
| root: Vector of basic | **1.0%** | **1.1%** |  |
| root: Vector of fixed composite | **2.9%** | **1.3%** |  |
| root: Vector of variable | 11.8% | 12.2% | 3% |
| root: List of basic | **0.8%** | **0.9%** |  |
| root: List of fixed composite | 3.6% | **2.0%** |  |
| root: List of variable | 10.6% | 11.6% | 3% |
| root: ProgressiveList of basic | **1.7%** | **1.2%** |  |
| root: ProgressiveList of fixed composite | **2.9%** | **1.8%** |  |
| root: ProgressiveList of variable | 9.9% | 10.9% | 3% |
| root: Container, fixed | **2.1%** | **1.6%** |  |
| root: Container, variable | 11.9% | 13.0% | 3% |
| root: ProgressiveContainer, fixed | **1.7%** | **1.1%** |  |
| root: ProgressiveContainer, variable | 4.7% | 5.3% | 1% |
| root: ProgressiveContainer with a gap | 7.1% | 8.6% | 2% |
| root: CompatibleUnion | 7.0% | 7.4% | 2% |
| holds: boolean | 10.6% | 5.4% | 1% |
| holds: uint8 | 10.6% | 6.5% | 2% |
| holds: uint16 | 9.0% | 6.1% | 1% |
| holds: uint32 | 7.2% | 7.8% | 2% |
| holds: uint64 | 9.5% | 5.6% | 1% |
| holds: uint128 | 8.2% | 8.7% | 1% |
| holds: uint256 | 8.4% | 5.6% | 1% |
| holds: ByteVector | 18.8% | 9.8% | 3% |
| holds: ByteList | 19.9% | 25.3% | 8% |
| holds: Bitvector | 18.0% | 18.3% | 6% |
| holds: Bitlist | 21.2% | 34.0% | 11% |
| holds: ProgressiveBitlist | 20.6% | 20.1% | 6% |
| holds: Vector of basic | 9.7% | 6.4% | 1% |
| holds: Vector of fixed composite | 8.7% | 5.1% | 1% |
| holds: Vector of variable | 22.7% | 25.4% | 7% |
| holds: List of basic | 7.8% | 6.2% | 1% |
| holds: List of fixed composite | 10.0% | 7.1% | 2% |
| holds: List of variable | 20.6% | 25.5% | 7% |
| holds: ProgressiveList of basic | 8.4% | 5.6% | 1% |
| holds: ProgressiveList of fixed composite | 8.5% | 6.1% | 2% |
| holds: ProgressiveList of variable | 21.4% | 24.0% | 8% |
| holds: Container, fixed | 9.0% | 7.8% | 1% |
| holds: Container, variable | 24.1% | 27.5% | 7% |
| holds: ProgressiveContainer, fixed | 5.2% | 3.5% | 1% |
| holds: ProgressiveContainer, variable | 12.0% | 11.2% | 3% |
| holds: ProgressiveContainer with a gap | 18.9% | 19.4% | 6% |
| holds: CompatibleUnion | 18.6% | 19.1% | 5% |
| nesting: 1 | 20.3% | 20.0% | 7% |
| nesting: 2 | 17.3% | 17.0% | 5% |
| nesting: 3 | 15.7% | 18.2% | 4% |
| nesting: 4 or more | 46.7% | 44.8% | 14% |
| size: fixed | 20.6% | 14.8% | 4% |
| size: variable | 79.4% | 85.2% | 27% |
| root: leaves: none | 12.2% | 9.9% | 3% |
| root: leaves: one | 39.5% | 42.4% | 14% |
| root: leaves: a power of two | 20.7% | 19.1% | 5% |
| root: leaves: one over a power of two | 15.8% | 13.0% | 3% |
| root: leaves: another count | 11.8% | 15.6% | 4% |
| root: capacity: 0 | 3.8% | **1.3%** |  |
| root: capacity: full | 53.6% | 49.3% | 15% |
| root: capacity: a power of two, not full | 7.3% | 11.6% | 3% |
| root: capacity: not a power of two, not full | 4.6% | 7.0% | 1% |
| root: zero subtree: none | 61.2% | 53.2% | 16% |
| root: zero subtree: 1 to 7 | 8.1% | 5.5% | 1% |
| root: zero subtree: 8 to 31 | **0.0%** | **1.4%** |  |
| root: zero subtree: 32 to 63 | **0.0%** | 4.2% | 1% |
| root: zero subtree: 64 | **0.0%** | **0.5%** |  |
| root: zero subtree: 65 or more | **0.0%** | 4.4% | 1% |
| root: spine: no run | **1.1%** | **0.9%** |  |
| root: spine: one run | 6.2% | 6.4% | 2% |
| root: spine: two runs | 10.3% | 8.1% | 2% |
| root: spine: three runs | 9.5% | 8.4% | 2% |
| root: spine: four runs | - | 3.2% |  |
| root: spine: five runs | - | **2.8%** | 1% |
| root: spine: six runs or more | - | **1.0%** |  |
| root: spine: its last run is full | 9.9% | 11.3% | 3% |
| root: asks the zero root of depth 64, the last of the table | - | **0.7%** |  |
| root: asks a zero root of depth 65 or more, which is folded | - | 4.0% | 1% |
| root: mixes a word in | 58.2% | 61.9% | 21% |
| holds: bits: 0 | 15.4% | 21.3% | 7% |
| holds: bits: 1 | 10.1% | 18.2% | 6% |
| holds: bits: 7 | **2.9%** | 14.9% | 4% |
| holds: bits: 8 | **2.4%** | 14.3% | 4% |
| holds: bits: 9 | **0.9%** | 14.0% | 4% |
| holds: bits: 255 | **2.4%** | 10.3% | 3% |
| holds: bits: 256 | **2.8%** | 10.0% | 3% |
| holds: bits: 257 | **2.6%** | 10.1% | 3% |
| holds: bits: another count | 25.7% | 26.3% | 8% |
| holds: a list at its limit | 21.0% | 13.1% | 4% |
| holds: a list of none | 39.3% | 36.9% | 12% |
| holds: a union | 16.7% | 18.3% | 5% |
| bytes: no byte | 11.2% | 8.3% | 3% |
| bytes: 1 to 31 | 38.6% | 38.9% | 12% |
| bytes: 32 | 3.9% | **2.2%** | 1% |
| bytes: a multiple of 32 above it | 4.9% | 4.6% |  |
| bytes: another size above 32 | 41.4% | 42.1% | 13% |
| bytes: 65536 or more | - | 3.9% | 1% |

**SSZ deserializes what the reference does** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 56.3% | 23.2% | 7% |
| verdict: SCOPE | 11.1% | 11.8% | 3% |
| verdict: SCOPE_TOO_SMALL | 5.8% | 5.9% | 1% |
| verdict: SCOPE_UNDIVIDED | 4.1% | 6.2% | 1% |
| verdict: FIRST_OFFSET | 5.2% | 9.8% | 3% |
| verdict: OFFSET_UNORDERED | **2.0%** | **2.2%** |  |
| verdict: OFFSET_PAST_SCOPE | 6.3% | 4.8% | 1% |
| verdict: OFFSET_UNALIGNED | **0.4%** | **2.8%** |  |
| verdict: OFFSET_BELOW_TABLE | **0.0%** | 3.6% | 1% |
| verdict: NOT_A_BIT | **1.9%** | **2.1%** |  |
| verdict: PADDING_BITS | **1.3%** | 3.1% | 1% |
| verdict: EMPTY_ENCODING | **0.8%** | 4.2% | 1% |
| verdict: NO_DELIMITER | **0.2%** | 5.5% | 1% |
| verdict: TRAILING_ZEROS | **0.1%** | 5.9% | 1% |
| verdict: NO_SELECTOR | **0.3%** | **1.5%** |  |
| verdict: UNKNOWN_SELECTOR | **1.5%** | **2.4%** |  |
| verdict: LIMIT | **2.7%** | 5.0% | 1% |
| the encoding of a value, unchanged | 26.1% | 12.4% | 3% |
| root: boolean | **1.2%** | **0.6%** |  |
| root: uint | - | 4.7% | 1% |
| root: ByteVector | **2.0%** | **0.6%** |  |
| root: ByteList | **2.7%** | 4.1% | 1% |
| root: Bitvector | 3.3% | 3.0% |  |
| root: Bitlist | **2.9%** | 4.8% | 1% |
| root: ProgressiveBitlist | **2.8%** | 3.3% |  |
| root: Vector | - | 13.6% | 4% |
| root: List | - | 16.7% | 4% |
| root: ProgressiveList | - | 14.5% | 4% |
| root: Container | - | 12.5% | 4% |
| root: ProgressiveContainer | - | 14.3% | 4% |
| root: CompatibleUnion | 7.6% | 7.3% | 2% |

**SSZ sizes are within the bounds of the type** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| size: fixed | 20.9% | 15.4% | 4% |
| size: variable with a bound | 33.6% | 41.4% | 13% |
| size: variable with no bound | 45.5% | 43.2% | 14% |
| the least and the most are equal, and the size is not fixed | 7.4% | 5.4% | 1% |

**SSZ defaults are the reference's** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| has a default | 84.7% | 84.5% | 28% |
| has no default: a union inside | 15.3% | 15.5% | 4% |

**SSZ compatibility is the reference's** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| pair: the same type | 61.7% | 48.4% | 15% |
| pair: compatible, not the same | 9.7% | 34.8% | 12% |
| pair: not compatible | 28.6% | 16.8% | 5% |
| compatible, not the same, both: ProgressiveBitlist | **0.1%** | 6.9% | 2% |
| compatible, not the same, both: Vector | **0.6%** | 3.9% | 1% |
| compatible, not the same, both: List | **0.8%** | 3.9% | 1% |
| compatible, not the same, both: ProgressiveList | **2.5%** | 5.0% | 1% |
| compatible, not the same, both: Container | **0.4%** | 4.4% | 1% |
| compatible, not the same, both: ProgressiveContainer | **2.0%** | 3.9% | 1% |
| compatible, not the same, both: CompatibleUnion | **2.9%** | **2.7%** |  |
| compatible: a byte array and a sequence of bytes | - | 4.1% | 1% |

**SSZ paths have the index of the specification** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 63.0% | 50.9% | 16% |
| verdict: NO_PARTS | 10.9% | 16.7% | 5% |
| verdict: NO_PARTS_MIXIN | **1.6%** | 5.8% | 1% |
| verdict: NO_MIXIN | 9.9% | 10.6% | 3% |
| verdict: NO_SUCH_FIELD | **2.5%** | **2.8%** | 1% |
| verdict: NO_SUCH_OPTION | **1.6%** | **2.9%** |  |
| verdict: NO_SUCH_POSITION | 10.5% | 10.3% | 3% |
| steps: 0 | 22.8% | 11.7% | 4% |
| steps: 1 | 42.6% | 41.2% | 12% |
| steps: 2 | 22.5% | 33.8% | 10% |
| steps: 3 | 8.2% | 10.5% | 3% |
| steps: 4 or more | 3.9% | **2.8%** | 1% |
| step: an element of ByteVector | **2.3%** | 4.0% | 1% |
| step: an element of ByteList | **1.1%** | **2.4%** |  |
| step: an element of Bitvector | **2.5%** | 3.4% | 1% |
| step: an element of Bitlist | **1.4%** | **2.6%** |  |
| step: an element of ProgressiveBitlist | **2.5%** | **1.9%** |  |
| step: an element of Vector | 9.5% | 10.2% | 3% |
| step: an element of List | 4.5% | 7.1% | 1% |
| step: an element of ProgressiveList | 9.2% | 5.6% | 1% |
| step: an element of Container | 10.4% | 12.3% | 3% |
| step: an element of ProgressiveContainer | 9.0% | 7.0% | 2% |
| step: an element of CompatibleUnion | 3.8% | 3.8% | 1% |
| step: the word of List | 5.3% | 5.1% | 1% |
| step: the word of ByteList | **1.0%** | 4.2% | 1% |
| step: the word of Bitlist | **1.1%** | 4.2% | 1% |
| step: the word of ProgressiveList | 5.5% | **2.5%** |  |
| step: the word of ProgressiveBitlist | **0.8%** | **2.3%** |  |
| step: the word of ProgressiveContainer | 4.7% | 6.4% | 1% |
| step: the word of CompatibleUnion | **2.7%** | 3.2% |  |

**SSZ nodes are those of the reference tree** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 60.2% | 56.2% | 18% |
| verdict: NOT_A_GINDEX | 14.6% | 9.0% | 3% |
| verdict: PATH_INTO_MIXIN | 9.9% | 9.7% | 2% |
| verdict: PATH_INTO_PACKED | 7.5% | 16.5% | 4% |
| verdict: PATH_INTO_GAP | **2.8%** | 4.5% | 2% |
| verdict: PATH_PAST_SPINE | 5.0% | 4.1% | 1% |
| depth: no index | 14.6% | 9.0% | 3% |
| depth: the root | 31.8% | 25.5% | 7% |
| depth: 1 | 23.1% | 19.2% | 5% |
| depth: 2 to 4 | 13.5% | 12.5% | 3% |
| depth: 5 to 8 | 8.6% | 7.4% | 2% |
| depth: 9 to 16 | 6.2% | 5.0% | 1% |
| depth: 17 to 63 | **2.2%** | 8.3% | 3% |
| depth: 64 or more | **0.0%** | 13.1% | 3% |
| walk: the root | 46.4% | 34.5% | 11% |
| walk: the mixed-in word | 9.2% | 8.0% | 2% |
| walk: under the mixed-in word | 6.1% | 6.7% | 1% |
| walk: on or under a spine | 11.4% | 16.4% | 5% |
| walk: inside the tree of the root | 7.6% | 8.3% | 2% |
| walk: under a leaf of the tree of the root | 19.3% | 26.1% | 8% |
| the node is the root of a zero subtree | 10.1% | 12.9% | 3% |

**SSZ proofs verify, and only for their leaf** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| a proof was built and checked | 32.3% | 75.6% | 25% |
| nodes of the proof: 1 | 21.9% | 48.6% | 15% |
| nodes of the proof: 2 to 4 | 7.4% | 14.9% | 4% |
| nodes of the proof: 5 to 8 | **2.4%** | 3.9% | 2% |
| nodes of the proof: 9 or more | **0.6%** | 8.2% | 2% |
| walk: the mixed-in word | 10.1% | 21.1% | 6% |
| walk: on or under a spine | 6.1% | 16.4% | 5% |
| walk: inside the tree of the root | 9.7% | 23.0% | 7% |
| walk: under a leaf of the tree of the root | 6.4% | 15.1% | 5% |
| no node at the index: nothing checked | 35.4% | 16.0% |  |
| the root, which has no proof: nothing checked | 32.3% | 8.4% |  |

**SSZ helper indices are the specification's** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 51.4% | 38.4% | 11% |
| verdict: EMPTY_REQUEST | 39.3% | 5.7% | 2% |
| verdict: REPEATED_INDEX | **0.6%** | 15.5% | 4% |
| verdict: NESTED_INDEX | 7.0% | 27.6% | 9% |
| verdict: ROOT_HAS_NO_BRANCH | **1.7%** | 5.5% | 1% |
| verdict: NOT_A_GINDEX | **0.0%** | 7.3% | 1% |
| indices: 0 | 39.3% | 5.7% | 2% |
| indices: 1 | 25.0% | 8.0% | 2% |
| indices: 2 | 16.9% | 14.8% | 4% |
| indices: 3 | 9.4% | 13.1% | 4% |
| indices: 4 or more | 9.4% | 58.4% | 18% |

**SSZ multiproofs rebuild the specification's root** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| indices: 1 | 55.1% | 22.5% | 6% |
| indices: 2 | 23.9% | 23.6% | 7% |
| indices: 3 | 12.1% | 17.9% | 5% |
| indices: 4 or more | 8.9% | 36.0% | 12% |
| helpers: 0 | **0.0%** | **1.9%** |  |
| helpers: 1 to 4 | 34.4% | 34.8% | 11% |
| helpers: 5 to 12 | 57.9% | 54.6% | 17% |
| helpers: 13 or more | 7.7% | 8.7% | 2% |
| two indices are siblings | **1.4%** | 33.5% | 10% |

**SSZ branches by depth and index** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| depth: 0 | 27.5% | 27.6% | 8% |
| depth: 1 | 18.5% | 18.1% | 5% |
| depth: 2 to 8 | 50.0% | 50.3% | 16% |
| depth: 9 or more | 4.0% | 4.0% | 1% |
| index: below 2 ^ depth | 75.8% | 75.6% | 25% |
| index: 2 ^ depth or more | 24.2% | 24.4% | 7% |
| verdict: valid | 50.7% | 49.4% | 16% |
| verdict: not valid | 49.3% | 50.6% | 16% |

**SSZ documents read back under every spelling** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| spelling: byte | 18.8% | 19.8% | 5% |
| spelling: digits | 17.8% | 19.9% | 6% |
| spelling: text | 18.1% | 17.2% | 5% |
| a mark that changes the document: byte | 4.9% | 4.6% | 1% |
| a mark that changes the document: digits | 5.2% | 6.7% | 2% |
| a mark that changes the document: text | 4.9% | 6.9% | 1% |

**SSZ documents are those of the mapping** (1,000 cases, passed).

It names no class.

**SSZ documents hold integers as digits** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| width: 1 | 17.2% | 15.1% | 5% |
| width: 2 | 16.5% | 16.3% | 5% |
| width: 4 | 16.5% | 18.8% | 5% |
| width: 8 | 16.6% | 17.0% | 5% |
| width: 16 | 15.1% | 15.9% | 5% |
| width: 32 | 18.1% | 16.9% | 5% |
| digits: read | 4.9% | 27.5% | 8% |
| digits: out of the width | **2.8%** | 11.4% | 3% |
| digits: another text | 92.3% | 61.1% | 20% |
| a number: out of the width | 32.8% | 30.1% | 10% |

**typed SSZ: a container of every kind of field** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 55.2% | 18.1% | 5% |
| verdict: SCOPE_TOO_SMALL | 10.8% | 7.1% | 2% |
| verdict: SCOPE_UNDIVIDED | **0.7%** | 6.6% | 1% |
| verdict: FIRST_OFFSET | 7.7% | 13.0% | 4% |
| verdict: OFFSET_UNORDERED | 5.1% | 5.5% | 1% |
| verdict: OFFSET_PAST_SCOPE | 8.6% | 4.1% |  |
| verdict: NOT_A_BIT | **0.5%** | 12.7% | 4% |
| verdict: PADDING_BITS | 3.1% | 14.6% | 5% |
| verdict: EMPTY_ENCODING | **0.1%** | **2.3%** |  |
| verdict: NO_DELIMITER | **0.4%** | 4.7% |  |
| verdict: TRAILING_ZEROS | **0.0%** | 4.1% |  |
| verdict: LIMIT | 7.8% | 7.2% | 2% |
| the encoding of a value, unchanged | 16.3% | 5.9% | 1% |

**typed SSZ: a progressive container with fork lists** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 59.0% | 18.3% | 6% |
| verdict: SCOPE_TOO_SMALL | 11.1% | 5.3% | 1% |
| verdict: SCOPE_UNDIVIDED | **0.2%** | 4.7% | 1% |
| verdict: FIRST_OFFSET | 5.9% | 20.0% | 6% |
| verdict: OFFSET_UNORDERED | 8.8% | 5.5% | 1% |
| verdict: OFFSET_PAST_SCOPE | 10.0% | 3.2% | 1% |
| verdict: EMPTY_ENCODING | 4.2% | 12.3% | 3% |
| verdict: NO_DELIMITER | **0.7%** | 10.3% | 3% |
| verdict: TRAILING_ZEROS | **0.1%** | 14.7% | 5% |
| verdict: LIMIT | **0.0%** | 5.7% | 1% |
| the encoding of a value, unchanged | 15.5% | 3.9% | 1% |

**typed SSZ: a container of fixed size** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 56.8% | 17.0% | 5% |
| verdict: SCOPE | 42.3% | 57.3% | 18% |
| verdict: PADDING_BITS | **0.9%** | 25.7% | 9% |
| the encoding of a value, unchanged | 14.0% | 4.8% | 1% |

**typed RLP reads back within its range** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| scalar: below 2 | **1.4%** | 15.0% | 4% |
| scalar: 2 to 2^8 - 1 | 3.9% | 14.9% | 4% |
| scalar: 2^8 to 2^16 - 1 | 3.6% | 11.9% | 4% |
| scalar: 2^16 to 2^32 - 1 | 6.8% | 11.8% | 4% |
| scalar: 2^32 to 2^64 - 1 | 14.4% | 16.2% | 3% |
| scalar: 2^64 to 2^256 - 1 | 69.9% | 22.9% | 7% |
| scalar: 2^256 or more | **0.0%** | 7.3% | 2% |
| bytes: none | 11.1% | 6.9% | 2% |
| bytes: 20 | **2.2%** | 35.9% | 11% |
| bytes: another count | 86.7% | 57.2% | 18% |

**DER reads one tag, length and value** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 41.6% | 40.5% | 13% |
| verdict: truncated | 17.6% | 18.4% | 5% |
| verdict: tag | 17.8% | 16.5% | 5% |
| verdict: length | 23.0% | 24.6% | 8% |
| length: none | 3.2% | 5.0% | 1% |
| length: short | 35.2% | 31.2% | 9% |
| length: indefinite, 0x80 | 6.2% | 5.9% | 2% |
| length: reserved, 0xff | 8.4% | 7.9% | 2% |
| length: long on 1 octet | 30.5% | 25.9% | 8% |
| length: long on 2 octets | 14.5% | 16.6% | 5% |
| length: long on 3 octets or more | **2.0%** | 7.5% | 2% |
| tag: none | **1.4%** | **1.3%** |  |
| tag: 0 | 3.1% | 3.5% |  |
| tag: a high tag number | 15.3% | 14.3% | 4% |
| tag: of another class than universal | 11.4% | 9.5% | 3% |
| tag: universal, constructed | 11.9% | 11.7% | 3% |
| tag: universal, primitive | 56.9% | 59.7% | 19% |
| bytes follow the value | 12.4% | 11.3% | 3% |

**DER integers are minimal** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 29.7% | 26.6% | 8% |
| verdict: truncated | **0.0%** | 6.9% | 2% |
| verdict: tag | 5.5% | 4.9% | 2% |
| verdict: length | 37.4% | 37.8% | 12% |
| verdict: value | 27.4% | 17.8% | 5% |
| verdict: trailing | **0.0%** | 6.0% | 1% |
| integer: none | 70.3% | 73.4% | 24% |
| integer: negative | 15.2% | 10.9% | 3% |
| integer: 0 | **0.1%** | **2.9%** |  |
| integer: positive | 14.4% | 12.8% | 3% |
| content: no octet | 10.4% | 11.8% | 3% |
| content: 1 octet | **1.6%** | 15.0% | 4% |
| content: 2 to 8 octets | 56.1% | 54.1% | 18% |
| content: 9 octets or more | 31.9% | 19.1% | 6% |

**DER signatures read as the reference reads them** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | **1.3%** | 32.0% | 10% |
| verdict: truncated | **2.9%** | 5.4% | 1% |
| verdict: tag | **0.7%** | 9.6% | 3% |
| verdict: length | 72.5% | 16.7% | 6% |
| verdict: value | 19.4% | 32.1% | 10% |
| verdict: trailing | 3.2% | 4.2% | 1% |

**DER values are valid as X.690 says** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: valid | 58.7% | 27.5% | 7% |
| verdict: not valid | 41.3% | 72.5% | 25% |
| the generated value, unchanged | 79.8% | 37.1% | 11% |
| holds the tag: 1 | 7.1% | 9.8% | 3% |
| holds the tag: 2 | 6.8% | 11.5% | 3% |
| holds the tag: 3 | 6.3% | 9.6% | 2% |
| holds the tag: 4 | 7.7% | 4.4% | 1% |
| holds the tag: 5 | 7.5% | 8.3% | 2% |
| holds the tag: 6 | 7.1% | 8.6% | 2% |
| holds the tag: 12 | 5.6% | 8.6% | 2% |
| holds the tag: 19 | 7.6% | 10.8% | 2% |
| holds the tag: 22 | 7.2% | 8.5% | 2% |
| holds the tag: 28 | 7.6% | 7.2% | 3% |
| holds the tag: 30 | 7.9% | 8.4% | 2% |
| holds the tag: 48 | 35.3% | 26.2% | 9% |
| holds the tag: 49 | 35.5% | 29.5% | 9% |
| not valid, at the root the tag: 1 | **2.2%** | 4.8% | 1% |
| not valid, at the root the tag: 2 | **1.5%** | 4.3% | 1% |
| not valid, at the root the tag: 3 | **2.1%** | 3.9% | 1% |
| not valid, at the root the tag: 5 | **1.3%** | 3.0% | 1% |
| not valid, at the root the tag: 6 | **1.7%** | 3.2% | 1% |
| not valid, at the root the tag: 12 | **0.8%** | 3.0% |  |
| not valid, at the root the tag: 19 | **1.0%** | 3.6% |  |
| not valid, at the root the tag: 22 | **0.5%** | 3.0% | 1% |
| not valid, at the root the tag: 28 | **1.2%** | 3.4% |  |
| not valid, at the root the tag: 30 | **0.5%** | 3.6% | 1% |
| not valid, at the root the tag: 48 | 8.9% | 13.8% | 5% |
| not valid, at the root the tag: 49 | 8.5% | 17.1% | 5% |

**JSON-RPC readers accept the patterns of the schema** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| bytes: accepted | 26.3% | 33.9% | 10% |
| hash32: accepted | **0.2%** | 4.7% | 1% |
| bytes8: accepted | **1.8%** | 6.3% | 1% |
| address: accepted | **1.3%** | 8.2% | 2% |
| address: accepted with an upper-case digit | **0.8%** | 3.2% | 1% |
| uint: accepted | 25.5% | 38.9% | 12% |
| uint64: accepted | 23.6% | 21.3% | 6% |
| uint64: refused, uint accepted | **1.9%** | 17.6% | 5% |
| uint256: accepted | 25.4% | 35.4% | 11% |
| uint256: refused, uint accepted | **0.1%** | 3.5% |  |
| no reader accepts | 56.7% | 44.5% | 14% |

**JSON-RPC writers write the patterns** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| quantity: 0 | **2.2%** | 4.5% | 1% |
| quantity: 1 to 15 | 6.7% | 10.0% | 3% |
| quantity: 16 to 2^64 - 1 | 60.4% | 56.7% | 18% |
| quantity: 2^64 or more | 30.7% | 28.8% | 9% |
| data: no byte | 10.1% | 10.1% | 4% |

**JSON-RPC integers are the integral numbers** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: an integer | 64.4% | 62.2% | 20% |
| verdict: not an integer | 35.6% | 37.8% | 12% |
| an integer written with a fraction or an exponent | 29.2% | 28.9% | 9% |
| an integer below zero | 15.1% | 15.9% | 5% |

**JSON-RPC error objects read back** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: read | 49.8% | 50.8% | 16% |
| verdict: refused | 50.2% | 49.2% | 16% |
| with data | 80.8% | 81.4% | 27% |
| with the data null | 20.8% | 19.6% | 6% |

**RLP decodes inputs at the edge of each form** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| input: no byte | **0.0%** | **1.7%** |  |
| input: a byte below 0x80 | 5.5% | 3.3% | 1% |
| input: short string | 26.1% | 6.7% | 2% |
| input: short list | 22.4% | 14.5% | 4% |
| input: long string, length on 1 | 6.0% | 6.7% | 2% |
| input: long string, length on 2 | 6.8% | 7.5% | 2% |
| input: long string, length on 3 | 6.2% | 4.8% | 1% |
| input: long string, length on 4 | **0.0%** | **2.6%** | 1% |
| input: long string, length on 5 | **0.0%** | **2.1%** |  |
| input: long string, length on 6 | **0.0%** | 4.4% |  |
| input: long string, length on 7 | **0.0%** | 3.4% |  |
| input: long string, length on 8 | 7.0% | 4.5% | 1% |
| input: long list, length on 1 | 7.0% | 8.4% | 2% |
| input: long list, length on 2 | 6.2% | 7.9% | 2% |
| input: long list, length on 3 | **0.0%** | 3.9% | 1% |
| input: long list, length on 4 | **0.0%** | 3.4% |  |
| input: long list, length on 5 | **0.0%** | 3.8% |  |
| input: long list, length on 6 | **0.0%** | 3.0% |  |
| input: long list, length on 7 | **0.0%** | 3.7% |  |
| input: long list, length on 8 | 6.8% | 3.7% | 1% |
| verdict: accepted | 3.3% | 9.3% | 2% |
| verdict: input too short | 59.0% | 60.4% | 19% |
| verdict: a byte below 0x80 with a prefix | 3.3% | 4.0% | 1% |
| verdict: long form for a short length | **2.2%** | 7.4% | 2% |
| verdict: leading zero in a length | 3.1% | 13.4% | 4% |
| verdict: trailing bytes | 29.1% | 5.5% | 2% |

**SSZ refuses a declaration that breaks a rule** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| refused as: UINT_WIDTH | - | 11.3% | 3% |
| refused as: VECTOR_EMPTY | - | 13.1% | 3% |
| refused as: CONTAINER_EMPTY | - | 4.6% | 1% |
| refused as: LAYOUT_WIDTH | - | 7.3% | 2% |
| refused as: LAYOUT_TRAILING_GAP | - | 8.7% | 2% |
| refused as: LAYOUT_TOO_WIDE | - | 3.5% | 1% |
| refused as: LAYOUT_FIELD_COUNT | - | 11.0% | 3% |
| refused as: BAD_DECLARATION | - | 15.4% | 5% |
| refused as: UNION_EMPTY | - | 3.2% | 1% |
| refused as: UNION_SELECTOR_RANGE | - | 11.2% | 3% |
| refused as: UNION_SELECTOR_REPEATED | - | 3.9% | 1% |
| refused as: UNION_INCOMPATIBLE | - | 6.8% | 2% |
| around it: nothing: it is the root | - | 12.3% | 4% |
| around it: Vector | 15.6% | 12.1% | 4% |
| around it: List | 25.0% | 24.8% | 7% |
| around it: ProgressiveList | 10.3% | 12.1% | 4% |
| around it: Container | 13.9% | 12.3% | 4% |
| around it: ProgressiveContainer | 15.5% | 13.1% | 3% |
| around it: CompatibleUnion | 16.8% | 13.3% | 3% |

**SSZ layouts are at most 256 positions wide** (255 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| fields: 1 | **0.0%** | 5.5% | 1% |
| fields: 2 to 128 | 52.9% | 53.3% | 8% |
| fields: 129 to 255 | 47.1% | 41.2% | 8% |

**SSZ limits of progressive shapes bound the count only** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| shape: ProgressiveBitlist | 45.6% | 51.6% | 16% |
| shape: ProgressiveList of basic | 4.2% | 3.2% |  |
| shape: ProgressiveList of composite | 50.2% | 45.2% | 15% |
| count: below the limit | 37.3% | 43.4% | 13% |
| count: at the limit | 25.6% | 23.5% | 7% |
| count: over the limit | 37.1% | 33.1% | 11% |
| count: 0 | 9.2% | 9.0% | 2% |
| root: leaves: none | 9.2% | 9.0% | 2% |
| root: leaves: one | 13.7% | 23.6% | 8% |
| root: leaves: a power of two | 15.1% | 14.0% | 4% |
| root: leaves: one over a power of two | 14.7% | 7.8% | 2% |
| root: leaves: another count | 47.3% | 45.6% | 15% |
| root: spine: no run | 9.2% | 9.0% | 2% |
| root: spine: one run | 13.7% | 23.6% | 8% |
| root: spine: two runs | 27.4% | 19.8% | 6% |
| root: spine: three runs | 33.8% | 18.0% | 6% |
| root: spine: four runs | - | 13.2% | 4% |
| root: spine: five runs | - | 14.0% | 4% |
| root: spine: six runs or more | - | **2.4%** | 1% |
| root: spine: its last run is full | 30.3% | 38.2% | 12% |
| root: mixes a word in | 100.0% | 100.0% | 33% |

**SSZ lists far below their limit** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| root: List of basic | 22.8% | 19.4% | 6% |
| root: List of fixed composite | 4.0% | **2.6%** |  |
| root: List of variable | 7.7% | 13.3% | 3% |
| root: ByteList | 32.4% | 36.1% | 10% |
| root: Bitlist | 33.1% | 28.6% | 10% |
| root: leaves: none | 20.9% | 19.2% | 6% |
| root: leaves: one | 25.1% | 33.3% | 10% |
| root: leaves: a power of two | 10.4% | 10.4% | 3% |
| root: leaves: one over a power of two | 31.6% | 23.3% | 6% |
| root: leaves: another count | 12.0% | 13.8% | 4% |
| root: capacity: a power of two, not full | 50.8% | 49.2% | 17% |
| root: capacity: not a power of two, not full | 49.2% | 50.8% | 15% |
| root: zero subtree: none | **1.4%** | **0.1%** |  |
| root: zero subtree: 1 to 7 | 18.1% | 7.8% | 2% |
| root: zero subtree: 8 to 31 | 41.8% | 14.0% | 5% |
| root: zero subtree: 32 to 63 | 38.7% | 39.7% | 12% |
| root: zero subtree: 64 | **0.0%** | **2.8%** |  |
| root: zero subtree: 65 or more | **0.0%** | 35.6% | 11% |
| root: asks the zero root of depth 64, the last of the table | - | 5.3% | 1% |
| root: asks a zero root of depth 65 or more, which is folded | - | 35.3% | 11% |
| root: mixes a word in | 100.0% | 100.0% | 33% |
| verdict: accepted | 73.0% | 65.0% | 22% |
| verdict: NOT_A_GINDEX | 10.5% | 7.8% | 3% |
| verdict: PATH_INTO_MIXIN | 10.2% | 10.4% | 2% |
| verdict: PATH_INTO_PACKED | 5.1% | 10.8% | 2% |
| verdict: PATH_INTO_GAP | **1.2%** | 5.9% | 1% |
| depth: no index | 10.5% | 7.8% | 3% |
| depth: the root | 27.9% | 19.3% | 7% |
| depth: 1 | 22.1% | 24.1% | 7% |
| depth: 2 to 4 | 11.4% | 10.6% | 2% |
| depth: 5 to 8 | 8.4% | 5.4% | 1% |
| depth: 9 to 16 | 4.8% | 3.5% |  |
| depth: 17 to 63 | 14.5% | 13.2% | 3% |
| depth: 64 or more | **0.4%** | 16.1% | 4% |
| walk: the root | 38.4% | 27.1% | 10% |
| walk: the mixed-in word | 14.2% | 14.4% | 4% |
| walk: under the mixed-in word | 10.2% | 10.4% | 2% |
| walk: inside the tree of the root | 30.8% | 31.1% | 8% |
| walk: under a leaf of the tree of the root | 6.4% | 17.0% | 3% |
| the node is the root of a zero subtree | 23.5% | 18.0% | 6% |
| verdict: PATH_PAST_SPINE | **0.0%** | **0.1%** |  |

**SSZ multiproofs of a value rebuild its root** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| a multiproof was built and checked | 21.4% | 78.1% | 25% |
| indices: 1 | 20.1% | 10.2% | 3% |
| indices: 2 | **1.3%** | 51.2% | 15% |
| indices: 3 | **0.0%** | 10.1% | 4% |
| indices: 4 or more | **0.0%** | 6.6% | 1% |
| nodes of the proof: 0 | **0.4%** | 28.8% | 8% |
| nodes of the proof: 1 to 4 | 18.9% | 27.6% | 9% |
| nodes of the proof: 5 to 12 | **2.1%** | 7.8% | 2% |
| nodes of the proof: 13 or more | **0.0%** | 13.9% | 4% |
| refused: REPEATED_INDEX | 4.1% | **0.8%** |  |
| refused: NESTED_INDEX | **1.1%** | **0.3%** |  |
| refused: ROOT_HAS_NO_BRANCH | 24.4% | 4.7% | 1% |
| no node at an index: nothing checked | 49.0% | 16.1% |  |

**SSZ documents near a valid one read as the specification reads them** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 21.3% | 10.7% | 3% |
| verdict: WRONG_TYPE | 25.0% | 26.7% | 8% |
| verdict: HEX_PREFIX | 14.4% | 3.6% |  |
| verdict: HEX_DIGITS | 12.0% | 4.7% | 1% |
| verdict: HEX_LENGTH | **0.3%** | **1.3%** |  |
| verdict: BITFIELD_PADDING | **0.0%** | **2.7%** |  |
| verdict: BITFIELD_DELIMITER | **0.0%** | **2.5%** | 1% |
| verdict: BITFIELD_TRAILING_ZEROS | **1.0%** | 4.2% | 1% |
| verdict: UINT_RANGE | **2.5%** | 4.5% | 1% |
| verdict: OVER_LIMIT | **0.3%** | **2.7%** |  |
| verdict: ELEMENT_KIND | **0.0%** | 5.6% | 2% |
| verdict: NO_DEFAULT | **0.5%** | **1.1%** |  |
| verdict: UNDECLARED_FIELD | 9.8% | 4.2% | 1% |
| verdict: MISSING_FIELD | **2.3%** | 9.7% | 3% |
| verdict: STRUCT_NOT_AN_OBJECT | 4.5% | 3.5% |  |
| verdict: UNDECLARED_SELECTOR | **2.3%** | **2.2%** |  |
| verdict: COUNT | 3.5% | 6.2% | 1% |
| verdict: SCOPE | **0.3%** | **1.8%** |  |
| verdict: EMPTY_ENCODING | **0.0%** | **2.1%** |  |
| the document of the value, unchanged | 9.8% | **2.4%** |  |
| against the specification: both read | 21.3% | 10.7% | 3% |
| against the specification: both refuse | 77.3% | 79.7% | 25% |
| against the specification: EthLib refuses what the specification reads | **1.4%** | 9.6% |  |

**SSZ documents are those the specification writes** (1,000 cases, passed).

It names no class.

**SSZ documents under the byte alias** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| root: uint | - | 13.1% | 4% |
| root: Vector | - | 22.3% | 8% |
| root: List | - | 25.5% | 8% |
| root: ProgressiveList | - | 11.2% | 4% |
| root: Container | - | 14.2% | 3% |
| root: CompatibleUnion | 13.8% | 13.7% | 3% |

**SSZ declarations are legal as the specification says** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 67.8% | 32.4% | 10% |
| verdict: UINT_WIDTH | 3.2% | 8.6% | 2% |
| verdict: VECTOR_EMPTY | 4.0% | 8.1% | 2% |
| verdict: CONTAINER_EMPTY | **0.9%** | **2.9%** |  |
| verdict: LAYOUT_WIDTH | **2.7%** | 6.5% | 1% |
| verdict: LAYOUT_TRAILING_GAP | **2.5%** | 5.3% | 1% |
| verdict: LAYOUT_TOO_WIDE | **0.8%** | **2.3%** |  |
| verdict: LAYOUT_FIELD_COUNT | 4.5% | 7.3% | 2% |
| verdict: BAD_DECLARATION | 6.0% | 8.9% | 3% |
| verdict: UNION_EMPTY | **0.5%** | **2.4%** |  |
| verdict: UNION_SELECTOR_RANGE | 3.8% | 7.5% | 2% |
| verdict: UNION_SELECTOR_REPEATED | **1.3%** | **2.4%** |  |
| verdict: UNION_INCOMPATIBLE | **2.0%** | 5.4% | 1% |
| refused, and the oracle answers with a name of its own | 9.0% | 12.9% |  |

**SSZ proof requests are answered as the specification does** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| one index: accepted | 8.6% | 43.8% | 14% |
| one index: NOT_A_GINDEX | 9.7% | 9.8% | 3% |
| one index: ROOT_HAS_NO_BRANCH | 22.7% | 21.4% | 7% |
| one index: BRANCH_LENGTH | 59.0% | 25.0% | 7% |
| several indices: accepted | 7.1% | 21.1% | 7% |
| several indices: EMPTY_REQUEST | 41.0% | 4.7% | 1% |
| several indices: REPEATED_INDEX | **0.9%** | 14.8% | 3% |
| several indices: NESTED_INDEX | 6.5% | 24.4% | 8% |
| several indices: ROOT_HAS_NO_BRANCH | **2.6%** | 5.8% | 1% |
| several indices: NOT_A_GINDEX | **0.0%** | 5.6% | 1% |
| several indices: LEAF_COUNT | **0.0%** | 12.0% | 4% |
| several indices: PROOF_LENGTH | 41.9% | 11.6% | 3% |

**typed SSZ: a field before its fork** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 46.3% | 17.9% | 5% |
| verdict: SCOPE_TOO_SMALL | 15.9% | 17.0% | 4% |
| verdict: SCOPE_UNDIVIDED | 13.3% | 12.9% | 4% |
| verdict: FIRST_OFFSET | 22.9% | 45.0% | 15% |
| verdict: LIMIT | **1.6%** | 7.2% | 1% |
| the encoding of a value, unchanged | 15.3% | 7.7% | 2% |

**typed SSZ: a field from its fork on** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | 38.6% | 13.8% | 4% |
| verdict: SCOPE_TOO_SMALL | 12.2% | 9.3% | 3% |
| verdict: SCOPE_UNDIVIDED | 13.2% | 12.9% | 4% |
| verdict: FIRST_OFFSET | 17.5% | 31.8% | 10% |
| verdict: OFFSET_UNORDERED | **0.8%** | **1.9%** |  |
| verdict: OFFSET_PAST_SCOPE | 17.0% | 6.4% | 1% |
| verdict: LIMIT | **0.7%** | 23.9% | 7% |
| the encoding of a value, unchanged | 16.9% | 7.9% | 2% |

#### Group `serialization: state machines`

**StateMachine: List[uint64, 40] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 59.5% | 51.5% | 9% |
| reached, in nodes: 1 | 94.5% | 71.5% | 15% |
| reached, in nodes: 2 to 5 | 60.0% | 49.5% | 9% |
| reached, in nodes: 6 to 21 | 43.5% | 55.0% | 10% |
| reached: a last node that is full | 68.0% | 74.5% | 15% |
| reached: the limit | 16.0% | 34.0% | 5% |
| step: push | 99.5% | 87.0% | 17% |
| step: push many | 61.5% | 54.0% | 9% |
| step: set | 82.0% | 82.5% | 16% |
| step: set the last element | 71.5% | 75.0% | 14% |
| step: set the first element | 51.0% | 42.5% | 8% |

**StateMachine: ProgressiveList[uint64] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 58.0% | 42.5% | 10% |
| reached, in nodes: 1 | 94.5% | 69.5% | 14% |
| reached, in nodes: 2 to 5 | 62.0% | 44.5% | 8% |
| reached, in nodes: 6 to 21 | 41.0% | 32.0% | 6% |
| reached, in nodes: 22 to 85 | - | 47.5% | 9% |
| reached, in nodes: 86 to 341 | - | 28.0% | 5% |
| reached, in nodes: 342 or more | - | 3.5% |  |
| reached: a last node that is full | 71.5% | 75.0% | 14% |
| step: push | 97.0% | 95.5% | 18% |
| step: push many | 68.0% | 75.5% | 14% |
| step: set | 83.0% | 81.5% | 16% |
| step: set the last element | 72.5% | 67.5% | 13% |
| step: set the first element | 46.5% | 31.5% | 5% |

**StateMachine: List[uint16, 100] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 61.5% | 51.5% | 10% |
| reached, in nodes: 1 | 98.0% | 81.0% | 16% |
| reached, in nodes: 2 to 5 | 46.0% | 39.0% | 8% |
| reached, in nodes: 6 to 21 | 8.0% | 34.0% | 5% |
| reached: a last node that is full | 29.0% | 25.5% | 4% |
| reached: the limit | 3.0% | 21.5% | 3% |
| step: push | 94.5% | 91.5% | 17% |
| step: set | 80.5% | 84.5% | 17% |
| step: set the last element | 72.0% | 72.5% | 15% |
| step: set the first element | 42.0% | 38.5% | 7% |
| step: push many | 69.5% | 62.0% | 11% |

**StateMachine: ProgressiveList[boolean] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 58.0% | 51.0% | 10% |
| reached, in nodes: 1 | 100.0% | 80.0% | 15% |
| reached, in nodes: 2 to 5 | 34.0% | 25.0% | 5% |
| reached, in nodes: 6 to 21 | **1.0%** | 46.5% | 8% |
| reached, in nodes: 22 to 85 | - | 13.5% | 2% |
| reached, in nodes: 86 to 341 | - | 4.5% |  |
| reached, in nodes: 342 or more | - | **0.0%** |  |
| reached: a last node that is full | 12.0% | 24.0% | 4% |
| step: push | 96.0% | 94.0% | 18% |
| step: push many | 67.0% | 77.0% | 15% |
| step: set | 79.5% | 81.0% | 16% |
| step: set the last element | 68.0% | 69.5% | 13% |
| step: set the first element | 43.0% | 34.5% | 6% |

**StateMachine: List[uint256, 20] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 60.0% | 48.0% | 9% |
| reached, in nodes: 1 | 77.5% | 63.0% | 11% |
| reached, in nodes: 2 to 5 | 75.5% | 57.0% | 12% |
| reached, in nodes: 6 to 21 | 67.5% | 72.5% | 13% |
| reached: a last node that is full | 100.0% | 100.0% | 20% |
| reached: the limit | 18.5% | 38.0% | 6% |
| step: push | 95.5% | 83.5% | 17% |
| step: set | 76.5% | 83.5% | 15% |
| step: set the last element | 66.0% | 78.0% | 14% |
| step: set the first element | 47.5% | 41.5% | 9% |
| step: push many | 56.5% | 50.0% | 8% |

**StateMachine: ProgressiveList[uint256] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 65.5% | 52.5% | 9% |
| reached, in nodes: 1 | 80.5% | 65.5% | 11% |
| reached, in nodes: 2 to 5 | 65.5% | 63.0% | 10% |
| reached, in nodes: 6 to 21 | 50.5% | 43.0% | 8% |
| reached, in nodes: 22 to 85 | - | 29.0% | 5% |
| reached, in nodes: 86 to 341 | - | 43.5% | 8% |
| reached, in nodes: 342 or more | - | 14.0% | 3% |
| reached: a last node that is full | 100.0% | 100.0% | 20% |
| step: push many | 64.0% | 70.0% | 14% |
| step: push | 96.0% | 93.5% | 18% |
| step: set | 76.5% | 80.5% | 16% |
| step: set the last element | 68.5% | 64.0% | 13% |
| step: set the first element | 42.5% | 39.0% | 5% |

**StateMachine: List[Bytes32, 9] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 56.5% | 58.5% | 9% |
| reached, in nodes: 1 | 83.5% | 74.0% | 13% |
| reached, in nodes: 2 to 5 | 83.0% | 66.0% | 12% |
| reached, in nodes: 6 to 21 | 55.5% | 59.5% | 11% |
| reached: a last node that is full | 100.0% | 100.0% | 20% |
| reached: the limit | 40.5% | 46.5% | 9% |
| step: push many | 28.5% | 23.5% | 4% |
| step: set | 77.5% | 83.0% | 15% |
| step: set the last element | 73.5% | 76.5% | 14% |
| step: set the first element | 58.5% | 62.5% | 10% |
| step: push | 96.5% | 85.5% | 16% |

**StateMachine: ProgressiveList[Bytes32] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 60.0% | 51.0% | 9% |
| reached, in nodes: 1 | 74.0% | 63.5% | 12% |
| reached, in nodes: 2 to 5 | 77.0% | 66.0% | 10% |
| reached, in nodes: 6 to 21 | 55.5% | 37.5% | 7% |
| reached, in nodes: 22 to 85 | - | 27.5% | 5% |
| reached, in nodes: 86 to 341 | - | 46.0% | 8% |
| reached, in nodes: 342 or more | - | 15.0% | 2% |
| reached: a last node that is full | 100.0% | 100.0% | 20% |
| step: push | 94.5% | 95.5% | 18% |
| step: push many | 68.5% | 74.0% | 13% |
| step: set | 82.5% | 82.0% | 16% |
| step: set the last element | 74.5% | 68.5% | 13% |
| step: set the first element | 47.5% | 33.5% | 5% |

**StateMachine: List[Pair, 6] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 66.0% | 48.5% | 9% |
| reached, in nodes: 1 | 79.0% | 73.5% | 12% |
| reached, in nodes: 2 to 5 | 87.0% | 81.0% | 15% |
| reached, in nodes: 6 to 21 | 56.5% | 53.5% | 12% |
| reached: a last node that is full | 100.0% | 100.0% | 20% |
| reached: the limit | 56.5% | 53.5% | 12% |
| step: push | 95.5% | 86.5% | 16% |
| step: set | 79.0% | 83.5% | 16% |
| step: set the last element | 75.0% | 76.0% | 15% |
| step: set the first element | 59.5% | 60.0% | 12% |
| step: push many | 20.0% | 15.0% | 3% |

**StateMachine: ProgressiveList[Pair] keeps its tree** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| reached, in nodes: 0 | 58.5% | 51.0% | 10% |
| reached, in nodes: 1 | 77.5% | 57.0% | 12% |
| reached, in nodes: 2 to 5 | 76.5% | 51.5% | 11% |
| reached, in nodes: 6 to 21 | 55.0% | 45.0% | 6% |
| reached, in nodes: 22 to 85 | - | 31.0% | 5% |
| reached, in nodes: 86 to 341 | - | 49.5% | 8% |
| reached, in nodes: 342 or more | - | 18.5% | 3% |
| reached: a last node that is full | 100.0% | 100.0% | 20% |
| step: push | 97.5% | 89.0% | 18% |
| step: push many | 67.0% | 72.5% | 14% |
| step: set | 79.0% | 79.5% | 15% |
| step: set the last element | 70.5% | 64.5% | 12% |
| step: set the first element | 40.0% | 30.0% | 5% |

**StateMachine: an RLP stream is read in the order written** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| step: write | 97.4% | 97.6% | 32% |
| wrote: a byte below 0x80 | 41.4% | 22.8% | 7% |
| wrote: string of 0 | 16.8% | 12.0% | 4% |
| wrote: string of 1, 0x80 or more | 41.7% | 23.2% | 7% |
| wrote: string of 2 to 55 | 44.6% | 28.9% | 9% |
| wrote: string of 56 to 255 | 30.6% | 19.1% | 5% |
| wrote: string of 256 to 65535 | 16.0% | 21.1% | 6% |
| wrote: string of 65536 or more | **0.0%** | 19.1% | 5% |
| wrote: list payload of 0 | 42.2% | 52.9% | 15% |
| wrote: list payload of 1 to 55 | 56.0% | 54.2% | 18% |
| wrote: list payload of 56 to 255 | 42.2% | 50.1% | 16% |
| wrote: list payload of 256 to 65535 | 18.3% | 48.6% | 15% |
| wrote: list payload of 65536 or more | **0.0%** | 19.6% | 7% |
| step: read as a list | 60.7% | 63.9% | 20% |
| read as a list, a payload of: 0 | 18.5% | 20.2% | 6% |
| read as a list, a payload of: 1 to 55 | 16.0% | 11.8% | 3% |
| read as a list, a payload of: 56 to 255 | 23.2% | 11.0% | 3% |
| read as a list, a payload of: 256 to 65535 | 21.7% | 24.8% | 7% |
| read as a list, a payload of: 65536 or more | **0.0%** | 20.8% | 6% |
| step: read | 77.2% | 78.0% | 25% |
| read: not at the start of the buffer | 58.4% | 60.8% | 19% |
| read: the last item written | 58.6% | 60.6% | 19% |
| step: read short | 41.3% | 43.6% | 14% |
| read short: of the last item, refused | 22.4% | 24.5% | 7% |
| read short: of an item inside, read | 27.5% | 27.6% | 9% |

**Command, madhouse: rooted vectors keep their trees** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| ran: SET_PAIR | 37.8% | 51.9% | 17% |
| ran: SET_WORD | 53.5% | 70.5% | 23% |
| ran: CHECK | 55.2% | 70.2% | 22% |
| CHECK: after a write | 34.1% | 55.5% | 18% |
| ran: SHIFT_PAIRS | 35.1% | 49.1% | 17% |
| SHIFT_PAIRS: by every element | **0.1%** | 18.7% | 6% |
| ran: SHIFT_WORDS | 35.8% | 47.3% | 17% |
| SHIFT_WORDS: by none | 9.6% | 15.6% | 5% |
| SHIFT_WORDS: by every element | 5.6% | 9.6% | 3% |
| ran: RELOAD | 34.4% | 49.3% | 16% |
| RELOAD: after a write | 22.3% | 39.6% | 14% |

**Command, madhouse: an e2store file grows by records** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| appended a record of: no byte | 47.5% | 61.3% | 20% |
| appended a record of: 1 to 255 bytes | 65.0% | 77.1% | 25% |
| appended a record of: 256 bytes or more | 14.9% | 27.7% | 8% |
| appended: a Version record | 49.6% | 63.8% | 21% |
| appended: a Version record with data | 16.2% | 29.3% | 8% |
| appended: a type with a high second byte | 17.8% | 28.5% | 9% |
| ran: CHECK | 58.6% | 73.8% | 24% |
| CHECK, records: 0 | 30.7% | 32.3% | 10% |
| CHECK, records: 1 | 19.1% | 25.5% | 8% |
| CHECK, records: 2 or more | 22.4% | 47.2% | 15% |
| CHECK, as a file: read | 8.9% | 14.1% | 4% |
| CHECK, as a file: no version | 48.1% | 59.0% | 19% |
| CHECK, as a file: version with data | 4.3% | 9.6% | 2% |
| ran: INDEX | 39.8% | 56.0% | 18% |
| INDEX: no entry | 19.7% | 31.0% | 10% |
| INDEX: a negative offset | 18.2% | 28.3% | 9% |
| INDEX: a start of 2^63 or more | 23.5% | 35.6% | 11% |
| ran: CUT | 22.9% | 47.2% | 15% |
| CUT: read | **0.8%** | 30.1% | 9% |
| CUT: truncated header | 10.0% | 13.9% | 4% |
| CUT: truncated data | 14.3% | 21.2% | 6% |
| ran: SET_RESERVED | 14.0% | 41.5% | 14% |
| SET_RESERVED: not in the first record | 8.1% | 28.0% | 9% |

**Command, in order: an e2store file as a writer makes it** (1 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| appended a record of: no byte | 100.0% | 100.0% |  |
| appended a record of: 1 to 255 bytes | 100.0% | 100.0% |  |
| appended a record of: 256 bytes or more | **0.0%** | 100.0% |  |
| appended: a Version record | 100.0% | 100.0% |  |
| appended: a Version record with data | **0.0%** | **0.0%** |  |
| appended: a type with a high second byte | **0.0%** | **0.0%** |  |
| ran: INDEX | 100.0% | 100.0% |  |
| INDEX: no entry | 100.0% | 100.0% |  |
| INDEX: a negative offset | **0.0%** | **0.0%** |  |
| INDEX: a start of 2^63 or more | 100.0% | 100.0% |  |
| ran: CHECK | 100.0% | 100.0% |  |
| CHECK, records: 0 | **0.0%** | **0.0%** |  |
| CHECK, records: 1 | **0.0%** | **0.0%** |  |
| CHECK, records: 2 or more | 100.0% | 100.0% |  |
| CHECK, as a file: read | 100.0% | 100.0% |  |
| CHECK, as a file: no version | **0.0%** | **0.0%** |  |
| CHECK, as a file: version with data | **0.0%** | **0.0%** |  |
| ran: CUT | 100.0% | 100.0% |  |
| CUT: read | **0.0%** | **0.0%** |  |
| CUT: truncated header | **0.0%** | **0.0%** |  |
| CUT: truncated data | 100.0% | 100.0% |  |
| ran: SET_RESERVED | 100.0% | 100.0% |  |
| SET_RESERVED: not in the first record | **0.0%** | 100.0% |  |

#### Group `serialization: every parameter`

**RLP prefixes of every length** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| length: in the first byte | new | 11.2% | 3% |
| length: on 1 | new | 10.6% | 3% |
| length: on 2 | new | 11.7% | 3% |
| length: on 3 | new | 11.4% | 3% |
| length: on 4 | new | 7.0% | 2% |
| length: on 5 | new | 6.1% | 2% |
| length: on 6 | new | 8.4% | 2% |
| length: on 7 | new | 8.3% | 2% |
| length: on 8 | new | 6.8% | 2% |
| length: 2^64 or more | new | 18.5% | 6% |
| kind: list | new | 49.9% | 16% |
| kind: byte string | new | 50.1% | 16% |

**RLP reads a length on every count of bytes** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| input: short string | new | 3.1% | 1% |
| input: short list | new | 3.1% |  |
| input: long string, length on 1 | new | 12.0% | 3% |
| input: long string, length on 2 | new | 8.8% | 2% |
| input: long string, length on 3 | new | 7.0% | 1% |
| input: long string, length on 4 | new | 4.7% | 1% |
| input: long string, length on 5 | new | 3.0% | 1% |
| input: long string, length on 6 | new | 4.2% | 1% |
| input: long string, length on 7 | new | 3.4% | 1% |
| input: long string, length on 8 | new | 4.9% | 1% |
| input: long list, length on 1 | new | 11.1% | 3% |
| input: long list, length on 2 | new | 7.2% | 2% |
| input: long list, length on 3 | new | 6.7% | 1% |
| input: long list, length on 4 | new | 3.7% | 1% |
| input: long list, length on 5 | new | 4.8% | 1% |
| input: long list, length on 6 | new | **2.9%** | 1% |
| input: long list, length on 7 | new | 5.0% | 1% |
| input: long list, length on 8 | new | 4.4% | 1% |
| verdict: read | new | 69.1% | 22% |
| verdict: input too short | new | 12.1% | 3% |
| verdict: long form for a short length | new | 8.4% | 2% |
| verdict: leading zero in a length | new | 10.4% | 3% |
| the payload is cut short | new | 43.7% | 13% |
| the item is all there | new | 24.7% | 7% |
| all there, the length: in the first byte | new | 4.2% | 1% |
| all there, the length: on 1 | new | 6.5% | 2% |
| all there, the length: on 2 | new | 8.9% | 2% |
| all there, the length: on 3 | new | 5.1% | 1% |

**RLP reads an item between every two positions** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | new | 57.0% | 19% |
| verdict: input too short | new | 27.7% | 9% |
| verdict: a byte below 0x80 with a prefix | new | 3.7% |  |
| verdict: long form for a short length | new | 3.7% |  |
| verdict: leading zero in a length | new | 7.9% | 2% |
| from a position past the start | new | 59.9% | 19% |
| to a position before the end | new | 51.2% | 16% |
| the item ends before the stop | new | 19.6% | 6% |

**RLP numbers of every size in base 256** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| bytes: 0 | new | 11.5% | 2% |
| bytes: 1 | new | 15.8% | 5% |
| bytes: 2 to 8 | new | 28.4% | 8% |
| bytes: 9 to 32 | new | 32.6% | 11% |
| bytes: 33 or more | new | 11.7% | 3% |

**RLP scalars below every power of two** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| below 2 ^ bits | new | 25.0% | 8% |
| exactly 2 ^ bits - 1 | new | 15.0% | 4% |
| exactly 2 ^ bits | new | 36.2% | 12% |
| bits: 0 | new | 9.6% | 3% |
| bits: 1 | new | 11.2% | 2% |
| bits: 8 | new | 9.5% | 3% |
| bits: 16 | new | 9.9% | 2% |
| bits: 32 | new | 9.8% | 3% |
| bits: 64 | new | 8.5% | 3% |
| bits: 256 | new | 10.0% | 3% |
| bits: another width | new | 31.5% | 9% |

**typed RLP: byte strings of every length, fields of every fork** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| a byte string of the length of the type | new | 41.4% | 12% |
| a byte string of another length | new | 41.9% | 14% |
| a list | new | 16.7% | 5% |
| the type has no byte | new | 15.1% | 4% |
| no byte, for a type that has some | new | 11.4% | 3% |
| fields: as many as the structure has | new | 41.7% | 13% |
| a field of a fork: present | new | 62.5% | 20% |
| a field of a fork: absent | new | 37.5% | 12% |
| a field of a fork: at its first fork | new | 22.9% | 7% |

**SSZ merkleizes under every capacity and hasher** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| hasher: the table of SHA-256 | new | 23.6% | 7% |
| hasher: sha256 | new | 24.1% | 8% |
| hasher: twice | new | 24.4% | 8% |
| hasher: toy | new | 27.9% | 7% |
| zero subtree: none: the capacity is under the count | new | 10.5% | 3% |
| zero subtree: none | new | 30.2% | 10% |
| zero subtree: 1 to 7 | new | 11.8% | 3% |
| zero subtree: 8 to 31 | new | 7.9% | 2% |
| zero subtree: 32 to 63 | new | 20.9% | 6% |
| zero subtree: 64 | new | **2.9%** |  |
| zero subtree: 65 or more | new | 15.8% | 5% |
| capacity: none given | new | 6.9% | 2% |
| capacity: under the count | new | 10.5% | 3% |
| capacity: the count | new | 18.1% | 5% |
| capacity: a power of two | new | 37.9% | 11% |
| capacity: one over a power of two | new | 18.8% | 6% |
| capacity: another | new | 7.8% | 2% |
| chunks: none | new | 9.8% | 3% |

**SSZ progressive spines from every level** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| level: 0 | new | 23.5% | 6% |
| level: 1 | new | 18.0% | 5% |
| level: 2 | new | 22.0% | 6% |
| level: 3 | new | 18.3% | 6% |
| level: 4 | new | 18.2% | 6% |
| hasher: the table of SHA-256 | new | 25.2% | 7% |
| hasher: sha256 | new | 23.5% | 8% |
| hasher: twice | new | 24.3% | 8% |
| hasher: toy | new | 27.0% | 8% |
| runs: 0 | new | 19.0% | 6% |
| runs: 1 | new | 32.3% | 11% |
| runs: 2 | new | 24.1% | 7% |
| runs: 3 | new | 18.4% | 5% |
| runs: 4 or more | new | 6.2% | 1% |
| the last run is full | new | 24.2% | 8% |

**SSZ zero subtrees of every depth** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| depth: 0 to 63 | new | 60.1% | 21% |
| depth: 64 | new | 6.8% | 1% |
| depth: 65 or more | new | 33.1% | 10% |

**SSZ integers of every width** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| width: one of the six | new | 45.7% | 14% |
| width: 0 | new | **2.2%** | 1% |
| width: another up to 32 | new | 35.2% | 11% |
| width: more than 32 | new | 16.9% | 5% |
| the value fits | new | 81.7% | 26% |
| the value does not fit | new | 18.3% | 6% |
| the value: the greatest of the width | new | 3.6% | 1% |

**SSZ slots and spans of every layout** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| the bytes hold the fixed part | new | 85.2% | 28% |
| the bytes end inside the fixed part: TRUNCATED | new | 14.8% | 4% |
| from a position past the start | new | 33.9% | 11% |
| a field of variable size | new | 20.8% | 7% |
| offsets: none | new | 14.6% | 4% |
| offsets: in order within the bytes | new | 18.8% | 5% |
| offsets: one goes back | new | 52.1% | 17% |
| offsets: the last is past the end | new | 14.5% | 4% |

**SSZ values of every near count fit or do not** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| the value fits | new | 56.5% | 18% |
| the value does not fit | new | 43.5% | 14% |
| does not fit, refused as: nothing: it fits | new | 56.5% | 18% |
| does not fit, refused as: WRONG_TYPE | new | 15.9% | 5% |
| does not fit, refused as: LIMIT | new | 8.2% | 2% |
| does not fit, refused as: SCOPE | new | 14.5% | 4% |
| does not fit, refused as: UNKNOWN_SELECTOR | new | 4.9% | 1% |
| a struct with a value too few or too many | new | 10.2% | 3% |

**SSZ values of every type are zero or are not** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: zero | new | 42.6% | 13% |
| verdict: not zero | new | 43.8% | 13% |
| verdict: no default: a union inside | new | 13.6% | 4% |
| not zero, and every integer, byte and bit in it is zero | new | 24.9% | 7% |

**SSZ roots under every hasher** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| hash: sha256 | new | 36.0% | 10% |
| hash: twice | new | 31.3% | 11% |
| hash: toy | new | 32.7% | 11% |
| root: leaves: none | new | 9.7% | 3% |
| root: leaves: one | new | 40.0% | 14% |
| root: leaves: a power of two | new | 21.3% | 6% |
| root: leaves: one over a power of two | new | 14.6% | 4% |
| root: leaves: another count | new | 14.4% | 4% |
| root: capacity: 0 | new | **2.2%** |  |
| root: capacity: full | new | 49.9% | 16% |
| root: capacity: a power of two, not full | new | 9.8% | 3% |
| root: capacity: not a power of two, not full | new | 8.4% | 1% |
| root: zero subtree: none | new | 53.9% | 17% |
| root: zero subtree: 1 to 7 | new | 5.8% | 1% |
| root: zero subtree: 8 to 31 | new | **1.9%** |  |
| root: zero subtree: 32 to 63 | new | 4.2% | 1% |
| root: zero subtree: 64 | new | **0.4%** |  |
| root: zero subtree: 65 or more | new | 4.1% |  |
| root: spine: no run | new | **1.6%** |  |
| root: spine: one run | new | 5.4% | 2% |
| root: spine: two runs | new | 7.7% | 2% |
| root: spine: three runs | new | 8.1% | 2% |
| root: spine: four runs | new | 3.4% |  |
| root: spine: five runs | new | **2.9%** |  |
| root: spine: six runs or more | new | **0.6%** |  |
| root: spine: its last run is full | new | 10.0% | 3% |
| root: asks the zero root of depth 64, the last of the table | new | **0.4%** |  |
| root: asks a zero root of depth 65 or more, which is folded | new | 4.2% |  |
| root: mixes a word in | new | 60.6% | 20% |
| calls of the hash: 0 | new | 8.2% | 2% |
| calls of the hash: 1 to 9 | new | 29.8% | 10% |
| calls of the hash: 10 to 99 | new | 22.0% | 6% |
| calls of the hash: 100 or more | new | 40.0% | 12% |

**SSZ roots with every budget of nesting** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| budget: under what the value needs | new | 33.9% | 11% |
| budget: what the value needs | new | 51.8% | 16% |
| budget: between that and the nesting of the type | new | **1.9%** |  |
| budget: the nesting of the type or more | new | 12.4% | 3% |

**typed SSZ: collections of every element and length** (3,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| collection: Vector | new | 6.4% | 2% |
| collection: SszList | new | 7.4% | 2% |
| collection: ProgressiveList | new | 6.9% | 2% |
| collection: Bitvector | new | 17.5% | 5% |
| collection: Bitlist | new | 16.9% | 5% |
| collection: ProgressiveBitlist | new | 17.1% | 5% |
| collection: Vector UInt8 | new | 6.7% | 2% |
| collection: SszList UInt8 | new | 7.2% | 2% |
| collection: RootedVector | new | 6.8% | 2% |
| collection: Rooted | new | 7.1% | 2% |
| element: boolean | new | 3.0% |  |
| element: uint8 | new | **2.5%** |  |
| element: uint16 | new | **2.2%** |  |
| element: uint32 | new | **2.9%** |  |
| element: uint64 | new | **2.9%** | 1% |
| element: uint128 | new | **2.7%** |  |
| element: uint256 | new | 3.0% |  |
| element: Bytes32 | new | 3.3% | 1% |
| element: a container | new | 3.3% |  |
| element: a list | new | 3.1% |  |
| element: a bitlist | new | **2.7%** |  |
| element: a type chosen by a condition | new | 3.0% |  |
| length or limit: 0 | new | 7.6% | 2% |
| length or limit: 1 | new | 6.8% | 2% |
| length or limit: 7 | new | 7.1% | 2% |
| length or limit: 8 | new | 7.1% | 2% |
| length or limit: 9 | new | 7.9% | 2% |
| length or limit: 255 | new | 5.4% | 1% |
| length or limit: 256 | new | 4.0% | 1% |
| length or limit: 257 | new | 5.2% | 1% |
| length or limit: 2 | new | 7.6% | 2% |
| length or limit: 31 | new | 6.5% | 2% |
| length or limit: 32 | new | 7.4% | 2% |
| length or limit: 33 | new | 10.5% | 3% |
| length or limit: another | new | 16.9% | 5% |
| holds: bits: 0 | new | 9.1% | 3% |
| holds: bits: 1 | new | 8.8% | 2% |
| holds: bits: 7 | new | 6.1% | 1% |
| holds: bits: 8 | new | 5.4% | 1% |
| holds: bits: 9 | new | 4.9% | 1% |
| holds: bits: 255 | new | **2.7%** |  |
| holds: bits: 256 | new | **2.1%** |  |
| holds: bits: 257 | new | **2.2%** |  |
| holds: bits: another count | new | 22.3% | 7% |
| holds: a list at its limit | new | 7.8% | 2% |
| holds: a list of none | new | 11.5% | 3% |
| root: leaves: none | new | 16.3% | 5% |
| root: leaves: one | new | 49.7% | 16% |
| root: leaves: a power of two | new | 13.1% | 4% |
| root: leaves: one over a power of two | new | 8.2% | 2% |
| root: leaves: another count | new | 12.6% | 4% |
| root: capacity: 0 | new | **2.9%** | 1% |
| root: capacity: full | new | 55.2% | 18% |
| root: capacity: a power of two, not full | new | 13.0% | 3% |
| root: capacity: not a power of two, not full | new | 5.0% | 1% |
| root: zero subtree: none | new | 66.9% | 22% |
| root: zero subtree: 1 to 7 | new | 9.1% | 2% |
| root: zero subtree: 8 to 31 | new | **0.1%** |  |
| root: spine: no run | new | **1.7%** |  |
| root: spine: one run | new | 7.6% | 2% |
| root: spine: two runs | new | 5.3% | 1% |
| root: spine: three runs | new | 3.9% | 1% |
| root: spine: four runs | new | **2.4%** |  |
| root: spine: five runs | new | **2.6%** | 1% |
| root: spine: six runs or more | new | **0.4%** |  |
| root: spine: its last run is full | new | 10.5% | 3% |
| root: mixes a word in | new | 62.6% | 21% |

**typed SSZ: texts of every limit** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| bytes: a text within the limit | new | 59.8% | 20% |
| bytes: a text over the limit | new | 10.8% | 3% |
| bytes: no text | new | 29.4% | 8% |

**typed SSZ: every pair of forks** (3,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| type: ForkList | new | 16.5% | 5% |
| type: ForkList UInt8 | new | 17.2% | 5% |
| type: ForkBitlist | new | 17.2% | 5% |
| type: RootedForkList | new | 17.4% | 5% |
| type: a fork container | new | 15.4% | 5% |
| type: a container with fields of forks | new | 16.3% | 5% |
| the fork is: before the first | new | 35.6% | 11% |
| the fork is: the first | new | 28.5% | 8% |
| the fork is: after the first | new | 35.9% | 12% |
| and: before the last | new | 37.4% | 11% |
| and: the last | new | 26.4% | 8% |
| and: after the last | new | 36.3% | 12% |
| root: ByteList | new | 5.9% | 1% |
| root: Bitlist | new | 6.3% | 1% |
| root: ProgressiveBitlist | new | 10.9% | 3% |
| root: List | new | 12.7% | 3% |
| root: ProgressiveList | new | 32.5% | 10% |
| root: Container | new | 21.7% | 7% |
| root: ProgressiveContainer | new | 10.0% | 3% |
| at fork 0 | new | 3.3% | 1% |
| at fork 1 | new | 3.5% | 1% |
| at fork 2 | new | 3.3% | 1% |
| at fork 3 | new | 3.4% |  |
| at fork 4 | new | 3.7% | 1% |
| at fork 5 | new | 3.4% | 1% |
| at fork 6 | new | 3.9% | 1% |
| at fork 7 | new | 3.2% |  |
| at fork 8 | new | 3.3% | 1% |
| at fork 9 | new | 3.8% | 1% |
| at fork 10 | new | 4.1% | 1% |
| at fork 11 | new | 3.4% | 1% |
| at fork 12 | new | 3.2% | 1% |
| at fork 13 | new | **2.9%** | 1% |
| at fork 14 | new | 4.2% |  |
| at fork 15 | new | 3.1% |  |
| at fork 16 | new | 3.4% | 1% |
| at fork 17 | new | 3.4% | 1% |
| at fork 18 | new | 3.6% | 1% |
| at fork 19 | new | 3.7% | 1% |
| at fork 20 | new | 3.9% | 1% |
| at fork 21 | new | 3.5% | 1% |
| at fork 22 | new | 3.3% |  |
| at fork 23 | new | **2.9%** | 1% |
| at fork 24 | new | **2.7%** |  |
| at fork 25 | new | 3.6% | 1% |
| at fork 26 | new | 4.1% | 1% |
| at fork 27 | new | **2.9%** | 1% |
| at fork 28 | new | 3.2% | 1% |

**SSZ generalized indices of every spine, path and join** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| the first run, from the contents node | new | 45.4% | 14% |
| another run or another node | new | 54.6% | 18% |
| the run of the chunk: 0 | new | 7.4% | 1% |
| the run of the chunk: 1 | new | 14.5% | 4% |
| the run of the chunk: 2 | new | 13.0% | 4% |
| the run of the chunk: 3 | new | 11.9% | 4% |
| the run of the chunk: 4 | new | 13.1% | 4% |
| the run of the chunk: 5 | new | 12.1% | 3% |
| the run of the chunk: 6 or more | new | 28.0% | 8% |

**SSZ chunk positions of every element** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | new | 54.1% | 15% |
| verdict: NOT_STEPPABLE | new | 7.6% | 3% |
| verdict: NO_SUCH_FIELD | new | 18.5% | 6% |
| verdict: NO_SUCH_POSITION | new | 19.8% | 6% |
| of: boolean | new | **0.4%** |  |
| of: uint | new | **1.4%** |  |
| of: ByteVector | new | **2.2%** |  |
| of: ByteList | new | 4.1% | 1% |
| of: Bitvector | new | 4.2% |  |
| of: Bitlist | new | 4.9% | 1% |
| of: ProgressiveBitlist | new | 3.7% |  |
| of: Vector | new | 17.9% | 5% |
| of: List | new | 17.4% | 5% |
| of: ProgressiveList | new | 14.5% | 4% |
| of: Container | new | 13.6% | 4% |
| of: ProgressiveContainer | new | 9.9% | 3% |
| of: CompatibleUnion | new | 5.8% | 1% |
| the element: starts a chunk | new | 28.2% | 9% |
| the element: starts inside a chunk | new | 14.3% | 4% |
| the element: ends its chunk | new | 25.6% | 7% |
| the element: is a bit | new | 11.6% | 2% |
| the element: is in a chunk past the first | new | 24.5% | 7% |
| chunk count: none, a progressive shape | new | 28.1% | 8% |

**SSZ branches under every hash and depth** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| hash: sha256 | new | 33.0% | 11% |
| hash: twice | new | 32.9% | 10% |
| hash: toy | new | 34.1% | 10% |
| depth: 0 | new | 10.9% | 3% |
| depth: 1 to 31 | new | 55.3% | 17% |
| depth: 32 to 63 | new | 24.4% | 8% |
| depth: 64 or more | new | 9.4% | 3% |
| from a level above the leaves | new | 33.0% | 10% |
| a branch longer than the depth | new | 24.1% | 7% |
| an index of 2 ^ depth or more | new | 31.6% | 10% |

**DER reads a value of every tag** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: accepted | new | 26.1% | 7% |
| verdict: truncated | new | 36.0% | 11% |
| verdict: tag | new | 16.8% | 5% |
| verdict: length | new | 21.1% | 6% |
| length: none | new | 20.1% | 6% |
| length: short | new | 14.1% | 4% |
| length: indefinite, 0x80 | new | 4.9% | 1% |
| length: reserved, 0xff | new | 5.2% | 1% |
| length: long on 1 octet | new | 22.7% | 6% |
| length: long on 2 octets | new | 8.4% | 2% |
| length: long on 3 to 8 octets | new | 6.3% | 2% |
| length: long on 9 to 124 octets | new | 13.9% | 4% |
| length: long on 125 or 126 octets | new | 4.4% | 1% |
| tag: none | new | 10.3% | 3% |
| tag: 0 | new | **2.3%** |  |
| tag: a high tag number | new | 16.4% | 5% |
| tag: of another class than universal | new | 50.9% | 15% |
| tag: universal, constructed | new | 10.6% | 3% |
| tag: universal, primitive | new | 9.5% | 3% |
| a tag is asked for: the one of the value | new | 13.0% | 3% |
| a tag is asked for: another | new | 13.1% | 4% |

**DER validates a value of every tag** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| a tag that validation reads | new | 53.1% | 18% |
| another tag | new | 46.9% | 14% |
| the tag has no value: 0 or a high tag number | new | 12.2% | 3% |
| code points on: 1 octet | new | 21.0% | 6% |
| code points on: 2 octets | new | 19.9% | 6% |
| code points on: 3 octets | new | 19.3% | 6% |
| code points on: 4 octets | new | 19.3% | 6% |
| code points on: 5 octets | new | 20.5% | 6% |
| code points: valid | new | 68.1% | 21% |
| code points: not valid | new | 31.9% | 11% |
| valid | new | 22.6% | 7% |
| not valid, of a tag that validation reads | new | 30.5% | 10% |

**e2store headers of every type and length** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| length written on: no byte | new | 8.8% | 2% |
| length written on: 1 byte | new | 21.0% | 7% |
| length written on: 2 bytes | new | 21.6% | 6% |
| length written on: 3 bytes | new | 21.9% | 6% |
| length written on: 4 bytes | new | 26.7% | 9% |
| type: a second byte of 0x80 or more | new | 36.9% | 12% |
| type: a first byte of 0x80 or more | new | 37.6% | 12% |
| reserved: zero | new | 66.5% | 21% |
| reserved: not zero | new | 33.5% | 11% |
| from an offset past the start | new | 68.8% | 22% |
| the record: read | new | 3.3% | 1% |
| the record: reserved not zero | new | 33.9% | 11% |
| the record: truncated data | new | 56.7% | 18% |
| the record: truncated header | new | 6.1% | 1% |

**e2store index records of every count** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| verdict: read | new | 48.4% | 15% |
| verdict: refused | new | 51.6% | 17% |
| entries: 0 | new | 20.3% | 7% |
| entries: 1 | new | 11.1% | 3% |
| entries: 2 | new | 8.4% | 2% |
| entries: 3 or more | new | 8.6% | 2% |
| an entry below zero | new | 20.1% | 5% |
| refused: fewer than 16 bytes | new | 16.5% | 5% |
| refused: 16 bytes or more | new | 35.1% | 11% |

**JSON-RPC readers at every width** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| fixed: read | new | 20.3% | 5% |
| fixed: read with an upper-case digit | new | 6.0% | 1% |
| fixed: an upper-case digit, refused where the pattern has none | new | 4.0% | 1% |
| fixed: of no byte | new | 11.9% | 4% |
| fixed: the reader takes upper case | new | 51.8% | 16% |
| at most: read | new | 18.2% | 5% |
| at most: refused, and bytes | new | 3.9% | 1% |
| quantity: read | new | 17.1% | 5% |
| quantity: 2 ^ bits or more | new | 80.0% | 26% |
| quantity: exactly 2 ^ bits - 1 | new | 12.7% | 4% |
| quantity: a leading zero | new | 11.3% | 3% |

**JSON-RPC readers of every structure** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| value: array | new | 13.0% | 5% |
| value: null | new | 15.7% | 5% |
| value: object | new | 17.7% | 5% |
| value: string | new | 18.6% | 5% |
| value: true | new | 16.0% | 5% |
| value: number | new | 19.0% | 5% |
| a number: an integer | new | 77.3% | 26% |
| a number: an integer with an exponent | new | 37.3% | 12% |
| a number: not an integer | new | 22.7% | 6% |
| members: exactly those asked for | new | 6.1% | 1% |
| members: only among those asked for | new | 12.2% | 3% |

#### Group `serialization: rooted values at every length and fork`

**rooted vectors of every length: boolean** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 54.9% | 19% |
| leaves: a power of two | new | 26.8% | 8% |
| leaves: one over a power of two | new | 9.2% | 2% |
| leaves: another count | new | 9.1% | 2% |
| the last leaf is not full | new | 82.5% | 27% |
| steps: none | new | 32.2% | 11% |
| step: set | new | 55.1% | 17% |
| step: shift | new | 33.8% | 11% |
| step: reload | new | 19.5% | 6% |

**rooted vectors of every length: uint8** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 58.2% | 18% |
| leaves: a power of two | new | 25.9% | 7% |
| leaves: one over a power of two | new | 8.1% | 2% |
| leaves: another count | new | 7.8% | 2% |
| the last leaf is not full | new | 83.2% | 27% |
| steps: none | new | 33.7% | 11% |
| step: reload | new | 20.7% | 6% |
| step: set | new | 55.4% | 17% |
| step: shift | new | 34.4% | 11% |

**rooted vectors of every length: uint16** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 42.5% | 15% |
| leaves: a power of two | new | 33.7% | 9% |
| leaves: one over a power of two | new | 15.2% | 5% |
| leaves: another count | new | 8.6% | 2% |
| the last leaf is not full | new | 81.4% | 27% |
| steps: none | new | 31.7% | 10% |
| step: set | new | 55.2% | 17% |
| step: reload | new | 20.7% | 6% |
| step: shift | new | 33.7% | 11% |

**rooted vectors of every length: uint32** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 37.9% | 11% |
| leaves: a power of two | new | 34.6% | 12% |
| leaves: one over a power of two | new | 18.1% | 5% |
| leaves: another count | new | 9.4% | 3% |
| the last leaf is not full | new | 78.6% | 25% |
| steps: none | new | 34.7% | 11% |
| step: set | new | 53.1% | 16% |
| step: shift | new | 33.1% | 10% |
| step: reload | new | 22.2% | 6% |

**rooted vectors of every length: uint64** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 22.7% | 6% |
| leaves: a power of two | new | 40.6% | 13% |
| leaves: one over a power of two | new | 22.1% | 7% |
| leaves: another count | new | 14.6% | 4% |
| the last leaf is not full | new | 72.1% | 23% |
| steps: none | new | 33.5% | 11% |
| step: shift | new | 34.0% | 10% |
| step: set | new | 54.6% | 17% |
| step: reload | new | 20.1% | 6% |

**rooted vectors of every length: uint128** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 10.3% | 3% |
| leaves: a power of two | new | 44.6% | 14% |
| leaves: one over a power of two | new | 26.2% | 8% |
| leaves: another count | new | 18.9% | 5% |
| the last leaf is not full | new | 62.6% | 19% |
| steps: none | new | 34.8% | 11% |
| step: set | new | 52.0% | 17% |
| step: shift | new | 35.6% | 10% |
| step: reload | new | 19.4% | 6% |

**rooted vectors of every length: uint256** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 5.7% | 2% |
| leaves: a power of two | new | 26.5% | 9% |
| leaves: one over a power of two | new | 34.6% | 10% |
| leaves: another count | new | 33.2% | 10% |
| steps: none | new | 34.4% | 11% |
| step: shift | new | 35.0% | 11% |
| step: set | new | 54.0% | 17% |
| step: reload | new | 20.5% | 7% |

**rooted vectors of every length: Bytes32** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 7.5% | 2% |
| leaves: a power of two | new | 28.5% | 8% |
| leaves: one over a power of two | new | 31.0% | 10% |
| leaves: another count | new | 33.0% | 10% |
| steps: none | new | 35.1% | 10% |
| step: shift | new | 33.6% | 12% |
| step: reload | new | 20.1% | 7% |
| step: set | new | 50.1% | 16% |

**rooted vectors of every length: a container** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 6.7% | 1% |
| leaves: a power of two | new | 26.5% | 9% |
| leaves: one over a power of two | new | 33.2% | 10% |
| leaves: another count | new | 33.6% | 10% |
| steps: none | new | 33.8% | 10% |
| step: set | new | 53.6% | 17% |
| step: reload | new | 18.7% | 6% |
| step: shift | new | 35.2% | 11% |

**rooted vectors of every length: a list** (1,000 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| leaves: one | new | 5.4% | 2% |
| leaves: a power of two | new | 29.1% | 9% |
| leaves: one over a power of two | new | 34.7% | 11% |
| leaves: another count | new | 30.8% | 10% |
| steps: none | new | 35.3% | 11% |
| step: reload | new | 19.8% | 6% |
| step: shift | new | 35.0% | 11% |
| step: set | new | 52.2% | 17% |

**rooted lists at every pair of forks: boolean** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| before the switch: a list under a limit | new | 32.5% | 5% |
| at the switch | new | 32.5% | 6% |
| after the switch: a progressive list | new | 35.0% | 6% |
| limit: up to 100 | new | 47.5% | 9% |
| limit: 2^10 to 2^63 + 1 | new | 27.5% | 4% |
| limit: 2^64 or more | new | 25.0% | 4% |
| reached, in nodes: 0 | new | 52.5% | 10% |
| reached, in nodes: 1 | new | 84.5% | 16% |
| reached, in nodes: 2 to 5 | new | 20.5% | 3% |
| reached, in nodes: 6 to 21 | new | 27.5% | 4% |
| reached, in nodes: 22 to 85 | new | 6.5% | 1% |
| reached, in nodes: 86 to 341 | new | **2.0%** |  |
| reached, in nodes: 342 or more | new | **0.0%** |  |
| reached: a last node that is full | new | 15.5% | 3% |
| step: push many | new | 58.0% | 10% |
| step: set | new | 79.5% | 14% |
| step: set the last element | new | 61.5% | 12% |
| step: set the first element | new | 34.0% | 5% |
| step: push | new | 92.5% | 17% |
| reached: the limit | new | 10.0% | 1% |

**rooted lists at every pair of forks: uint8** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| before the switch: a list under a limit | new | 33.0% | 7% |
| at the switch | new | 33.0% | 5% |
| after the switch: a progressive list | new | 34.0% | 5% |
| limit: up to 100 | new | 49.5% | 9% |
| limit: 2^10 to 2^63 + 1 | new | 25.0% | 5% |
| limit: 2^64 or more | new | 25.5% | 4% |
| reached, in nodes: 0 | new | 43.0% | 10% |
| reached, in nodes: 1 | new | 81.5% | 16% |
| reached, in nodes: 2 to 5 | new | 19.5% | 4% |
| reached, in nodes: 6 to 21 | new | 26.0% | 3% |
| reached, in nodes: 22 to 85 | new | 8.0% | 1% |
| reached, in nodes: 86 to 341 | new | 3.5% |  |
| reached, in nodes: 342 or more | new | **0.0%** |  |
| reached: a last node that is full | new | 17.5% | 2% |
| step: push | new | 90.5% | 17% |
| reached: the limit | new | 9.0% | 1% |
| step: push many | new | 56.5% | 10% |
| step: set | new | 75.5% | 14% |
| step: set the last element | new | 61.0% | 10% |
| step: set the first element | new | 33.0% | 6% |

**rooted lists at every pair of forks: uint64** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| before the switch: a list under a limit | new | 29.5% | 7% |
| at the switch | new | 38.0% | 6% |
| after the switch: a progressive list | new | 32.5% | 5% |
| limit: up to 100 | new | 53.5% | 9% |
| limit: 2^10 to 2^63 + 1 | new | 23.5% | 5% |
| limit: 2^64 or more | new | 23.0% | 4% |
| reached, in nodes: 0 | new | 50.5% | 9% |
| reached, in nodes: 1 | new | 77.5% | 15% |
| reached, in nodes: 2 to 5 | new | 36.5% | 6% |
| reached, in nodes: 6 to 21 | new | 21.5% | 4% |
| reached, in nodes: 22 to 85 | new | 27.5% | 5% |
| reached, in nodes: 86 to 341 | new | 12.5% | 1% |
| reached, in nodes: 342 or more | new | **2.5%** |  |
| reached: a last node that is full | new | 56.5% | 11% |
| step: push | new | 88.0% | 17% |
| reached: the limit | new | 7.5% | 1% |
| step: push many | new | 54.0% | 11% |
| step: set | new | 74.0% | 15% |
| step: set the last element | new | 59.0% | 11% |
| step: set the first element | new | 33.5% | 6% |

**rooted lists at every pair of forks: uint256** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| before the switch: a list under a limit | new | 31.0% | 6% |
| at the switch | new | 31.0% | 7% |
| after the switch: a progressive list | new | 38.0% | 5% |
| limit: up to 100 | new | 49.5% | 10% |
| limit: 2^10 to 2^63 + 1 | new | 29.5% | 4% |
| limit: 2^64 or more | new | 21.0% | 4% |
| reached, in nodes: 0 | new | 54.5% | 10% |
| reached, in nodes: 1 | new | 70.5% | 13% |
| reached, in nodes: 2 to 5 | new | 59.0% | 8% |
| reached: a last node that is full | new | 100.0% | 20% |
| reached: the limit | new | 9.0% | 1% |
| step: push | new | 93.0% | 17% |
| reached, in nodes: 6 to 21 | new | 28.5% | 5% |
| reached, in nodes: 22 to 85 | new | 21.0% | 3% |
| reached, in nodes: 86 to 341 | new | 30.0% | 6% |
| reached, in nodes: 342 or more | new | 9.0% | 1% |
| step: push many | new | 54.0% | 10% |
| step: set | new | 74.5% | 13% |
| step: set the last element | new | 62.5% | 11% |
| step: set the first element | new | 37.5% | 7% |

**rooted lists at every pair of forks: Bytes32** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| before the switch: a list under a limit | new | 31.0% | 5% |
| at the switch | new | 38.0% | 6% |
| after the switch: a progressive list | new | 31.0% | 6% |
| limit: up to 100 | new | 51.0% | 9% |
| limit: 2^10 to 2^63 + 1 | new | 23.0% | 4% |
| limit: 2^64 or more | new | 26.0% | 5% |
| reached, in nodes: 0 | new | 49.0% | 9% |
| reached, in nodes: 1 | new | 67.5% | 12% |
| reached, in nodes: 2 to 5 | new | 57.5% | 11% |
| reached, in nodes: 6 to 21 | new | 31.5% | 6% |
| reached, in nodes: 22 to 85 | new | 22.5% | 4% |
| reached, in nodes: 86 to 341 | new | 27.0% | 5% |
| reached, in nodes: 342 or more | new | 8.0% | 1% |
| reached: a last node that is full | new | 100.0% | 20% |
| step: push | new | 88.5% | 17% |
| step: push many | new | 53.5% | 10% |
| step: set | new | 77.0% | 14% |
| step: set the last element | new | 62.5% | 11% |
| step: set the first element | new | 41.0% | 6% |
| reached: the limit | new | 11.0% | 1% |

**rooted lists at every pair of forks: a container** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| before the switch: a list under a limit | new | 35.5% | 7% |
| at the switch | new | 30.5% | 7% |
| after the switch: a progressive list | new | 34.0% | 5% |
| limit: up to 100 | new | 53.5% | 9% |
| limit: 2^10 to 2^63 + 1 | new | 24.5% | 4% |
| limit: 2^64 or more | new | 22.0% | 4% |
| reached, in nodes: 0 | new | 57.5% | 10% |
| reached, in nodes: 1 | new | 71.5% | 13% |
| reached, in nodes: 2 to 5 | new | 58.0% | 11% |
| reached: a last node that is full | new | 100.0% | 20% |
| reached: the limit | new | 7.0% | 1% |
| step: set | new | 74.5% | 14% |
| step: set the last element | new | 63.5% | 11% |
| step: set the first element | new | 32.5% | 6% |
| reached, in nodes: 6 to 21 | new | 24.5% | 7% |
| reached, in nodes: 22 to 85 | new | 17.5% | 3% |
| reached, in nodes: 86 to 341 | new | 28.0% | 5% |
| reached, in nodes: 342 or more | new | 5.0% | 1% |
| step: push | new | 92.5% | 17% |
| step: push many | new | 50.0% | 10% |

**rooted lists at every pair of forks: a list** (200 cases, passed).

| Class | Before | After | Minimum |
| --- | --- | --- | --- |
| before the switch: a list under a limit | new | 36.0% | 6% |
| at the switch | new | 35.0% | 6% |
| after the switch: a progressive list | new | 29.0% | 6% |
| limit: up to 100 | new | 52.0% | 9% |
| limit: 2^10 to 2^63 + 1 | new | 28.5% | 4% |
| limit: 2^64 or more | new | 19.5% | 5% |
| reached, in nodes: 0 | new | 53.0% | 11% |
| reached, in nodes: 1 | new | 69.5% | 13% |
| reached, in nodes: 2 to 5 | new | 54.5% | 11% |
| reached, in nodes: 6 to 21 | new | 32.5% | 4% |
| reached, in nodes: 22 to 85 | new | 18.5% | 4% |
| reached, in nodes: 86 to 341 | new | 28.5% | 6% |
| reached, in nodes: 342 or more | new | 9.0% | 1% |
| reached: a last node that is full | new | 100.0% | 20% |
| step: push | new | 85.5% | 17% |
| reached: the limit | new | 10.0% | 1% |
| step: push many | new | 58.0% | 10% |
| step: set | new | 75.5% | 14% |
| step: set the last element | new | 60.5% | 11% |
| step: set the first element | new | 39.5% | 6% |

#### Group `serialization: findings`

**OPEN: a branch longer than its depth is valid as phase0 says** (1 cases, failed).

It names no class.

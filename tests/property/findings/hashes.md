# Symmetric cryptography: what the property tests found

The driver is `Property/Hashes.lean` with its modules under `Property/Hashes/`.
The references are in `oracle/hashes.py`, `oracle/hashes_aes.py` and `oracle/hashes_cost.py`.
`oracle/requirements-hashes.txt` pins what they import.

```bash
cd tests/property
lake exe hashes-property 1000        # Every property, about 2 minutes.
lake exe hashes-property 1000 slow   # Also the ERC-2335 vectors, the cache of epoch 0 and a message of 2^29 bytes.
```

No property found a place where EthLib deviates from its source.
Three behaviours outside the documented preconditions are recorded below as OPEN or as notes.
The first two sections are the first round's; "Round 3: the coverage audit" below says what its generators reached and what changed since.

## What was tested

Cases are those of the last full run of the first round, `lake exe hashes-property 1000 slow`.
An earlier run of the same properties at 2000 cases, and one at 1500, also passed.
Every row passed.
Round 3 changed four rows, and each says how.

| Property | EthLib definitions | Reference | Cases |
| --- | --- | --- | --- |
| Keccak-256 | `Keccak.keccak256` | pycryptodome | 1000 |
| Keccak-512 | `Keccak.keccak512` | pycryptodome | 1000 |
| SHA-256 | `Hash.sha256`, `Sha256.hash32` | hashlib | 1000 |
| RIPEMD-160 | `Hash.ripemd160` | pycryptodome, and hashlib where OpenSSL has it | 1000 |
| CRC-32 and CRC-32C | `Crc32.crc32`, `Crc32c.crc32c`, both `digest` | zlib, crc32c | 1000 |
| BLAKE2b F | `Blake2b.compress`, rounds 0 to 200 | RFC 7693 §3.2 transcribed, checked against hashlib at start | 1000 |
| HMAC-SHA-256 | `Hmac.hmac`, `hmac32` | hmac | 1000 |
| HKDF-Expand | `Hkdf.expand` | RFC 5869 §2.3 transcribed, cross-checked with `cryptography` | 1000 |
| HKDF | `Hkdf.hkdf`, `extract` | the same | 1000 |
| TLS 1.3 HKDF-Expand-Label | `Tls13.expandLabel`, `hkdfLabel` | RFC 8446 §7.1 transcribed | 1000 |
| Concatenation KDF | `ConcatKdf.concatKdf` | `cryptography` | 1000 |
| PBKDF2 | `Pbkdf2.pbkdf2` | hashlib | 1000 |
| scrypt steps | `Scrypt.salsa208`, `blockMix`, `romix` | RFC 7914 §§3 to 5 transcribed, checked against hashlib at start | 1000 |
| scrypt | `Scrypt.scrypt`, N up to 32, r and p up to 3 | hashlib, and the rules of RFC 7914 §2 | 1000 |
| AES block | `Aes.ciph`, `ciphInv`, 128 and 256 bits; since round 3 also 192 bits by the general cipher | `cryptography` | 1000 |
| AES-CTR | `Aes.ctr`, `inc`, widths 0 to 200, counters at their wrap | SP 800-38A §6.5 and B.1 over the library's ECB, and its CTR at width 128 | 1000 |
| AES-GCM encryption | `Gcm.encrypt`, IV of 0 to 60 bytes, every tag length | pycryptodome, cross-checked with `cryptography` | 1000 |
| AES-GCM decryption | `Gcm.decrypt`, one bit changed, tags too short and too long | pycryptodome | 1000 |
| ChaCha20 block | `ChaCha20Poly1305.block` | `cryptography` | 1000 |
| ChaCha20 encryption | `crypt`, counters up to `2^32 - 1` | `cryptography`, and the counter rule | 1000 |
| Poly1305 | `poly1305` | `cryptography` | 1000 |
| ChaCha20-Poly1305 encryption | `encrypt` | `cryptography` | 1000 |
| ChaCha20-Poly1305 decryption | `decrypt`, one bit changed | `cryptography` | 1000 |
| X25519 | `X25519.x25519`, `publicKey`, low order, non-canonical, high bit | RFC 7748 §5 transcribed, cross-checked with `cryptography` | 1000 |
| RFC 6979 seed | `Rfc6979.nonceSeed` | RFC 6979 §3.2 transcribed | 1000 |
| ERC-2335 keystore | `Keystore.decrypt`, 18 mutations; since round 3, 42 changes, the limits of the caller and both cost models | ERC-2335 transcribed over hashlib and `cryptography` | 1000; 3000 since round 3 |
| Ethash sizes | `cacheSize`, `datasetSize`, epochs 0 to 2047 | the Ethash specification transcribed | 1000 |
| Ethash primality and size search | `isPrime`, `primeSize` | trial division on `Nat` | 1000 |
| Ethash seed | `Ethash.seed`, epochs up to 60 | the specification | 100 |
| Ethash cache, item and proof of work | `initialCache`, `cacheRound`, `datasetItem`, `hashimotoLight`, caches of 1 to 40 items | the specification | 250 |
| Merkle tree | `root`, `node`, `path`, `climb` | a list of levels with a symbolic hash | 1000 |
| Merkle multiproof | `helpers`, `verify` | the same model, and the definition of a helper | 1000 |
| paddings as arithmetic | `lengthBytes`, `paddingZeros`, `Keccak.padding`, `paddingByte`, `blockCount`, sizes to `2^70` | FIPS 180-4 §5.1.1, RFC 1320 §3, FIPS 202 §5.1 on `Nat` | 1000 |
| padded messages | `Sha256.pad`, `Ripemd160.pad`, `Keccak.pad`, `Keystore.shaBlocks` | the same | 1000 |
| scrypt cost bound | `Scrypt.validCost` | RFC 7914 §2 on `Nat` | 1000 |
| ChaCha20-Poly1305 length limits | `checkLengths` | RFC 8439 §2.8 | 1000 |
| AES-192 by the general cipher (replaced in round 3 by the general cipher at any `Nk` and `Nr`) | `keyExpansion 6 12`, `cipher`, `invCipher` | `cryptography` | 1000 |
| key derivations past 255 and 65535 blocks | `pbkdf2`, `concatKdf`, outputs to 2 MiB | hashlib, `cryptography` | 20 |
| machine: incremental Keccak-256 | `Keccak.Hasher` | pycryptodome | 1000 sequences of 1 to 30 |
| machine: AES-CTR stream | `Aes.ctr`, `Aes.inc` | the CTR reference | 1000 sequences of 1 to 20 |
| scenario: RFC 6979 generator | `nonceSeed`, `nonceNext`, `nonceReject` | the RFC 6979 reference | 1 in order, 1000 madhouse |
| scenario: AEAD session | `Gcm.encrypt`, `Gcm.decrypt`, ChaCha20-Poly1305 | both libraries | 1 in order, 1000 madhouse |
| a multiproof does not bind every value given (since round 3 stated the other way, and failing by design) | `Merkle.verify` | pinned behaviour | 1000 |
| a keystore number is read by its text (since round 3 stated the other way, and failing by design) | `Keystore.number` | pinned behaviour | 1 |
| ERC-2335 test vectors (slow) | `Keystore.decrypt`, scrypt N = 262144 and PBKDF2 c = 262144 | the secret of the ERC | 1 |
| Ethash epoch 0 (slow) | `Ethash.cache 0`, 262139 items, `hashimotoLight` | the specification | 1 |

The two `StateMachine` tests are the incremental hasher and the CTR stream.
The two `Command` scenarios are the RFC 6979 generator (3 commands) and the AEAD session (6 commands).
Each scenario runs once in order and then in madhouse mode whatever the environment says.

The harness was checked for sensitivity by breaking the reference in three places and running again.
A wrong Keccak-256 at lengths 135 mod 136 failed both the hash property and the hasher machine.
A counter that carries past its width failed both the CTR property and the stream machine.
A wrong pad byte in the rejection step failed both modes of the generator scenario.
The reference was then restored, and the file compared with its copy.

## Findings

No BUG and no DOC finding.

### OPEN: a keystore version is read by its JSON text

`Keystore.number` (`EthLib/Cryptography/Keystore.lean`, the `number` definition) reads a field with `Json.getNat?`.
`"version": 4e0` is read as 4 and the keystore opens.
`"version": 4.0` is refused, and so is `40e-1`.
All three are the integer 4.
The schema of ERC-2335 says only `"version": {"type": "integer"}` and names no schema draft.
A draft-04 validator refuses `4.0`, and one from draft-06 on accepts it.
The same reader takes `dklen`, `c`, `n`, `r` and `p`.
What would decide it: the draft that the ERC intends, or the behaviour of the client keystores.
`HEDGEHOG_ONLY="keystore number" lake exe hashes-property` shows it under "a keystore number is read by its value", which fails by design.

### Note: a multiproof binds values only under the preconditions of `verify_binding`

`Merkle.verify` (`EthLib/Cryptography/Merkle/Multiproof.lean`) takes an opened node as it is.
So it rebuilds the true root with a bogus value in four cases:

- A value opened below another opened node: `opened = [(1, 0), (0, 0)]`, `values = [X_{1,0}, "bogus"]`.
- A repeated position: `opened = [(0, 0), (0, 0)]`, `values = [X_{0,0}, "bogus"]`.
- A position outside the tree: `opened = [(0, 0), (0, 2^h)]`.
- More helper values than helpers: the extra ones are not read.

SOUNDNESS.md says so: "The opened positions are distinct and lie in the tree, and none is an ancestor of another. Each list of values has one value per position."
So this is not a deviation, and the caller must check those four conditions.
The SSZ multiproof in the serialization layer is that caller, and it is worth a test there.
`HEDGEHOG_ONLY=multiproof lake exe hashes-property` shows it under "a multiproof binds every value given", which fails by design.

### Note: choices of EthLib that are stricter than a reference

These are deliberate and documented, and the references were written to the same rule.

- `Hkdf.expand` refuses a key shorter than 32 bytes, as RFC 5869 §2.3 words it ("at least HashLen octets"); `cryptography` accepts any length.
- `Gcm` refuses tags of 4 and 8 bytes, which SP 800-38D allows under Appendix C.
- `Keystore` refuses `dklen < 32`; ERC-2335 only slices `decryption_key[16:32]`.
- `ChaCha20Poly1305.crypt` refuses a text that needs the counter `2^32`; RFC 8439 leaves that to the caller.

### HARNESS

- The first multiproof generator discarded empty openings and gave up; it now always opens one node.

## Not covered

- Lengths that cannot be built: SHA-256 and RIPEMD-160 at `2^61` bytes, GCM text at `2^39 - 256` bits, the `inputTooLong` branches of PBKDF2 and the Concatenation KDF.
  The length fields are tested as arithmetic up to `2^70`, but not through a real message.
  Since round 3 a real message of `2^29` bytes, whose length in bits passes `2^32`, runs twice in the slow group.
- (Covered since round 3.) GCM with the 32-bit counter wrapping inside one message: `J_0` of a non-96-bit IV cannot be chosen.
  The wrap is tested through `Aes.ctr` at width 32, which `gctr` is by definition.
  Round 3 solves for the IV of a chosen `J_0`: see "AES-GCM across the wrap of its counter".
- `Blake2b.compress` above 200 rounds, and the parsing of the EIP-152 input with its final byte other than 0 or 1.
  The parser is in the EVM precompiles, not in this layer.
- scrypt above N = 32, r = 3, p = 3 in random cases; N = 262144, r = 8 runs once in the slow group.
  Since round 3, r of 4, 8 and 16 at N of 2 and 4, and p of 8.
- Ethash caches above 40 items in random cases; epoch 0 runs once in the slow group, and no later epoch.
  No mainnet block header was checked: I had no vector at hand, and `ethereum-execution` did not install.
- `Keystore.Kdf.memory`: it is a model of EthLib's own with no source to compare.
  Since round 3 `Kdf.work` is compared with the count of a derivation as it runs, and the limit on each is tested on both sides of the cost.
- Keystore passwords outside a small set of characters; NFKD itself is the base layer's.
- The Yellow Paper's variant readings that the Ethash docstrings mention were read against `Paper.tex` (FNV, `c_size`, the compression indices) and agree, but only by eye.
- `Rfc6979.MAX_NONCES` and the signing loop that uses it: the curves layer.
- Constant time: nothing here measures it, and EthLib claims none.
- `Proofs/` and `Exports/`, by the brief.

## Notes on lean-hedgehog

These are the notes of the first round, on the library before 0.3.0; the notes on 0.3.0 close this file.

What worked well:

- `Gen.frequency` with `Gen.zipWith` made boundary-biased lengths one line (`k * block + 2 - d`), and they shrink toward the smallest failing boundary.
- Shrinking was excellent on the three injected faults.
  The Keccak fault at 135 mod 136 shrank to exactly 271 zero bytes, the smallest failing length, in 270 shrinks.
  The hasher machine shrank to one `absorb` of 271 zero bytes and one `digest`.
  The CTR fault shrank to a zero key, width 64, the counter `0^64 || 1^64` and 17 zero bytes: the minimal wrap.
  The scenario shrank to `SEED(x=0, h1=0)` then `REJECT`.
- `StateMachine` with a model state that the generator reads (`transitions s`) let chunks end exactly on, before and after a block boundary given what was already absorbed.
- `preconditions` kept the "closed stream" rule through shrinking with no extra work.
- `Gen.subsequence` then `Gen.shuffle` gave sets of tree positions directly.
- `propertyM` with an oracle in `IO` was painless; one process served about 100,000 questions per run.

What was awkward or missing:

- `Command.apply` sees only the command and the state, not the context.
  The oracle handle had to be copied into every command by `build`.
  A context argument to `apply`, or a state initialised from the context, would remove that.
- `scenario` starts from `default`, so the initial state cannot be generated.
  The session scenario needed a `Rekey` command only to move the state to interesting places.
- Madhouse sequences are fixed at 1 to 15 commands; `StateMachine.property` takes a range and `scenario` does not.
- `scenario` draws commands with `Gen.choice`, so weighting a command means listing it twice.
- `StateMachine.property` shows the state and the transitions with `Repr` only.
  A `ByteArray` of 271 bytes prints as seven lines of `0, 0, 0`; there is no `forAllWith` hook for a machine.
- The failure report says `recheck 21 ⟨..⟩ <property>`, without the name of the property, and a `checkGroup` driver has no way to take a size and a seed from the command line.
  I did not replay a failure with `recheck` for that reason; the faults were deterministic enough to rerun.
- `checkGroup` prints no totals and no time per property, and takes no seed.
- `discard` in a pure property gave up after 100 discards at 257 tests with no hint of which condition discarded; building the value right by construction fixed it.
- A property cannot run fewer tests than its group without `withTests` on each entry; a per-property cost hint would help the slow ones.

Bugs in the library: none hit.
One Lean parsing surprise, not the library's: a structure update split over two lines inside a `do` block of a `Command` instance failed to parse, and a `let` before it fixed it.

## Round 3: the coverage audit

The properties above were written before lean-hedgehog had coverage, and all passed.
This round measures what their generators reached, fixes the generators, and runs each general function at every value of its parameters that `findings/kernels.md` did not already reach.

```bash
cd tests/property
lake exe hashes-property 1000                        # Every property with its shares, 2 to 5 minutes.
lake exe hashes-property 1000 slow                   # Also the three slow ones, some minutes more.
HEDGEHOG_ONLY=keystore lake exe hashes-property 1000 # Only the properties whose name holds a word.
HEDGEHOG_ONLY=multiproof lake exe hashes-property    # With one of the two that fail by design.
```

Result: 53 properties.
48 run by default and pass, 43,620 test cases in a run of 1,000; 2 fail by design in a `mustFail` group; 3 are slow and pass when asked for.
No property found a place where EthLib deviates from its source.
That is a negative result on the inputs generated, and "Not covered in round 3" says where no input was generated.

What was run on the final driver: 1,000 cases twice, 500 cases and 100 cases, each with exit code 0 and every minimum met where one is asked.
The slow group ran once on the final build, with the default group at 100 cases: exit code 0 in 377 seconds.
The machine was shared with other runs, so a run of 1,000 took from 135 to 287 seconds.

### Shares before any generator changed

Every property got a `classify` or a `label` for each class of its input and each outcome, and nothing else changed.
The run is `lake exe hashes-property 1000`, and every property passed.
A share is the part of the test cases that a label counts; for a state machine or a scenario a test case is a sequence.
A class in bold was under 3%: the passing property had effectively not tested it.

| Property | Cases | Shares |
| --- | --- | --- |
| Keccak-256 | 1000 | **message: a block plus one 1.6%**; message: empty 8.3%; **message: exactly a block 1.3%**; message: many blocks 26.8%; message: under a block 42.3%; padding: a whole block 13.5%; padding: the one byte 0x81 4.4%; padding: two bytes or more, under a block 82.1% |
| Keccak-512 | 1000 | **message: a block plus one 1.6%**; message: empty 8.5%; **message: exactly a block 1.1%**; message: many blocks 34.4%; message: under a block 39.5%; padding: a whole block 13.1%; padding: the one byte 0x81 4.5%; padding: two bytes or more, under a block 82.4% |
| the Keccak sponge at each rate of the family | 1000 | **message: a block plus one 1.4%**; message: empty 6.6%; **message: exactly a block 1.3%**; message: many blocks 33.8%; message: under a block 39.1%; padding: a whole block 11.1%; padding: the one byte 0x81 4.4%; padding: two bytes or more, under a block 84.5%; rate: 104 bytes 25.3%; rate: 136 bytes 22.4%; rate: 144 bytes 26.7%; rate: 72 bytes 25.6% |
| SHA-256 | 1000 | **message: a block plus one 1.4%**; message: empty 6.4%; **message: exactly a block 1.3%**; message: many blocks 38.1%; message: under a block 36.8%; padding: fills the last block exactly 3.9%; padding: fits in the last block 56.6%; padding: needs one more block 39.5% |
| RIPEMD-160 | 1000 | **message: a block plus one 1.8%**; message: empty 6.1%; **message: exactly a block 1%**; message: many blocks 39.2%; message: under a block 37%; padding: fills the last block exactly 5.4%; padding: fits in the last block 58.7%; padding: needs one more block 35.9% |
| CRC-32 and CRC-32C | 1000 | message: empty 25.8%; **message: exactly 4 bytes 2.9%**; message: longer than 4 bytes 40.9%; message: shorter than the register of 4 bytes 30.4% |
| BLAKE2b F | 1000 | rounds: 1 to 9 23.8%; rounds: 10 or 11, the schedule starts again 14%; rounds: 12, as BLAKE2b 6.1%; rounds: above 12 49.3%; rounds: none 6.8%; the final block 50.3%; the high word of the offset is not zero 99% |
| HMAC-SHA-256 | 1000 | key: empty 7%; key: exactly a block 3.6%; key: longer than a block, hashed first 38.3%; key: under a block 51.1%; **message: a block plus one 2.4%**; message: empty 6.8%; **message: exactly a block 2.4%**; message: many blocks 7.3%; message: under a block 51.4% |
| HKDF-Expand | 1000 | info: empty 11.6%; key: exactly 32 bytes 24.2%; outcome: accepted 66.3%; outcome: refused, keyTooShort 25.7%; outcome: refused, outputTooLong 8%; output: empty 7.2%; output: exactly the limit 6.3%; output: one past the limit 4.8%; output: several blocks, the last one cut 52.3%; output: under a block 20.8%; output: whole blocks 19.7% |
| HKDF | 1000 | key material: empty 10.2%; outcome: accepted 92.1%; outcome: refused, outputTooLong 7.9%; output: empty 8.5%; output: exactly the limit 5.4%; output: one past the limit 3.6%; output: several blocks, the last one cut 50.2%; output: under a block 21.2%; output: whole blocks 20.1%; salt: empty 52.5%; salt: longer than a block 6.9% |
| TLS 1.3 HKDF-Expand-Label | 1000 | context: 255 bytes, the longest 10%; context: empty 14.7%; label: 249 bytes, the longest 5.3%; outcome: accepted 41.6%; outcome: refused, contextLength 6.1%; outcome: refused, hkdf 7.5%; outcome: refused, labelLength 36.7%; outcome: refused, lengthOverflow 8.1% |
| Concatenation KDF | 1000 | info: empty 11.1%; outcome: accepted 92%; outcome: refused, emptyOutput 8%; output: empty 8%; output: exactly the limit 3.7%; output: one past the limit 6%; output: several blocks, the last one cut 56.3%; output: under a block 21.8%; output: whole blocks 13.9%; secret: empty 8.8% |
| PBKDF2 | 1000 | iterations: one 38.3%; iterations: several 48.4%; outcome: accepted 80.5%; outcome: refused, emptyOutput 6.2%; outcome: refused, zeroIterations 13.3%; output: empty 7.1%; output: exactly the limit 5.7%; output: one past the limit 4.5%; output: several blocks, the last one cut 57.1%; output: under a block 23.9%; output: whole blocks 11.9%; password: longer than a block, hashed first 14%; salt: empty 10.8% |
| scrypt steps | 1000 | N = 16 26.8%; N = 2 25.6%; N = 4 24.3%; N = 8 23.3%; r = 1 33.1%; r = 2 33.7%; r = 3 33.2% |
| scrypt | 1000 | cost: 0 or 1 3.3%; cost: a power of two, too large for r 29%; cost: not a power of two 7.7%; outcome: accepted 44.2%; outcome: refused, emptyOutput 6.4%; outcome: refused, invalidBlockSize 6.2%; outcome: refused, invalidCost 33.8%; outcome: refused, invalidParallelization 9.4%; p: several blocks mixed 54.2% |
| AES block | 1000 | key: 128 bits 49.6%; key: 256 bits 50.4% |
| AES-CTR | 1000 | counter: its low bits wrap inside the data 10.6%; counter: the last block uses the last value before the wrap 10%; data: empty 6.5%; data: one block or less 44.3%; data: several blocks 49.2%; data: the last block is partial 89.4%; key: 128 bits 50.7%; key: 256 bits 49.3%; width: 0, the counter never moves 5.4%; width: 1 to 31 bits 30.5%; width: 128 bits, the whole block 8.2%; width: 32 bits, as GCM 7.6%; width: 33 to 127 bits 33.9%; width: above 128 bits 14.4% |
| AES-GCM encryption | 1000 | IV: 96 bits, the counter block itself 47.2%; IV: by GHASH, over a block with a partial one 10.9%; IV: by GHASH, under a block 26.5%; IV: by GHASH, whole blocks 11.8%; IV: empty 3.6%; additional data: empty 10.1%; additional data: the last block is partial 72.2%; additional data: whole blocks 17.7%; key: 128 bits 52.7%; key: 256 bits 47.3%; outcome: accepted 76.9%; **outcome: refused, ivLength 2.7%**; outcome: refused, shortTag 6%; outcome: refused, tagLength 14.4%; tag: 0 bytes 3%; tag: 11 bytes 3.7%; tag: 12 bytes 16.2%; tag: 13 bytes 15.8%; tag: 14 bytes 16.9%; tag: 15 bytes 15.9%; tag: 16 bytes 14.8%; tag: 17 bytes 3%; tag: 32 bytes 4.7%; tag: 4 bytes 3.4%; **tag: 8 bytes 2.6%**; text: empty 10.9%; text: one block or less 42.1%; text: several blocks 47%; text: the last block is partial 70.4% |
| AES-GCM decryption | 1000 | IV: 96 bits, the counter block itself 45.4%; IV: by GHASH, over a block with a partial one 11.8%; IV: by GHASH, under a block 27.8%; IV: by GHASH, whole blocks 9.2%; IV: empty 5.8%; additional data: empty 10.6%; additional data: the last block is partial 70.8%; additional data: whole blocks 18.6%; change: aad 12.1%; change: longTag 11.1%; change: nonce 10.5%; change: none 31.5%; change: shortTag 11.3%; change: tag 11.8%; change: text 11.7%; key: 128 bits 48.3%; key: 256 bits 51.7%; outcome: accepted 29.9%; outcome: encryption refused, nothing to open 5.8%; outcome: refused, authentication 43.3%; outcome: refused, tagLength 21%; tag: 12 bytes 19.6%; tag: 13 bytes 20.2%; tag: 14 bytes 20.2%; tag: 15 bytes 20%; tag: 16 bytes 20%; text: empty 10.1%; text: one block or less 40.3%; text: several blocks 49.6%; text: the last block is partial 73.4% |
| ChaCha20 block | 1000 | **counter: 0 1.3%**; **counter: 1, the first of the AEAD text 0.5%**; counter: 2^31 or more, the high bit 73.8%; counter: 2^32 - 1, the last 11.9% |
| ChaCha20 encryption | 1000 | counter: the data ends on the last counter, 2^32 - 1 9.6%; counter: the data needs one counter past the last 5.5%; counter: the data needs two counters or more past the last 5.9%; **data: a block plus one 1.8%**; data: empty 7.3%; **data: exactly a block 0.4%**; data: many blocks 36.7%; data: the last block is partial 87.8%; data: under a block 36.9%; outcome: accepted 88.6%; outcome: refused, counterExhausted 11.4% |
| Poly1305 | 1000 | accumulator: 2^128 or more, its high bits are dropped 57.2%; **message: a block plus one 2.3%**; message: empty 11%; **message: exactly a block 1.7%**; message: many blocks 35.1%; message: the last block is partial 83.8%; message: under a block 34.3%; r: zero after the clamp 11.4%; tag: the sum with the pad passes 2^128 43.5% |
| ChaCha20-Poly1305 encryption | 1000 | additional data: empty 10.9%; additional data: padded for the tag 70.4%; additional data: whole blocks of 16 18.7%; text: empty 6.1%; **text: exactly one block of 64 2.7%**; text: more than one block of 64 40.4%; text: padded for the tag 87.8%; text: whole blocks of 16 6.1% |
| ChaCha20-Poly1305 decryption | 1000 | additional data: empty 11.1%; additional data: padded for the tag 68.9%; additional data: whole blocks of 16 20%; change: aad 18.4%; change: nonce 17.7%; change: none 24.1%; change: tag 18%; change: text 21.8%; outcome: accepted 24.1%; outcome: refused, authenticationFailed 75.9%; text: empty 11.1%; **text: exactly one block of 64 0%**; **text: more than one block of 64 0.1%**; text: padded for the tag 69.7%; text: whole blocks of 16 19.2% |
| X25519 | 1000 | scalar: a low bit to clear 75%; scalar: bit 254 to set 49.7%; scalar: the high bit to clear 48.4%; the result is zero 30.3%; u: not canonical, p to 2^255 - 1 36.4%; u: of small order 30.3%; u: the base point 9 3.4%; u: the high bit is set, to be masked 47%; u: zero after reduction 8.6% |
| RFC 6979 seed | 1000 | hash: above the order, reduced 10.4%; hash: below the order 89.6%; **hash: the order exactly 0%**; key: the order or more 22.9%; **key: zero 0.3%**; **order: another 0%**; order: secp256k1 52.6% |
| ERC-2335 keystore | 1000 | **change: checksum 2.4%**; change: checksumfn 3.4%; change: cipher 3.1%; change: cipherfn 4.6%; change: iv15 3%; change: kdffn 3.4%; change: listparams 4%; change: nodescription 3.2%; **change: nomessage 2.8%**; change: none 39.6%; **change: noparams 2.9%**; change: nopath 3%; change: nopubkey 3.6%; **change: nouuid 2.7%**; change: oddhex 3.8%; change: prefix 4.7%; change: prf 4.5%; **change: upper 2.7%**; **change: version 2.6%**; derived key: longer than 32 bytes 74.3%; kdf: pbkdf2 50.2%; kdf: scrypt 49.8%; outcome: accepted 44.4%; outcome: refused, checksumMismatch 12.3%; outcome: refused, invalidField 26.9%; outcome: refused, unsupportedFunction 13.8%; **outcome: refused, unsupportedVersion 2.6%**; password: holds a character that NFKD changes 38.9%; password: holds a control code 51.6%; password: the one that sealed 86.7%; **secret: 32 bytes, as a BLS key 0.6%**; secret: empty 10.6%; secret: more than one block of the cipher 21.5% |
| Ethash sizes | 1000 | block: the first of its epoch 23.2%; block: the last of its epoch 19.8%; cache: the first candidate is prime 13.6%; dataset: the first candidate is prime 12.5%; **epoch: 0 0.8%**; epoch: past 512, beyond the chain's last 41.1% |
| Ethash primality and size search | 1000 | number: 0 or 1 4.1%; number: composite 86.5%; number: prime 9.4%; number: the square of a prime 14.2%; search: several steps down 72%; search: the first candidate is prime 15.3%; search: unit 1 32.7%; search: unit 128 33.7%; search: unit 64 33.6% |
| Ethash seed | 100 | block: the first or the last of its epoch 68%; epoch: 0, the seed is zeros 5%; epoch: 1 5%; epoch: 2 or more 90% |
| Ethash cache, item and proof of work | 250 | cache: more than 16 items 20%; cache: one item 12.4%; cache: two items 10.8%; dataset: its size is not whole pairs 48.8%; dataset: one pair of items 4%; index: 2^31 or more 48.4%; index: beyond the cache 96% |
| Merkle tree | 1000 | height: 0 48.1%; height: 1 22.9%; height: 2 15.5%; height: 3 8.6%; height: 4 4.6%; **height: 5 0.3%**; leaf: the first 64.1%; leaf: the last 65.1%; node: a leaf 67.2%; node: the root 68.3% |
| Merkle multiproof | 1000 | height: 0 45.6%; height: 1 26.6%; height: 2 15.1%; height: 3 8.4%; height: 4 4.2%; **height: 5 0.1%**; helpers: none 88.2%; **helpers: on several levels 0.8%**; opened: every leaf 51.3%; opened: leaves only, several 6.8%; opened: nodes of several levels 8.2%; opened: not in order of position 12.4%; opened: one node 81.2%; opened: the root alone 76.2% |
| paddings as arithmetic | 1000 | **padding: a whole block 1.9%**; **padding: fills the last block exactly 0.7%**; padding: fits in the last block 75%; padding: needs one more block 24.3%; **padding: the one byte 0x81 1.2%**; padding: two bytes or more, under a block 97%; rate: of Keccak-256 or Keccak-512 75.6%; size: its bit length passes 2^32 45.4%; size: its bit length passes 2^64, reduced 11.3% |
| padded messages | 1000 | **message: a block plus one 2.2%**; message: empty 7.1%; **message: exactly a block 2.6%**; message: many blocks 28.3%; message: under a block 38%; padding: a whole block 7.1%; padding: fills the last block exactly 4.4%; padding: fits in the last block 55.2%; padding: needs one more block 40.4%; **padding: the one byte 0x81 0%**; padding: two bytes or more, under a block 92.9% |
| scrypt cost bound | 1000 | r: zero 18.1%; refused: 0 or 1 3.7%; refused: a power of two, too large for r 17%; refused: not a power of two 67.5%; **the largest valid cost of r, 2^(16 r - 1) 0%**; the least cost too large for r, 2^(16 r) 6.6%; valid 13% |
| ChaCha20-Poly1305 length limits | 1000 | additional data: exactly the limit 14%; additional data: one past the limit 13.5%; outcome: accepted 22.8%; outcome: refused, aadTooLong 51.1%; outcome: refused, counterExhausted 26.1%; text: exactly the limit 13%; text: one past the limit 13.5% |
| AES-192 by the general cipher | 1000 | -- |
| key derivations past 255 and 65535 blocks | 20 | blocks: the index passes one byte 95%; blocks: the index passes two bytes 30%; output: the last block is cut 65% |
| machine: incremental Keccak-256 | 1000 | absorb: an empty chunk 28.7%; absorb: the chunk crosses a block 88.7%; absorb: the chunk ends exactly on a block 67.4%; absorb: the chunk ends one byte before a block 64.2%; absorb: the chunk holds two blocks or more 49.4%; absorb: the chunk stays inside a block 74.4%; digest: 135 bytes pending, the padding is one byte 20.8%; digest: after two blocks or more 46.5%; digest: nothing pending, the padding is a whole block 22.5%; digest: of nothing 20.3% |
| machine: AES-CTR stream | 1000 | piece: a tail, which closes the stream 55.3%; piece: empty 36.8%; piece: starts after the counter wrapped 30.8%; piece: the counter wraps inside it 32.4%; width: 1 bits 15.1%; width: 128 bits 15.8%; width: 2 bits 17.5%; width: 32 bits 16.6%; width: 64 bits 18.4%; width: 8 bits 16.6% |
| scenario: RFC 6979 generator, in order | 1 | a candidate drawn 100%; a candidate drawn after a rejection 100%; a candidate rejected 100%; **a rejection with no candidate drawn before 0%**; **seeded again, over a state in use 0%**; **two candidates drawn with no rejection between 0%**; two rejections or more since the seed 100% |
| scenario: RFC 6979 generator, madhouse | 1000 | a candidate drawn 30.4%; a candidate drawn after a rejection 13.8%; a candidate rejected 28%; a rejection with no candidate drawn before 23.1%; seeded again, over a state in use 20.6%; two candidates drawn with no rejection between 11.9%; two rejections or more since the seed 13.4% |
| scenario: AEAD session, in order | 1 | opened a packet 100%; opened a packet out of order 100%; **opened a packet sealed under an earlier key 0%**; refused a packet, changed: text 100%; refused a packet, changed: key 100%; **sealed at a number whose bytes carry next 0%**; **sealed at the number 2^96, whose nonce is zeros again 0%**; sealed under AES-GCM 100%; sealed under ChaCha20-Poly1305 100%; sealed with packets in flight 100% |
| scenario: AEAD session, madhouse | 1000 | opened a packet 23.5%; opened a packet out of order 7.3%; opened a packet sealed under an earlier key 5.2%; refused a packet, changed: aad 10.9%; refused a packet, changed: nonce 9.9%; refused a packet, changed: tag 11.4%; refused a packet, changed: text 10.5%; refused a packet, changed: key 10.6%; sealed at a number whose bytes carry next 14%; **sealed at the number 2^96, whose nonce is zeros again 1.3%**; sealed under AES-GCM 63.6%; sealed under ChaCha20-Poly1305 42%; sealed with packets in flight 41.7% |
| a multiproof does not bind every value given | 1000 | -- |
| a keystore number is read by its text | 1 | -- |

### What the shares showed

Sixteen weaknesses, the worst first.

1. Merkle multiproof: 76.2% of the cases opened the root alone, 88.2% needed no helper, and 0.8% had helpers on several levels.
   The generator drew any subset of the positions; a subset holds the root half the time, and the root covers every other node.
   Also 45.6% of the trees had one leaf.
2. ChaCha20-Poly1305 decryption: 0.1% of the texts were longer than one block of 64 bytes, and none was exactly one block.
   So `decrypt` had run `crypt` past its first counter in one case of 1,000.
3. ERC-2335 keystore: four of the nine refusal reasons never appeared: `shortKey`, `pbkdf2`, `scrypt` and `limitExceeded`.
   The report does not list a reason that never occurs, so only the type `KeystoreError` shows the gap.
   A fifth, `invalidJson`, cannot occur through `decrypt`, which takes parsed JSON.
   A secret of 32 bytes, the size of a BLS key, was 0.6% of the cases.
4. RFC 6979: the order was never anything but the two curve orders, and a hash equal to the order never occurred.
   `nonceSeed` takes the order as a number.
5. scrypt steps: `salsa208`, `blockMix` and `romix` each have refusals, and no case reached one.
6. AES-GCM decryption: the declared tag length was always the one that sealed.
   So the refusals `shortTag` and `tagLength t t` of `decrypt` never ran, and 5.8% of the cases sealed nothing because the IV was empty.
7. AES-CTR and AES-GCM never ran under a key of 192 bits.
8. Every hash: a message of exactly one block was 1.0% to 1.3% of the cases, and a block plus one byte 1.4% to 1.8%.
9. ChaCha20 block: the counter 0 in 1.3% and the counter 1 in 0.5%, the two that the AEAD uses.
10. ChaCha20 encryption: data of exactly one block in 0.4%.
11. BLAKE2b F: the high word of the offset was zero in 1% of the cases, and BLAKE2b itself always has it zero.
12. Paddings as arithmetic: a padding that fills the block exactly in 0.7%, the one byte `0x81` in 1.2%, a whole block in 1.9%.
    Padded messages: the one byte `0x81` never.
13. scrypt cost bound: the largest valid cost of an `r`, `2^(16 r - 1)`, never.
14. Ethash sizes: epoch 0 in 0.8%.
15. AES-GCM encryption: a tag of 8 bytes in 2.6%, and an empty IV, the only `ivLength` refusal, in 2.7%.
16. Merkle tree: height 5 in 0.3%, and no height above it.

### What changed

Generators:

- `genLen` puts a quarter of its draws on a block boundary or one byte from it, and `genMdMsg` adds the lengths 54 to 56 bytes into a block.
  The four hashes also draw a message of 1,000 to 5,000 bytes in one case of 13.
- Merkle: heights 0 to 6, the first two rarely.
  The opened set is 1 to 8 nodes, each a leaf or an ancestor of a leaf, with the root alone, every leaf and any subset as rare cases.
  The multiproof property also changes one helper value and requires another root.
- ChaCha20-Poly1305 decryption draws its text as encryption does.
  ChaCha20 encryption draws a counter that leaves the data from two blocks short of `2^32` to two blocks past it.
- Keystore: 42 changes in place of 18, a derived key of 0 to 31 bytes, a cost that the function refuses, a secret of 32 bytes in a third of the cases, and limits of the caller on each side of the cost.
  A change that a function has no field for is no longer drawn for it.
  The property runs 3 times the cases, so each change runs 20 to 80 times in a run of 1,000.
  All eight refusal reasons that `decrypt` can give now occur, the rarest (`pbkdf2`) in 4% of the cases.
- RFC 6979: the order is one of the two curves or any number with its top bit set, and the hash and the key are drawn around the order.
- scrypt steps: an input of another size, `r = 0`, and a cost that is not valid.
  scrypt: `r` of 4, 8 and 16, and `p` of 8.
- AES: keys of 128, 192 and 256 bits everywhere a key is drawn.
  CTR: any width from 0 to 128 bits, with a counter whose low bits of that width are about to wrap.
- GCM: tag lengths 0 to 20 and 32; an IV of 1 to 130 bytes; a declared tag length other than the one that sealed; an empty IV as a change before opening.
- BLAKE2b F: the high word of the offset is zero in a third of the cases, and a few cases run 255 to 5,000 rounds.

Structure, for lean-hedgehog 0.3.0:

- The six commands that held the oracle read it from the context: `apply oracle c s`.
- Each scenario gives `next` and `buildIn`, and draws a command that fits the state: `inFlight Open` is an `Open` when a packet is in flight and a seal otherwise.
  Sequences are 1 to 30 commands.
- `main` takes its selection from `Selection.fromEnv`.
- The two properties that pinned a behaviour outside a documented precondition now state the opposite and sit in a `mustFail` group.
- `Property/Hashes/Minimums.lean` holds a minimum for each class of 5% or more: a third of the least share in two runs of 1,000.
  `withMinimums` requires them in a run of 500 cases or more.

### Shares after

The run is `lake exe hashes-property 1000`.
"min" is the minimum that the property requires.
A class in bold is under 3%.
Each change of a keystore is one of 42, and runs 20 to 80 times in the 3,000 cases: its share is under 3% by its number, not by neglect.

| Property | Cases | Shares |
| --- | --- | --- |
| Keccak-256 | 1000 | message: 1,000 bytes or more 7.7% (min 2); message: a block plus one 8% (min 2); message: empty 5.1%; message: exactly a block 8.7% (min 2); message: many blocks 29.8% (min 9); message: under a block 35% (min 12); padding: a whole block 18.1% (min 4); padding: the one byte 0x81 12.6% (min 4); padding: two bytes or more, under a block 69.3% (min 23) |
| Keccak-512 | 1000 | message: 1,000 bytes or more 8.2% (min 2); message: a block plus one 6.9% (min 2); message: empty 6.3% (min 1); message: exactly a block 8.2% (min 2); message: many blocks 35.7% (min 11); message: under a block 33.2% (min 11); padding: a whole block 19.9% (min 5); padding: the one byte 0x81 11.6% (min 4); padding: two bytes or more, under a block 68.5% (min 22) |
| the Keccak sponge at each rate of the family | 1000 | message: a block plus one 8.9% (min 2); message: empty 3.8%; message: exactly a block 8.3% (min 2); message: many blocks 31.1% (min 9); message: under a block 36.4% (min 11); padding: a whole block 18.6% (min 6); padding: the one byte 0x81 11.7% (min 4); padding: two bytes or more, under a block 69.7% (min 22); rate: 104 bytes 22.1% (min 8); rate: 136 bytes 26.5% (min 8); rate: 144 bytes 24.5% (min 7); rate: 72 bytes 26.9% (min 8) |
| SHA-256 | 1000 | message: 1,000 bytes or more 7.4% (min 2); message: a block plus one 4.9% (min 1); message: empty 9.8% (min 3); message: exactly a block 4.6% (min 1); message: many blocks 37.8% (min 12); message: under a block 29.5% (min 9); padding: fills the last block exactly 9.8% (min 2); padding: fits in the last block 59.2% (min 18); padding: needs one more block 31% (min 10) |
| RIPEMD-160 | 1000 | message: 1,000 bytes or more 7.8% (min 2); message: a block plus one 5.4% (min 1); message: empty 9% (min 2); message: exactly a block 5.2%; message: many blocks 37.1% (min 12); message: under a block 28.8% (min 9); padding: fills the last block exactly 10.3% (min 3); padding: fits in the last block 58.9% (min 19); padding: needs one more block 30.8% (min 9) |
| CRC-32 and CRC-32C | 1000 | message: empty 20.1% (min 6); message: exactly 4 bytes 19% (min 5); message: longer than 4 bytes 39% (min 12); message: shorter than the register of 4 bytes 21.9% (min 7) |
| BLAKE2b F | 1000 | rounds: 1 to 9 21.6% (min 7); rounds: 10 or 11, the schedule starts again 12.9% (min 4); rounds: 12, as BLAKE2b 6.2% (min 1); rounds: 255 or more 6.8% (min 2); rounds: above 12 53.8% (min 17); rounds: none 5.5% (min 1); the final block 47% (min 16); the high word of the offset is not zero 65.1% (min 21); the high word of the offset is zero, as BLAKE2b 34.9% (min 11) |
| HMAC-SHA-256 | 1000 | key: empty 5.9% (min 1); key: exactly a block 8.9% (min 3); key: longer than a block, hashed first 40.7% (min 13); key: under a block 44.5% (min 14); message: a block plus one 10.1% (min 3); message: empty 6.2% (min 1); message: exactly a block 8.8% (min 2); message: many blocks 10.4% (min 3); message: under a block 44.6% (min 14) |
| HKDF-Expand | 1000 | info: empty 10.7% (min 3); key: exactly 32 bytes 22.7% (min 7); outcome: accepted 67.8% (min 21); outcome: refused, keyTooShort 23.8% (min 8); outcome: refused, outputTooLong 8.4% (min 2); output: empty 5.7% (min 2); output: exactly the limit 4.2%; output: one past the limit 5.6% (min 1); output: several blocks, the last one cut 55.1% (min 17); output: under a block 21.9% (min 7); output: whole blocks 17.3% (min 6) |
| HKDF | 1000 | key material: empty 11.4% (min 3); outcome: accepted 88.4% (min 29); outcome: refused, outputTooLong 11.6% (min 3); output: empty 5.8% (min 2); output: exactly the limit 4.8%; output: one past the limit 6.4% (min 1); output: several blocks, the last one cut 54.7% (min 17); output: under a block 23.7% (min 7); output: whole blocks 15.8% (min 5); salt: empty 52.2% (min 16); salt: longer than a block 10.6% (min 3) |
| TLS 1.3 HKDF-Expand-Label | 1000 | context: 255 bytes, the longest 7.5% (min 2); context: empty 14.9% (min 5); label: 249 bytes, the longest 5.2% (min 1); outcome: accepted 43.5% (min 13); outcome: refused, contextLength 7.1% (min 1); outcome: refused, hkdf 9.2% (min 2); outcome: refused, labelLength 34.3% (min 11); outcome: refused, lengthOverflow 5.9% (min 2) |
| Concatenation KDF | 1000 | info: empty 11.7% (min 3); outcome: accepted 93.6% (min 30); outcome: refused, emptyOutput 6.4% (min 2); output: empty 6.4% (min 2); output: exactly the limit 4.3%; output: one past the limit 5.9%; output: several blocks, the last one cut 54.7% (min 19); output: under a block 26% (min 7); output: whole blocks 12.9% (min 4); secret: empty 5.2% (min 1) |
| PBKDF2 | 1000 | iterations: one 39.2% (min 13); iterations: several 47.3% (min 15); outcome: accepted 80.2% (min 26); outcome: refused, emptyOutput 6.3% (min 1); outcome: refused, zeroIterations 13.5% (min 4); output: empty 6.7% (min 2); output: exactly the limit 5.3%; output: one past the limit 5.9%; output: several blocks, the last one cut 56.1% (min 18); output: under a block 24.3% (min 7); output: whole blocks 12.9% (min 4); password: longer than a block, hashed first 21.1% (min 6); salt: empty 11.6% (min 3) |
| scrypt steps | 1000 | BlockMix: accepted 69.6% (min 23); BlockMix: refused, invalidBlockSize 10.2% (min 3); BlockMix: refused, invalidInputSize 20.2% (min 5); N: 2, 4, 8 or 16 80.9% (min 26); ROMix: accepted 56.7% (min 18); ROMix: refused, invalidBlockSize 10.2% (min 3); ROMix: refused, invalidCost 17.2% (min 6); ROMix: refused, invalidInputSize 15.9% (min 4); Salsa20/8: accepted 77.7% (min 26); Salsa20/8: refused, invalidInputSize 22.3% (min 5); block: of 128 r bytes 78.5% (min 26); r = 0 10.2% (min 3); r = 1 31.3% (min 10); r = 2 28.9% (min 9); r = 3 29.6% (min 9) |
| scrypt | 1000 | cost: 0 or 1 3.6%; cost: a power of two, too large for r 26.3% (min 7); cost: not a power of two 10.9% (min 3); outcome: accepted 46.3% (min 14); outcome: refused, emptyOutput 6.2% (min 1); outcome: refused, invalidBlockSize 8.4% (min 2); outcome: refused, invalidCost 32.4% (min 10); outcome: refused, invalidParallelization 6.7% (min 2); p: several blocks mixed 63.6% (min 19); r: 4 or more 12.5% (min 4) |
| AES block | 1000 | key: 128 bits 35.7% (min 11); key: 192 bits 29.5% (min 10); key: 256 bits 34.8% (min 10) |
| the general cipher at any key length and round count | 1000 | Nk: above 6, the extra SUBWORD 32.1% (min 10); Nk: above 8 words 11% (min 3); Nk: under 4 words 15.1% (min 4); Nr: above 14 6%; Nr: no round 5.7% (min 2); Nr: one round, with no middle round 8.5% (min 2); a key of Rijndael that AES leaves out: 5 or 7 words 24.7% (min 8); a pair of AES: 4 and 10, 6 and 12, 8 and 14 21.5% (min 7); the key is longer than the schedule 4.7% (min 2); the round constant passes x^7, reduced 30.4% (min 10) |
| AES-CTR | 1000 | counter: its low bits wrap inside the data 23.4% (min 7); counter: the last block uses the last value before the wrap 14.5% (min 4); data: empty 8.9% (min 3); data: one block or less 33.4% (min 11); data: several blocks 57.7% (min 18); data: the last block is partial 59.3% (min 19); key: 128 bits 31.1% (min 10); key: 192 bits 32.1% (min 10); key: 256 bits 36.8% (min 11); width: 0, the counter never moves 6.3% (min 2); width: 1 to 31 bits 27.4% (min 8); width: 128 bits, the whole block 7.4% (min 1); width: 32 bits, as GCM 5.3%; width: 33 to 127 bits 43% (min 14); width: above 128 bits 10.6% (min 3) |
| the product of GF(2^128) and GHASH | 1000 | GHASH: of no block 19.6% (min 6); GHASH: of several blocks 57.4% (min 19); a factor is one 14.1% (min 4); a factor is zero 25.8% (min 7); the first factor is a power of x 28.7% (min 10); the last bit of a factor is set, so a shift reduces 51.1% (min 16) |
| AES-GCM encryption | 1000 | IV: 96 bits, the counter block itself 32.2% (min 10); IV: by GHASH, over a block with a partial one 19.9% (min 6); IV: by GHASH, under a block 25.2% (min 7); IV: by GHASH, whole blocks 15.2% (min 4); IV: empty 7.5% (min 2); additional data: empty 10.9% (min 3); additional data: the last block is partial 72.5% (min 23); additional data: whole blocks 16.6% (min 5); key: 128 bits 33.7% (min 10); key: 192 bits 28% (min 10); key: 256 bits 38.3% (min 11); outcome: accepted 58.4% (min 19); outcome: refused, ivLength 4.5%; outcome: refused, shortTag 16.2% (min 5); outcome: refused, tagLength 20.9% (min 6); tag: 12 bytes 13.7% (min 4); tag: 13 bytes 11.5% (min 3); tag: 14 bytes 14.9% (min 4); tag: 15 bytes 11% (min 4); tag: 16 bytes 11.8% (min 3); tag: 4 bytes 6.5% (min 2); tag: 8 bytes 9.7% (min 2); tag: a length that SP 800-38D does not have 20.9% (min 6); text: empty 10.7% (min 3); text: one block or less 43.1% (min 13); text: several blocks 46.2% (min 15); text: the last block is partial 71.8% (min 24) |
| AES-GCM decryption | 1000 | IV: 96 bits, the counter block itself 30.9% (min 11); IV: by GHASH, over a block with a partial one 20.3% (min 6); IV: by GHASH, under a block 31.3% (min 8); IV: by GHASH, whole blocks 17.5% (min 5); additional data: empty 10.2% (min 2); additional data: the last block is partial 70.2% (min 24); additional data: whole blocks 19.6% (min 6); change: aad 10.3% (min 3); change: emptyIv 10.4% (min 3); change: longTag 10% (min 3); change: nonce 9.7% (min 2); change: none 30.7% (min 9); change: shortTag 9.9% (min 3); change: tag 9.6% (min 3); change: text 9.4% (min 3); declared: 8 or 4 bytes 7% (min 2); declared: a length that SP 800-38D does not have 7.5% (min 2); declared: another supported length 7.2%; declared: the length that sealed 78.3% (min 25); key: 128 bits 34% (min 10); key: 192 bits 32.4% (min 11); key: 256 bits 33.6% (min 10); outcome: accepted 24.3% (min 7); outcome: refused, authentication 29.6% (min 10); outcome: refused, ivLength 9.4% (min 2); outcome: refused, shortTag 7% (min 2); outcome: refused, tagLength 29.7% (min 9); sealed with a tag: 12 bytes 20.4% (min 6); sealed with a tag: 13 bytes 19.7% (min 6); sealed with a tag: 14 bytes 19.4% (min 6); sealed with a tag: 15 bytes 17.5% (min 6); sealed with a tag: 16 bytes 23% (min 6); text: empty 10.5% (min 3); text: one block or less 43% (min 12); text: several blocks 46.5% (min 16); text: the last block is partial 71.1% (min 23) |
| AES-GCM across the wrap of its counter | 250 | key: 128 bits 36.4% (min 8); key: 192 bits 32.4% (min 8); key: 256 bits 31.2% (min 7); the counter wraps inside the text 46% (min 10); the counter wraps on the first block of the text 14.4% (min 4); the text ends before the wrap 21.6% (min 6); the text ends on the last counter before the wrap 16.8% (min 2) |
| ChaCha20 block | 1000 | counter: 0 8.6% (min 2); counter: 1, the first of the AEAD text 7.1% (min 2); counter: 2^31 or more, the high bit 61.1% (min 19); counter: 2^32 - 1, the last 9.8% (min 2) |
| ChaCha20 encryption | 1000 | counter: the data ends on the last counter, 2^32 - 1 21.9% (min 7); counter: the data needs one counter past the last 10.5% (min 3); counter: the data needs two counters or more past the last 5.7% (min 1); data: a block plus one 7.5% (min 2); data: empty 5.7% (min 1); data: exactly a block 9.3% (min 2); data: many blocks 27.9% (min 9); data: the last block is partial 80.6% (min 26); data: under a block 38.5% (min 11); outcome: accepted 83.8% (min 28); outcome: refused, counterExhausted 16.2% (min 5) |
| Poly1305 | 1000 | accumulator: 2^128 or more, its high bits are dropped 60% (min 20); message: a block plus one 6.7% (min 2); message: empty 7.5% (min 2); message: exactly a block 9% (min 2); message: many blocks 28.6% (min 8); message: the last block is partial 79% (min 26); message: under a block 36% (min 11); r: zero after the clamp 11.4% (min 3); tag: the sum with the pad passes 2^128 47.5% (min 14) |
| ChaCha20-Poly1305 encryption | 1000 | additional data: empty 10.8% (min 2); additional data: padded for the tag 71% (min 24); additional data: whole blocks of 16 18.2% (min 5); text: empty 5.3% (min 1); text: exactly one block of 64 10% (min 3); text: more than one block of 64 40.2% (min 13); text: padded for the tag 80.2% (min 26); text: whole blocks of 16 14.5% (min 4) |
| ChaCha20-Poly1305 decryption | 1000 | additional data: empty 10.4% (min 3); additional data: padded for the tag 72.8% (min 23); additional data: whole blocks of 16 16.8% (min 5); change: aad 18.1% (min 4); change: nonce 17.6% (min 5); change: none 26.2% (min 8); change: tag 18.7% (min 5); change: text 19.4% (min 6); outcome: accepted 26.2% (min 8); outcome: refused, authenticationFailed 73.8% (min 24); text: empty 7.9% (min 2); text: exactly one block of 64 3.4%; text: more than one block of 64 21.5% (min 6); text: padded for the tag 78% (min 24); text: whole blocks of 16 14.1% (min 5) |
| X25519 | 1000 | scalar: a low bit to clear 77% (min 25); scalar: bit 254 to set 51.8% (min 15); scalar: the high bit to clear 52.3% (min 16); the result is zero 26.9% (min 9); u: not canonical, p to 2^255 - 1 33.6% (min 10); u: of small order 26.9% (min 9); u: the base point 9 11.8% (min 3); u: the high bit is set, to be masked 52.3% (min 16); u: zero after reduction 7.6% (min 2) |
| RFC 6979 seed | 1000 | hash: above the order, reduced 27% (min 9); hash: below the order 68.5% (min 21); hash: the order exactly 4.5%; key: below the order 39.7% (min 14); key: the order or more 47.3% (min 14); key: zero 13% (min 3); order: another number of 256 bits 49.7% (min 16); order: of P-256 26.3% (min 8); order: of secp256k1 24% (min 7) |
| ERC-2335 keystore | 3000 | **change: checksum 1.4%**; **change: checksum31 1.5%**; **change: checksum33 1.3%**; **change: checksumfn 1.9%**; **change: cipher 0.9%**; **change: cipherfn 1.1%**; change: cost0 7.1%; **change: cost1 1.7%**; **change: cost3 1.8%**; **change: dklentext 1.6%**; **change: extra 0.9%**; **change: iv15 1.2%**; **change: iv17 1.3%**; **change: kdffn 1.2%**; **change: listparams 1.1%**; **change: nochecksum 1.3%**; **change: nocipher 1.7%**; **change: nocost 1.3%**; **change: nocrypto 1.1%**; **change: nodescription 1.8%**; **change: nodklen 1.4%**; **change: noiv 1%**; **change: nokdf 0.7%**; **change: nomessage 1.2%**; change: none 30.3%; **change: noparams 1.5%**; **change: nopath 1.2%**; **change: nopubkey 1.1%**; **change: nosalt 1.3%**; **change: nothex 1%**; **change: nouuid 1.2%**; **change: numdescription 1.4%**; **change: numpath 1.4%**; **change: numpubkey 1.1%**; **change: oddhex 1.4%**; **change: p0 1.7%**; **change: prefix 1.3%**; change: prf 5%; **change: r0 1.9%**; **change: upper 1.3%**; change: version 3%; **change: version5 2.9%**; **change: versiontext 2.5%**; cost: the reference ran the derivation and counted its work 74.3%; derived key: 16 to 31 bytes, sealed as the slices of the ERC read it 7.2% (min 2); derived key: longer than 32 bytes 62.7% (min 21); derived key: shorter than 16 bytes 7.3% (min 2); kdf: pbkdf2 50.2% (min 16); kdf: scrypt 49.8% (min 16); limit: on both costs exactly, opened 5.9% (min 1); limit: one byte under the memory 7.2% (min 2); limit: one unit under the work 7.4% (min 2); limit: the memory exactly 21.1% (min 6); limit: the work exactly 20.3% (min 6); outcome: accepted 21.9% (min 7); outcome: refused, checksumMismatch 4.5%; outcome: refused, invalidField 30.7% (min 10); outcome: refused, limitExceeded 5.7% (min 1); outcome: refused, pbkdf2 4.1% (min 2); outcome: refused, scrypt 8.1% (min 2); outcome: refused, shortKey 11.2% (min 3); outcome: refused, unsupportedFunction 8%; outcome: refused, unsupportedVersion 5.9% (min 1); password: holds a character next to a range of control codes 20.7% (min 6); password: holds a character that NFKD changes 39.8% (min 13); password: holds a control code 54.2% (min 17); password: holds the first or the last of a range of control codes 21.8% (min 6); password: the one that sealed 88.7% (min 29); secret: 32 bytes, as a BLS key 38.7% (min 12); secret: empty 16.4% (min 5); secret: more than one block of the cipher 54% (min 18) |
| Ethash sizes | 1000 | block: the first of its epoch 24.1% (min 6); block: the last of its epoch 20.4% (min 6); cache: the first candidate is prime 12.7% (min 3); dataset: the first candidate is prime 15.5% (min 4); epoch: 0 17.1% (min 5); epoch: past 512, beyond the chain's last 31.6% (min 9) |
| Ethash sizes of every epoch to 2047 | 1 | -- |
| Ethash primality and size search | 1000 | number: 0 or 1 4.3%; number: composite 85.4% (min 28); number: prime 10.3% (min 3); number: the square of a prime 12.4% (min 3); search: several steps down 69.1% (min 24); search: the first candidate is prime 16.9% (min 4); search: unit 1 32% (min 10); search: unit 128 35% (min 11); search: unit 64 33% (min 11) |
| Ethash seed | 100 | block: the first or the last of its epoch 70%; epoch: 0, the seed is zeros 7%; epoch: 1 17%; epoch: 2 or more 76% |
| Ethash cache, item and proof of work | 250 | cache: more than 16 items 16.8% (min 4); cache: one item 14.4% (min 3); cache: two items 8.8% (min 2); dataset: its size is not whole pairs 50.8% (min 12); dataset: one pair of items 9.6% (min 2); index: 2^31 or more 51.2% (min 13); index: beyond the cache 97.2% (min 24) |
| Merkle tree | 1000 | height: 0 12.2% (min 4); height: 1 12.3% (min 4); height: 2 16% (min 4); height: 3 14.6% (min 5); height: 4 15.9% (min 4); height: 5 14.6% (min 5); height: 6 14.4% (min 4); leaf: the first 25.4% (min 8); leaf: the last 24.9% (min 8); node: a leaf 35.1% (min 11); node: the root 33.9% (min 11) |
| Merkle multiproof | 1000 | height: 0 12.7% (min 4); height: 1 11.7% (min 3); height: 2 17.4% (min 4); height: 3 14.2% (min 4); height: 4 15.7% (min 5); height: 5 13.2% (min 5); height: 6 15.1% (min 4); helpers: none 54.9% (min 16); helpers: on several levels 30.3% (min 10); helpers: two or more on one level 21.1% (min 7); opened: every leaf 25.2% (min 7); opened: leaves only, several 21.8% (min 6); opened: nodes of several levels 25.9% (min 9); opened: not in order of position 33.5% (min 10); opened: one node 47.3% (min 15); opened: the root alone 34.6% (min 11); opened: two siblings, which need no helper between them 28% (min 8) |
| paddings as arithmetic | 1000 | padding: a whole block 9.2% (min 3); padding: fills the last block exactly 8% (min 3); padding: fits in the last block 67% (min 21); padding: needs one more block 25% (min 7); padding: the one byte 0x81 9.9% (min 3); padding: two bytes or more, under a block 81% (min 27); rate: of Keccak-256 or Keccak-512 77.8% (min 24); size: its bit length passes 2^32 49.3% (min 15); size: its bit length passes 2^64, reduced 13.5% (min 4) |
| padded messages | 1000 | message: a block plus one 3%; message: empty 8.3% (min 2); **message: exactly a block 2.8%**; message: many blocks 49.4% (min 16); message: under a block 24.9% (min 7); padding: a whole block 14.1% (min 4); padding: fills the last block exactly 5.6% (min 1); padding: fits in the last block 74.9% (min 25); padding: needs one more block 19.5% (min 5); padding: the one byte 0x81 6.6% (min 2); padding: two bytes or more, under a block 79.3% (min 25) |
| scrypt cost bound | 1000 | r: zero 18.2% (min 5); refused: 0 or 1 6.5% (min 2); refused: a power of two, too large for r 21% (min 7); refused: not a power of two 54.9% (min 17); the largest valid cost of r, 2^(16 r - 1) 5.7% (min 1); the least cost too large for r, 2^(16 r) 12.5% (min 4); valid 19.5% (min 6) |
| ChaCha20-Poly1305 length limits | 1000 | additional data: exactly the limit 14.1% (min 4); additional data: one past the limit 12.9% (min 4); outcome: accepted 23.4% (min 7); outcome: refused, aadTooLong 47.3% (min 15); outcome: refused, counterExhausted 29.3% (min 9); text: exactly the limit 12.2% (min 4); text: one past the limit 13.1% (min 4) |
| key derivations past 255 and 65535 blocks | 20 | blocks: the index passes one byte 90%; blocks: the index passes two bytes 25%; output: the last block is cut 60% |
| machine: incremental Keccak-256 | 1000 | absorb: an empty chunk 27.9% (min 8); absorb: the chunk crosses a block 88.8% (min 29); absorb: the chunk ends exactly on a block 67.2% (min 22); absorb: the chunk ends one byte before a block 64.6% (min 21); absorb: the chunk holds two blocks or more 50.4% (min 15); absorb: the chunk stays inside a block 75% (min 23); digest: 135 bytes pending, the padding is one byte 20.8% (min 6); digest: after two blocks or more 47.3% (min 15); digest: nothing pending, the padding is a whole block 24% (min 7); digest: of nothing 19.8% (min 6) |
| machine: AES-CTR stream | 1000 | piece: a tail, which closes the stream 53.2% (min 17); piece: empty 34.2% (min 12); piece: starts after the counter wrapped 43.8% (min 14); piece: the counter wraps inside it 43.4% (min 13); width: 128 bits 12.9% (min 4); width: 32 bits, as GCM 13.4% (min 4); width: not whole bytes 44.8% (min 15); width: under 8 bits 25.5% (min 8) |
| scenario: RFC 6979 generator, in order | 1 | a candidate drawn 100%; a candidate drawn after a rejection 100%; a candidate rejected 100%; a rejection with no candidate drawn before 100%; **seeded again, over a state in use 0%**; **two candidates drawn with no rejection between 0%**; two rejections or more since the seed 100% |
| scenario: RFC 6979 generator, madhouse | 1000 | a candidate drawn 68.8% (min 23); a candidate drawn after a rejection 50.9% (min 16); a candidate rejected 76.8% (min 25); a rejection with no candidate drawn before 71% (min 22); seeded again, over a state in use 56.4% (min 18); two candidates drawn with no rejection between 33.4% (min 11); two rejections or more since the seed 59.8% (min 19) |
| scenario: AEAD session, in order | 1 | opened a packet 100%; **opened a packet out of order 0%**; **opened a packet sealed under an earlier key 0%**; refused a packet, changed: tag 100%; refused a packet, changed: text 100%; sealed at a number whose bytes carry next 100%; **sealed at the number 2^96, whose nonce is zeros again 0%**; sealed under AES-GCM 100%; sealed under ChaCha20-Poly1305 100%; sealed with packets in flight 100% |
| scenario: AEAD session, madhouse | 1000 | opened a packet 52.5% (min 17); opened a packet out of order 28.6% (min 8); opened a packet sealed under an earlier key 20.5% (min 6); refused a packet, changed: aad 27.2% (min 9); refused a packet, changed: key 28.9% (min 8); refused a packet, changed: nonce 27.1% (min 9); refused a packet, changed: tag 28.3% (min 10); refused a packet, changed: text 27.9% (min 9); sealed at a number whose bytes carry next 34.2% (min 11); sealed at the number 2^96, whose nonce is zeros again 6.9% (min 2); sealed under AES-GCM 75.9% (min 25); sealed under ChaCha20-Poly1305 86.7% (min 27); sealed with packets in flight 70.3% (min 23) |
| a multiproof binds every value given | -- | fails by design |
| a keystore number is read by its value | -- | fails by design |

### Every parameter

Each general function of this area, its parameters and case splits, and where each is generated.
`findings/kernels.md` has the constant tables, the compression functions on any state, the sponge at every rate, any CRC generator and the key derivations at their limits; they are not repeated here.

| Definition | Parameters and case splits | Property | Reference |
| --- | --- | --- | --- |
| `Aes.keyExpansion Nk Nr`, `cipher Nr`, `invCipher Nr` | `Nk` 1 to 10 and `Nr` 0 to 16; the extra SUBWORD of `Nk > 6`; a key longer than the schedule; no middle round | the general cipher at any key length and round count (new) | Algorithms 1 to 3 of FIPS 197 written from the text in `oracle/hashes_aes.py`, with the S-box computed from its definition; `cryptography` confirms it at the three pairs of AES |
| `Aes.ciph`, `ciphInv` | both values of `KeySize` | AES block | `cryptography` |
| `Aes.inc m`, `Aes.ctr ciph m T data` | `m` from 0 to 128 and above; a counter 0 to 3 steps before its low `m` bits wrap; data empty, partial, whole blocks; three key sizes | AES-CTR; machine: AES-CTR stream | SP 800-38A over the library's ECB |
| `Gcm.mul`, `Gcm.ghash` | any two blocks: zero, one, a power of `x`, all ones, `R`; any hash subkey; 0 to 4 blocks | the product of GF(2^128) and GHASH (new) | the product of two polynomials reduced by `x^128 + x^7 + x^2 + x + 1`, which is not Algorithm 1 |
| `Gcm.preCounter` | 96 bits or not; under a block, whole blocks, a partial last block; 1 to 130 bytes | AES-GCM encryption; across the wrap | pycryptodome, `cryptography` |
| `Gcm.encrypt ciph t iv p aad` | `t` from 0 to 20 and 32; each of the 7 lengths of SP 800-38D; empty IV, text, data; three key sizes | AES-GCM encryption | pycryptodome, `cryptography` |
| `Gcm.decrypt ciph t iv c aad T` | `t` the one that sealed, another supported, 8 or 4, none of them; `T` one byte short or long; one bit of each input; an empty IV | AES-GCM decryption | pycryptodome |
| `Gcm.gctr` from `inc 32 J0` | the counter wraps on the first block, inside the text, right after it, or not | AES-GCM across the wrap of its counter (new) | Algorithm 4 of SP 800-38D written from the text; `cryptography` confirms each answer |
| `ChaCha20Poly1305.block` | counter 0, 1, `2^32 - 1`, any | ChaCha20 block | `cryptography` |
| `ChaCha20Poly1305.crypt` | `counter + blocks` from `2^32 - 2` to `2^32 + 2`; data empty, a block, a block plus one, many | ChaCha20 encryption | `cryptography`, and the rule of RFC 8439 §2.8 |
| `poly1305` | `r` zero after the clamp; an accumulator of `2^128` or more; a sum with the pad that passes `2^128`; each length class | Poly1305 | `cryptography`, and a model on `Nat` |
| `ChaCha20Poly1305.encrypt`, `decrypt` | data and text empty, padded or whole; text over one block of 64; one bit of each input | both AEAD properties | `cryptography` |
| `ChaCha20Poly1305.checkLengths` | each limit, one past it, any | ChaCha20-Poly1305 length limits | RFC 8439 §2.8 |
| `X25519.x25519`, `publicKey` | `u` with its high bit, not canonical, of small order, zero, 9; each bit that the scalar loses or gains | X25519 | RFC 7748 §5 written from the text, `cryptography` |
| `Rfc6979.nonceSeed q x hash` | `q` either curve or any number of 256 bits; the hash below, on and above `q`; the key 0, below `q`, `q` or more | RFC 6979 seed; scenario | RFC 6979 §3.2 written from the text |
| `Rfc6979.nonceNext`, `nonceReject` | sequences of 1 to 30 draws, rejections and seeds | scenario: RFC 6979 generator | the same |
| `Keystore.decrypt limits value password` | limits on, one under and one over each cost; both functions; 42 changes; a derived key of 0 to 64 bytes; passwords with control codes and their neighbours | ERC-2335 keystore | ERC-2335 over hashlib and `cryptography` |
| `Kdf.work`, `pbkdf2Blocks`, `hmacBlocks`, `shaBlocks` | PBKDF2 with 1 to 3 iterations; scrypt with `N` 2 to 8, `r` and `p` 1 to 2; a key of 16 to 64 bytes; a salt of 0 to 40 bytes; any password | ERC-2335 keystore | `oracle/hashes_cost.py`: HMAC, PBKDF2 and scrypt from RFC 2104, 8018 and 7914, counting each block function as it runs |
| `Kdf.memory` | the same | ERC-2335 keystore | the text of the definition only |
| `Blake2b.compress rounds h m t0 t1 f` | rounds 0 to 200, and 255 to 5,000; `t1` zero or not; `f` | BLAKE2b F | RFC 7693 §3.2 written from the text, checked against hashlib |
| `Scrypt.salsa208`, `blockMix`, `romix` | an input of the right size and of another; `r` 0 to 3; `N` valid, 0, 1, not a power of two, `2^(16 r)` | scrypt steps | RFC 7914 §§3 to 5 written from the text |
| `Scrypt.scrypt` | `N`, `r` (0 to 3, 4, 8, 16), `p` (0 to 3, 8, `2^30`), the length | scrypt | hashlib, and the rules of RFC 7914 §2 |
| `Tls13.hkdfLabel`, `expandLabel`, `extract` | a label of 0 to 256 bytes; a context of 0 to 256; a length to 65,537 | TLS 1.3 HKDF-Expand-Label; HKDF | RFC 8446 §7.1 written from the text |
| `Ethash.cacheSize`, `datasetSize`, `epoch` | every epoch from 0 to 2047, at its first block and at its last | Ethash sizes of every epoch to 2047 (new) | the Ethash specification written from the text |
| `Ethash.primeSize x unit`, `isPrime` | units 1, 64, 128; primes, squares of primes, 0 and 1 | Ethash primality and size search | trial division on `Nat` |
| `initialCache n`, `cacheRound`, `datasetItem`, `hashimotoLight size` | 1 to 40 items; any index of 32 bits; 1 to 200 pairs, with and without a remainder | Ethash cache, item and proof of work | the specification |
| `Merkle.root`, `node`, `path`, `climb`, `helpers`, `verify` | heights 0 to 6; one node, the root, every leaf, siblings, nodes of several levels, in any order | Merkle tree; Merkle multiproof | a list of levels with a symbolic hash |
| `Sha256.hash`, `Ripemd160.hash` | each length class; 1,000 to 5,000 bytes; `2^29` bytes in the slow group | SHA-256; RIPEMD-160; SHA-256 and RIPEMD-160 of 2^29 bytes (new, slow) | hashlib, pycryptodome |

Four results of the new properties are worth a line each.

- The general cipher agrees with FIPS 197 at every `Nk` from 1 to 10 and `Nr` from 0 to 16 that was drawn, 1,000 cases a run.
- GCM agrees with SP 800-38D when its 32-bit counter wraps: on the first block of the text in about 20% of 250 cases, inside the text in about 45%.
  GHASH is linear, so for one block of IV `J0 = (IV • H ⊕ L) • H`, and the reference solves `IV = (J0 • H⁻¹ ⊕ L) • H⁻¹`.
  EthLib takes that IV to the chosen `J0`, which the property also checks.
- `Kdf.work` equals the count of a derivation as it runs, in every one of about 2,200 keystores a run whose derivation the reference ran (74% of 3,000).
  The limits are inclusive: a limit equal to the cost opens the keystore, and one unit less refuses it, for memory and for work alone.
- SHA-256 and RIPEMD-160 of `2^29`, and of `2^29 + 1` to `2^29 + 64`, bytes agree with the libraries: 2 cases, 2 minutes 20 seconds.
  Their length in bits is the first to need more than 32 bits of the length field.

### The harness was checked again

Each reference was broken in one place and the run made again, then restored and compared with its copy.

| Fault in the reference | Property that failed | Shrunk counterexample |
| --- | --- | --- |
| The extra SUBWORD only for `Nk > 7` | the general cipher | `(7, 13)`, a key and a block of zeros, 46 shrinks |
| A GCM counter that carries past its 32 bits, with the library check off | AES-GCM across the wrap | a key and a head of zeros, distance 0, a text of 17 bytes, 53 shrinks |
| A work count one short for each HMAC of 32 bytes | ERC-2335 keystore | PBKDF2 with 2 iterations, a key of 32 bytes, an empty salt and password: 8 against 7 |
| The sizes of epoch 999 given for epoch 1000 | Ethash sizes of every epoch | epoch 1000 |
| A reference that opens a keystore with a derived key of 31 bytes | ERC-2335 keystore | PBKDF2 with 1 iteration, `dklen` 31, no change: `shortKey 31` against the secret |

The last one first passed: the store was sealed with a key of 32 bytes, so the short key failed the checksum in the reference too.
The reference now seals with a key of 16 to 31 bytes as the slices of the ERC read it, and the fault is seen.

### Findings of round 3

No BUG, no DOC and no new OPEN finding.

Notes:

- `Keystore` refuses `dklen` below 32, as the first round said.
  With a key of 16 to 31 bytes the slices `[16:32]` and `[:16]` of the ERC are defined in Python, and a reference that follows them opens such a keystore.
  EthLib's `shortKey` is the stricter reading, its text says so, and the reference here takes the same rule.
- The reference now refuses a `description` or a `pubkey` that is not a string, as the schema of the ERC types them, and an IV that is not 16 bytes.
  EthLib did so already.
- The two behaviours outside a documented precondition are unchanged: the multiproof binds under the preconditions of `verify_binding` only, and a keystore number is read by its JSON text.

HARNESS, each fixed:

- The first counter generator for ChaCha20 gave `2^32 + 2` for empty data, which is no 32-bit counter; the property failed with "accepted past the last counter", shrunk to a zero key, a zero nonce, no data and the counter 4294967298.
  The counter is now at most `2^32 - 1`.
- A change of the cost was drawn for PBKDF2 where only scrypt has the field, and `prf` for scrypt: the keystore was then unchanged, and its label said otherwise.

### Not covered in round 3

- `Gcm.checkLengths` above its limits: an IV of `2^61` bytes, a text of `2^36` bytes; no such buffer can be built, and the function takes the buffers, not their sizes.
- GCM with an IV of more than 130 bytes, and a chosen `J0` through an IV of more than one block.
- The general cipher with `Nk = 0`, where Algorithm 2 divides by `Nk`, and with `Nk` above 10 or `Nr` above 16.
  Below `Nk = 4` and at `Nr` that Rijndael does not pair with `Nk` the reference is the text of the algorithms alone, since no library runs there.
- `Rfc6979.nonceSeed` with an order of fewer than 256 bits: its text says the result is that of the RFC only for 256 bits.
  A key of `2^256` or more, which `int2octets` would cut.
- `Kdf.memory` against anything but its own text, and both cost models above `N = 8`, `r = 2`, `p = 2` and 3 iterations.
- The keystore changes run 20 to 80 times each in a run of 1,000, and a refusal that depends on two changes at once is not drawn.
- `Keystore.decrypt` on JSON numbers written as `4.0` or `4e0`: the OPEN item of the first round.
- Passwords are drawn from a small set of characters; NFKD on every code point is in `findings/kernels.md`.
- BLAKE2b F above 5,000 rounds.
- scrypt with `r` above 3 only at `N` of 2 and 4.
- Ethash: caches above 40 items in random cases, epochs above 2047, a seed above epoch 60, and no block header of the chain.
- A message of `2^29` bytes runs twice, with one byte repeated; SHA-256 and RIPEMD-160 at `2^61` bytes cannot be built.
- Keccak, CRC, HMAC and the key derivations on any parameter: `findings/kernels.md`.
- The error codes of each `Error.code`: they are for the bindings, and no source gives them.
- The scenarios "in order" draw each command once, so each is one random sequence; the madhouse runs are the tests.
- Constant time, `Proofs/` and `Exports/`.

## Notes on lean-hedgehog 0.3.0

What helped, concretely:

- The context first in `apply`.
  Six commands lost their `oracle` field, and two of them (`Next`, `Reject`) are now structures with no field: `build _ := pure {}`.
- `applySut sut before after t`.
  The hasher machine names a chunk by whether it crosses a block, which needs the size before and the size after.
  The stream machine names a piece that starts after the counter wrapped, from the data before it.
  In the first round the model would have had to carry its previous state.
- Coverage found sixteen weak generators in properties that had passed for two rounds; "What the shares showed" lists them.
  The worst was a multiproof property that opened the root alone in three cases of four.
- `classify` and `label` in the test, after the code under test ran: `labelOutcome` names a case by the constructor of EthLib's error.
  That is how the refusal reasons of the keystore, of GCM and of scrypt are counted.
- `Selection.fromEnv`: `HEDGEHOG_ONLY=keystore`, `HEDGEHOG_ONLY="general cipher"`, `HEDGEHOG_ONLY="GF(2^128),HKDF"`.
  Every check of the harness above was one such run of one property.
  I did not use `HEDGEHOG_RECHECK`: each failure here came back on the next run of its property.
- `mustFail`: the two pinned behaviours are now counterexamples that every run prints, and a run fails if one of them starts to pass.
- `scenario` with a range, and entries that are functions of the state.
  The list takes any `χ → σ → Gen (CommandWrapper σ m)`, so `inFlight Open` chooses by the state that `next` predicts.
  With that and sequences of 1 to 30, the sessions that opened a packet rose from 23.5% to 52%, and those that opened one out of order from 7.3% to 29%.
  The generator sequences that rejected a candidate rose from 28% to 77%.
- `buildIn`: `Open` draws its index among the packets that `next` predicts to be in flight.
- Shrinking stayed good: every fault above shrank to an input that names the fault.

What was awkward:

- A label that never occurs is absent from the report, and a label built from a value (`s!"refused, {reason}"`) exists only once its value occurs.
  The first table could not show that four refusal reasons of the keystore were never reached; I found them by reading the type.
  A way to declare the classes of a property, so that a class with no case prints 0.0%, would make such a gap visible.
- A minimum depends on the run length, so `cover` cannot sit in a property that also runs at 100 cases.
  As in the kernels driver, `withMinimums` appends `cover n name false` after the test when the run has 500 cases or more.
  With 445 minimums I wrote them to a file from the reports of two runs, with a script that reads the text of the report.
  The report as a value that a driver can print as JSON, or `checkGroup` returning the coverage, would remove the script.
- Labels print in the order of their first occurrence, which differs from run to run; the script sorts them.
- A share of a machine or a scenario counts sequences, not transitions: "absorb: the chunk crosses a block 89%" says little about how often a chunk crosses a block.
- `next` repeats by hand what `apply` does to the model, and nothing checks that they agree.
  For a seal the packet is not known before the seal runs, so `next` pushes a default packet to keep the count right; that needed `Inhabited Packet`.
- USAGE shows `Command.gen` and `Command.fixed` as the entries of a scenario, and does not say that an entry may be any function of the context and the state.
  That is the piece that made the scenarios fit their state.
- `Mode.deterministic` with `Command.gen` is one random sequence, as USAGE says; the two "in order" properties here are kept and say little.
- A length drawn through `Gen.frequency` and then a bind stopped short, as USAGE says a bind may: the GCM fault kept a text of 17 bytes where 1 byte fails too.
- `HEDGEHOG_ONLY` splits at commas, so a property whose name holds a comma cannot be named whole; two of mine do.

What is missing:

- Declared classes, and the coverage as a value, as above.
- A count per occurrence for a branch of a transition.
- A minimum that is asked only of a run above some length.

Bugs of the library: none met.

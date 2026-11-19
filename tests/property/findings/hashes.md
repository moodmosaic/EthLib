# Symmetric cryptography: what the property tests found

The driver is `Property/Hashes.lean` with its modules under `Property/Hashes/`.
The references are in `oracle/hashes.py`, and `oracle/requirements-hashes.txt` pins what it imports.

```bash
cd tests/property
lake exe hashes-property 1000        # Every property, about 75 seconds.
lake exe hashes-property 1000 slow   # Also the ERC-2335 vectors and the cache of epoch 0.
```

No property found a place where EthLib deviates from its source.
Three behaviours outside the documented preconditions are recorded below as OPEN or as notes.

## What was tested

Cases are those of the last full run, `lake exe hashes-property 1000 slow`.
An earlier run of the same properties at 2000 cases, and one at 1500, also passed.
Every row passed.

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
| AES block | `Aes.ciph`, `ciphInv`, 128 and 256 bits | `cryptography` | 1000 |
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
| ERC-2335 keystore | `Keystore.decrypt`, 18 mutations | ERC-2335 transcribed over hashlib and `cryptography` | 1000 |
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
| AES-192 by the general cipher | `keyExpansion 6 12`, `cipher`, `invCipher` | `cryptography` | 1000 |
| key derivations past 255 and 65535 blocks | `pbkdf2`, `concatKdf`, outputs to 2 MiB | hashlib, `cryptography` | 20 |
| machine: incremental Keccak-256 | `Keccak.Hasher` | pycryptodome | 1000 sequences of 1 to 30 |
| machine: AES-CTR stream | `Aes.ctr`, `Aes.inc` | the CTR reference | 1000 sequences of 1 to 20 |
| scenario: RFC 6979 generator | `nonceSeed`, `nonceNext`, `nonceReject` | the RFC 6979 reference | 1 in order, 1000 madhouse |
| scenario: AEAD session | `Gcm.encrypt`, `Gcm.decrypt`, ChaCha20-Poly1305 | both libraries | 1 in order, 1000 madhouse |
| a multiproof does not bind every value given | `Merkle.verify` | pinned behaviour | 1000 |
| a keystore number is read by its text | `Keystore.number` | pinned behaviour | 1 |
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
`lake exe hashes-property 1` shows it under "a keystore number is read by its text".

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
`lake exe hashes-property 1000` pins it under "a multiproof does not bind every value given".

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
- GCM with the 32-bit counter wrapping inside one message: `J_0` of a non-96-bit IV cannot be chosen.
  The wrap is tested through `Aes.ctr` at width 32, which `gctr` is by definition.
- `Blake2b.compress` above 200 rounds, and the parsing of the EIP-152 input with its final byte other than 0 or 1.
  The parser is in the EVM precompiles, not in this layer.
- scrypt above N = 32, r = 3, p = 3 in random cases; N = 262144, r = 8 runs once in the slow group.
- Ethash caches above 40 items in random cases; epoch 0 runs once in the slow group, and no later epoch.
  No mainnet block header was checked: I had no vector at hand, and `ethereum-execution` did not install.
- `Keystore.Kdf.memory` and `Kdf.work`: they are models of EthLib's own with no source to compare; only `shaBlocks` is checked, against the padded size.
- Keystore passwords outside a small set of characters; NFKD itself is the base layer's.
- The Yellow Paper's variant readings that the Ethash docstrings mention were read against `Paper.tex` (FNV, `c_size`, the compression indices) and agree, but only by eye.
- `Rfc6979.MAX_NONCES` and the signing loop that uses it: the curves layer.
- Constant time: nothing here measures it, and EthLib claims none.
- `Proofs/` and `Exports/`, by the brief.

## Notes on lean-hedgehog

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

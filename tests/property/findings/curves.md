# Public-key cryptography: what the property tests found

The driver is `Property/Curves.lean`, with its modules under `Property/Curves/`.
The oracle is `oracle/curves.py`, with `curves_model.py`, `curves_bls.py`, `curves_kzg.py`, `curves_xmss.py`, `curves_sphincs.py` and, since the third round, `curves_extra.py`.
`oracle/requirements-curves.txt` lists the references and their versions.

```bash
cd tests/property
lake exe curves-property 1000            # Every group.
lake exe curves-property 1000 kzg        # Only the groups whose name contains `kzg`.
HEDGEHOG_ONLY="bls verifies" lake exe curves-property 1000
```

The sections up to "Round 3" are the report of the first round, corrected where a later round changed a fact.
The third round measured what the properties of the first had reached; its report is the last section.

A slow property runs a fraction of the cases asked for; the table gives the number it ran.

## Result

No property found a place where EthLib deviates from its source.
Every failure met on the way was the harness or a quirk of a reference, and each is listed under Findings.
This is a negative result on the inputs generated, not a proof: see Not covered.

## What was tested

| Property | EthLib definitions | Answer from | Cases | Result |
| --- | --- | --- | --- | --- |
| Montgomery limbs are the integers mod p | `Montgomery.ofNat`, `toNat`, `add`, `sub`, `mul`, `neg`, `pow`, `inv`, `ofFin`, `toFin`, `toBytesBE` (8 limbs, secp256k1 `Fp`) | `Nat` | 2000 | pass |
| Montgomery limbs read bytes at an offset | `Montgomery.ofBytesBE` | `Nat` | 2000 | pass |
| the Euclidean inverse gives the gcd | `euclid`, `Fin.inverse`, any modulus | `Nat.gcd` | 2000 | pass |
| Jacobian formulas over 7, 23, 251 | `Jacobian.add`, `double`, `mulBits`, `mulAdd`, `toAffine`, any `a`, any `Z` | affine group law of SEC 1 on `Nat` | 3 x 2000 | pass |
| k1 signs as RFC 6979 with low s | `Secp256k1.Ecdsa.sign`, `signWith`, `nonceSeed` | model of RFC 6979 and SEC 1; coincurve | 1000 | pass |
| k1 verifies as SEC 1 | `Ecdsa.verify` on 14 kinds of change | model of SEC 1 section 4.1.4; coincurve on low s | 1000 | pass |
| k1 verifies a signature with x_R >= n | `Ecdsa.verify` | crafted by the oracle, model | 1000 | pass |
| k1 low-s rule | `Ecdsa.isLowS` | `Nat` | 1000 | pass |
| k1 recovers as SEC 1, and at the edges | `Ecdsa.recover` | model; coincurve; eth-keys | 2 x 1000 | pass |
| k1 decodes SEC 1 encodings only | `Point.decode`, `decompress`, `Fp.ofBytes` | coincurve, hybrid forms excluded | 1000 | pass |
| k1 encodings read back | `encodeCompressed`, `encodeUncompressed` | coincurve | 1000 | pass |
| k1 group law | `Point.add`, `mul`, `mulAdd`, `mulBits`, `neg`, `toJacobian`, `ofJacobian` | model | 1000 | pass |
| k1 ECDH, address | `ecdh`, `address`, `addressOfPrivateKey` | model; eth-keys | 2 x 1000 | pass |
| k1 field kernels | `Fp.pow`, `inv`, `sqrt`, `Fn.pow`, `inv` | `Nat` | 1000 | pass |
| r1 signs as RFC 6979 | `Secp256r1.Ecdsa.sign` | model; OpenSSL deterministic ECDSA | 1000 | pass |
| r1 verifies as SEC 1, and at the edges | `Secp256r1.verify` | model; OpenSSL | 2 x 1000 | pass |
| r1 decodes the uncompressed encoding only | `decodeUncompressed`, `encodeUncompressed` | OpenSSL | 1000 | pass |
| r1 group law | `Point.add`, `mul`, `mulAdd`, `mulBits` | model | 1000 | pass |
| bn G1 group law | `AltBn128.Point.add`, `neg`, `mulBits` | model | 2000 | pass |
| bn G2 group law | `Point2.add`, `mulBits` | py_ecc | 500 | pass |
| bn pairing value | `pairing`, `millerLoop`, `finalExponentiation` | py_ecc, all 12 coefficients | 100 | pass |
| bn pairing check | `pairingCheck` on 10 shapes of pairs | py_ecc | 100 | pass |
| bls Fr and Fp are the integers mod r and p | `Fr.*`, `Fp.*`, `fromBytesBE`, `toBytesBE`, `Fp.sqrt` | `Nat` | 1000 | pass |
| bls batch inverse | `Fr.batchInverse` | `Nat` | 1000 | pass |
| bls square root in Fp2 | `Fp2.sqrt` | Euler's criterion on the norm | 1000 | pass |
| bls G1 decompression and key validation | `G1.uncompress`, `compress`, `inSubgroup`, `keyValidate` | arkworks; py_ecc | 1000 | pass |
| bls G2 decompression | `G2.uncompress`, `compress`, `inSubgroup` | arkworks; py_ecc | 1000 | pass |
| bls G1 and G2 group law | `add`, `addMixed`, `addGeneral`, `double`, `neg`, `mulNat`, `mul`, `mulModulus`, `projectiveEq`, off the subgroup too | py_ecc | 2 x 250 | pass |
| bls multi-scalar multiplication | `G1.msm` | py_ecc, term by term | 250 | pass |
| bls pairing check | `Bls.pairingCheck` | arkworks | 250 | pass |
| bls expand_message_xmd | `expandMessageXmd`, long tags, every length | model of RFC 9380; py_ecc | 1000 | pass |
| bls hash to G2, map to curve | `hashToG2`, `mapToG1`, `mapToG2` | py_ecc; arkworks | 2 x 50 | pass |
| bls secret keys, signs | `SecretKey.fromBytes`, `skToPk`, `sign`, `popProve` | py_ecc; milagro | 500, 100 | pass |
| bls verifies | `verify`, `popVerify` on changed keys and signatures | py_ecc; milagro | 100 | pass |
| bls aggregates, aggregate verification | `aggregate`, `coreAggregateVerify`, `aggregateVerify` | py_ecc; milagro | 2 x 100 | pass |
| bls fast aggregate verification | `fastAggregateVerify`, `ethFastAggregateVerify`, `ethAggregatePubkeys` | py_ecc; milagro; consensus-specs text | 100 | pass |
| bls key generation, ERC-2333 derivation | `keyGen`, `deriveMasterSk`, `deriveChildSk`, `derivePath` | py_ecc `KeyGen`; model of ERC-2333 | 2000, 500 | pass |
| bls ERC-2334 paths | `KeyPath.parsePath`, `Path.toString` | model in Lean | 2000 | pass |
| kzg commitment, proof at a point, proof of a blob | `blobToKzgCommitment`, `kzgCommitmentToVersionedHash`, `computeKzgProof`, `verifyKzgProof`, `computeBlobKzgProof`, `verifyBlobKzgProof` | c-kzg-4844 | 3 x 100 | pass |
| kzg batch verification of blobs | `verifyBlobKzgProofBatch` | c-kzg-4844 | 100 | pass |
| kzg cells, recovery, batch verification of cells | `computeCells`, `computeCellsAndKzgProofs`, `recoverCellsAndKzgProofs`, `verifyCellKzgProofBatch` | c-kzg-4844 | 3 x 40 | pass |
| xmss verifies valid signatures only | `Xmss.verify`, `decodeSignature`, `decodePublicKey`, `signatureIndex`, encoders | model of the specification | 1000 | pass |
| xmss codewords, path to the root | `codeword?`, `fold` | model | 2 x 1000 | pass |
| xmss leaf of a one-time signature | `otsLeaf`, `Internal.findCodeword` | model | 50 | pass |
| xmss public parameter and subtrees | `schemeSeed`, `publicParamOf`, `node` to level 3 | model | 50 | pass |
| xmss one-time signature | `otsSign`, `otsPublicLeaf` | model | 5 | pass |
| vrf verifies valid openings only | `Vrf.verifyBytes`, `verify`, `decodeOpening`, `encodeOpening` | model of `vrf.Verify` | 1000 | pass |
| vrf secret, output and mix | `secret`, `evaluate`, `mixOutput` | model | 1000 | pass |
| sphincs signs, verifies and refuses changes | `Sphincs.keyGen`, `sign`, `verify`, encoders and decoders | model of verification; refusal of every changed bit | 100 without the model, 20 with it | pass |
| sphincs digest fields | `digestLeaves`, `digestTree`, `digestLeaf`, `digestIndex` | `Nat` | 5000 | pass |
| poly sums, products, values, product bound | `addPolynomialcoeff`, `multiplyPolynomialcoeff`, `evaluatePolynomialcoeff`, `computePowers` | model of the specification on `Nat` | 2000, 100 | pass |
| poly division | `dividePolynomialcoeff` | inverse of the model's product | 2000 | pass |
| poly interpolation and vanishing polynomial | `interpolatePolynomialcoeff`, `vanishingPolynomialcoeff` | values at the points | 2000 | pass |
| poly bit reversal, roots of unity and cosets | `reverseBits`, `bitReversalPermutation`, `computeRootsOfUnity`, `rootsOfUnityBrp`, `cosetForCell` | powers of 7 on `Nat` | 500 | pass |
| poly FFT, evaluation form, cell, packed indices | `fftField`, `evaluatePolynomialInEvaluationForm`, `polynomialEvalToCoeff`, `interpolateCosetEvals`, `unpackIndicesBE` | the sums they stand for | 2000, 200, 500, 2000 | pass |
| G1 accumulator (`StateMachine`) | `G1.add`, `double`, `neg`, `mulNat`, `compress`, `uncompress` in sequences of up to 30 | scalar mod `r`; py_ecc | 500 sequences | pass |
| RFC 6979 nonce generator (`StateMachine`) | `Rfc6979.nonceSeed`, `nonceNext`, `nonceReject`, sequences of up to 40 | model of RFC 6979 | 2000 sequences | pass |
| BLS signers (`Command`, madhouse) | 7 commands over `Bls.Signatures`: register, register the opposite key, sign, tamper, aggregate one message, aggregate all, empty set | py_ecc; milagro; the sum of the keys | 100 sequences of 1 to 15, and the deterministic order once | pass |
| KZG blob store (`Command`, madhouse) | 5 commands over `Kzg`: add a blob, verify all, sample cells, lose and recover, open at a point | c-kzg-4844; the cells stored | 40 sequences of 1 to 15, and the deterministic order once | pass |

The counts are the largest run of each property.
`lake exe curves-property 1000` runs each at 1,000 cases or at the fraction its cost allows: 250 for the BLS group laws, 50 for pairings, BLS signatures and KZG blobs, 20 for KZG cells and SPHINCS signatures, 5 for an XMSS one-time signature.
The last full pass at 1,000, group by group, had no failure.

## Findings

None of these is a deviation of EthLib from its source.

### 1. HARNESS (reference quirk): c-kzg copies the cells when all 128 are given

- Definition: `recoverCellsAndKzgProofs`, `EthLib/Cryptography/Kzg/Recovery.lean:138`.
- Shrunk counterexample: the zero blob, the indices `0` to `127`, and element 0 of cell 0 replaced by another canonical number, so that the cells are not the values of one polynomial of degree below 4096.
- EthLib returns the cells of the polynomial that `recoverPolynomialcoeff` gives, cut to 4096 coefficients.
- c-kzg-4844 2.1.8 returns the 128 input cells unchanged, and the same proofs as EthLib.
- The source decides for EthLib: `recover_cells_and_kzg_proofs` of `specs/fulu/polynomial-commitments-sampling.md` ends with "`polynomial_coeff = recover_polynomialcoeff(cell_indices, cosets_evals)`" and "`return compute_cells_and_kzg_proofs_polynomialcoeff(polynomial_coeff)`", with no case for 128 cells.
- The two agree on every input whose cells are consistent, which is the only case a caller that verified the cells can meet.
- The property now compares only the proofs in that one case, and says so in a comment.
- Corrected in the third round: the difference is not one of 128 cells, and c-kzg does not only copy.
  It answers other cells than the text on any more than 64 cells that no polynomial gives; see finding 4 of Round 3, where the property was made to check EthLib's cells too.
- The quoted lines were read from the revision of consensus-specs that EIP-7594 links, which is not the one that `tests/sources.toml` pins; the specification itself was not run, so "EthLib follows the text" rests on reading `Recovery.lean` against it.

### 1b. HARNESS: the oracle that crafts a signature with `x_R >= n` looped

- `k1_craft` searched upward for an `x` with a point, past `p - n`, where no `x + n` is below `p`; the search now wraps.
- It showed as a run that never ended, not as a failure.

### 2. HARNESS (reference quirks): the three BLS references disagree at the edges of an encoding

- arkworks `from_compressed_bytes_unchecked` reads any bytes under the infinity flag as the point at infinity (`e0 00...`, `c0 00...01`); EthLib and py_ecc refuse them, as the Zcash encoding requires.
- py_ecc `decompress_G1` refuses `80 00...00`, the point `(0, 2)` of the curve, because it takes `x = 0` for the point at infinity; EthLib and arkworks decode it, and key validation then refuses it in all three, since it is not in the subgroup.
- The oracle asks py_ecc under the infinity flag, arkworks at `x = 0`, and both elsewhere.

## Not covered

- XMSS `keyGen`, `sign`, `path` and VRF `keyGen`, `prove`, `root`: they build `2^16` one-time keys or a tree of `2^32` leaves. The parts were tested instead (one one-time signature, subtrees to level 3, the climb, verification on the repository's four valid signatures), and the composition rests on the vectors of `tests/cryptography`.
- leanSPHINCS signing has no reference: the model covers verification only, so a signer that deviates from the scheme and still verifies under EthLib's own verifier and the model would pass. The model was checked against the 26 `verify` vectors.
- The models of leanXMSS, leanSPHINCS and the VRF tree were written from the formulas in EthLib's docstrings and from FIPS 205, since the specification drafts are not in the tree. A formula that is wrong in the docstring and in the code alike is not caught.
- The value of the BLS12-381 pairing in `Fp12` is not compared here; the kernels driver compares it with py_ecc, coefficient by coefficient (`findings/kernels.md`).
- `G1.msm` runs its windows as tasks; nothing here tests it under a constrained thread pool.
- `Bls.Fp6`, `Fp12` and `Bls.Pairing.millerLoop` are reached here only through the pairing check; the kernels driver tests them directly.
- The precompile-shaped wrappers (`Execution/Evm/Precompiles`: padding of short input, the 192-byte pairs, P256VERIFY) belong to the EVM layer and its driver.
- `Cryptography/Exports` and the proofs were out of scope in the first round; the third tests the exports of secp256k1 and P-256.
- Constant time: none of this measures time.
- `computeChallenge`, `computeVerifyKzgProofBatchChallenge` and `computeVerifyCellKzgProofBatchChallenge` are reached only through the proofs and verifications that use them.
- `hashToG2` with an empty tag was compared in the first round only through `expand`; since the third round the oracle hashes under any tag, with py_ecc's maps (`h2g2any`).

## Notes on lean-hedgehog

These are the notes of the first round, on the library before 0.3.0.
Several of the missing pieces below exist now; the notes on 0.3.0 are at the end of Round 3.

What worked well:

- `Gen.frequency` with named edge cases made every generator of this layer: one line per edge of a modulus, and the report names the drawn value.
- Shrinking of structured cases was very good where the generator was a `Gen.zip` of small parts. The G1 decoding failure shrank from random bytes to `e0 00...00`, the minimal encoding that shows the disagreement, in 3 shrinks. The recovery failure shrank to the zero blob with no overrides.
- `StateMachine` with a `Nat` model (a scalar mod `r` against a Jacobian point) took 40 lines, and `transitions s` reading the state made "add the opposite of the accumulator" a one-liner.
- `Range.exponential` on bounds of `2^256` and `2^384` is exact, which is what a field needs.
- `Gen.subsequence` and `Gen.shuffle` gave the cell indices of recovery (ascending subsets, then disorder) directly.
- `Property IO` with `propertyM` and one long-lived oracle process was fast: about 1,000 round trips a second.

What was awkward or missing:

- `Command.apply` does not receive the context `χ`; only `build` does. A scenario that drives an oracle or needs a trusted setup must copy the handle into every command structure (`structure Sign where oracle : Oracle ...`), or put it in the state. An `apply : χ → κ → σ → TestT m σ` would remove that.
- `Model.apply` is pure, so a model that needs the reference process cannot be a `Model`. The nonce machine keeps a log of its transitions as the model state and replays it through the oracle in `invariants`. A monadic model, or `invariants` as the documented place for it, would help.
- No `classify`, `label` or `cover`. Most properties here mix valid and changed inputs, and nothing reports how many cases took the accepting branch. I had to reason about the weights instead of reading a count; this is the feature I missed most.
- `scenario` fixes the madhouse length at 1 to 15 commands. Reaching "five keys registered, then aggregate" needs longer runs; a `Range` argument as `StateMachine.property` has would do.
- `scenario` starts from `default`, so the initial state cannot be generated, where `Model.initState` is a `Gen`.
- `Gen.filter` in a property gives up after 100 discards and the report says `⚐ ... gave up`, which is easy to miss in a long group. The Jacobian property over 7 first gave up at 643 tests; a filtered generator for the curve fixed it.
- `recheck` takes the property as a Lean value, so replaying a failure of an executable driver means editing the driver. A `checkGroup` that accepts a size and seed (from the environment, say) would make the printed line usable as it is.
- `StateMachine.property` needs `Repr σ` and `Repr τ` and has no `forAllWith` variant; for a state without `Repr` one must rebuild the property from `sequence` and `run`, as `HedgehogTest/Counter.lean` does.
- Every shrink runs the test again. With a case that costs seconds (KZG cells, a SPHINCS signature) the default of 1,000 shrinks can take an hour; `withShrinks` is needed on slow properties, and a time bound would be more natural than a count.
- A value drawn after a `forAll` that depends on an earlier one (the override value of a blob after its index) shrinks less far than the same data in one `Gen.zip`; USAGE says so, and it showed: the replaced element of the recovery failure stayed a 255-bit number.
- There is no generator of `ByteArray`; `Support.genBytes` goes through a list, and a 131,072-byte blob had to be described by a small structure instead of generated, which was the better design anyway.

Bugs in the library: none met.

Shrunk counterexamples: of the failures seen (all harness), each was readable without further work, except that long hexadecimal inputs (a 2,404-byte signature) print in full in the report.

## Round 3: the coverage audit

The properties above were written before lean-hedgehog had coverage, and all of them passed.
This round first asks what share of the cases of each property reached each outcome and each branch.
Every property now names its classes with `classify` and `label`.
The first table below is read from the reports of a run made before any generator changed.

```bash
cd tests/property
lake exe curves-property 1000                      # Every group, with the shares: 20 minutes.
lake exe curves-property                           # 100 cases, no minimum asked: 3 minutes.
HEDGEHOG_ONLY="bls verifies" lake exe curves-property 1000
lake exe curves-property 1000 kzg                  # Only the groups whose name contains `kzg`.
```

### Before: the shares of the first-round generators

`lake exe curves-property 1000`, one process per group.
A slow property ran the fraction of 1,000 that the first round gave it: the count is in the second column.
A class under about 3% is marked **low**; a class at 0% was never tested by the passing property.

| Property | Cases | Shares that were fine | Classes under 3% |
| --- | --- | --- | --- |
| Montgomery limbs read bytes at an offset | 1000 | read below `p` 99.9% | **refused: exactly `p` 0.0%, above `p` 0.1%**: the refusal was not tested |
| Jacobian formulas over 251 | 1000 | doubling 24%, `P = -Q` 23% | **order two 0.7%, `a = 0` 0.3%**, scalar zero 2.7% |
| k1 signs | 1000 | zero key 21%, hash `≥ n` 18%, `s` negated 47%, kept 46% | none |
| k1 verifies | 1000 | accepted 28% (11% with high `s`); each of 9 refusals 5% to 28% | none |
| k1 verifies with `x_R ≥ n` | 1000 | `r` of 1 to 3 20%; recovery finds another key 56%, no point 44% | **`r = p - n - 1` 0.0%** |
| k1 low-s rule | 1000 | low 50%, last low value 6% | **first high value 2.5%** |
| k1 recovers | 1000 | signer's key 34%, another key 46%, `r` or `s` out of range 18% | **no point with this `x` 2.3%; the key at infinity 0%** |
| k1 recovers at the edges | 1000 | recovered 26%, out of range 54%, no point 20%, `r` in `[n, p)` 14% | **the key at infinity 0%** |
| k1 decodes | 1000 | wrong length 43%, wrong prefix 35%, decoded 16.5% | **no point with `x` 1.2%, off the curve 0.6%, `00` 0.3%** |
| k1 group law, r1 group law | 1000 | doubling 21% to 23%, opposite 22% to 24%, infinity 22%, scalar `n` 8% to 10%, above 8% | none |
| k1 ECDH | 1000 | secret 53%, key at infinity 15%, off the curve 16%, zero scalar 16% | none |
| r1 signs, r1 verifies | 1000 | as k1: accepted 29%, each refusal 5% to 26% | none |
| r1 verifies at the edges | 1000 | each range class of `r` and `s` 7% to 14% | **accepted 0.0%** (by design: `r` and `s` are not a signature) |
| r1 decodes | 1000 | decoded 32%, prefix 31%, length 30%, `x ≥ p` 7%, off the curve 9% | **`y ≥ p` 1.0%** |
| bn G1 and G2 group law | 1000, 250 | doubling 16% to 18%, opposite 18% to 20%, scalar `r` 15% to 19%, above 45% to 50% | scalar 1 at 2.4% on `G2` |
| bn pairing check | 50 | one 80%, not one 20%, no pair 8%, a point at infinity 16% to 20% | none |
| bls fields, batch inverse, square root in `Fp2` | 1000 | each branch 9% to 33% | none |
| bls G1 decompression | 1000 | each flag combination 4% to 34%; subgroup 19%, outside 14%, infinity 5%; each refusal 5% to 39% | `x = 0` at 2.5% |
| bls G2 decompression | 1000 | each flag combination 5% to 45%; subgroup 16%, outside 13%; each refusal 6% to 21% | **`y` real 0.0%**, `x` real 1.0% |
| bls G1 and G2 group law | 250 | doubling 17%, opposite 21%, mixed 38%, general 32%, outside the subgroup 35% | none |
| bls multi-scalar multiplication | 250 | 32 windows 17%, 1 window 15% | **no term at all 45.6%**; 2 to 8 windows 6%, 9 to 31 windows 5%, a point twice 4% |
| bls expand_message_xmd | 1000 | one block 31%, cut block 55% | **length 0 2.5%, 8160 1.9%, above 65535 2.2%, empty tag 0.0%** |
| bls hash to G2, map to curve | 50 | `x1` 40% to 54%, `x2` 46% to 60%, sign changed 40% to 56% | **exceptional case 0% on `G2`, isogeny kernel 0%, `y` with `c0 = 0` 0%** |
| bls signs | 50 | -- | **message above 55 bytes 0%, key 1 or `r - 1` 0%** |
| bls verifies | 50 | accepted 16%, pairing 26%, key at infinity 20% | key does not decode 2% |
| bls aggregates | 50 | -- | **no signature 70%; aggregated 30%, of one signature 26%; undecodable 0%, with infinity 2%** |
| bls aggregate verification | 50 | -- | **no signer 74%; accepted 8%, with one signer 6%; a message twice 0%** |
| bls fast aggregate verification | 50 | accepted 16% | **no key 72%; keys that sum to infinity 0%** |
| bls ERC-2334 paths | 1000 | too short 57%, wrong root 26%, bad index 12% | **accepted 1.3%**, index out of range 1.7%, wrong purpose 1.3% |
| kzg commitment | 50 | zero blob 20%, constant 14%, invalid 8% | element `r - 1` 0% |
| kzg proof at a point | 50 | `z` in the domain 40%, outside 42%, `z ≥ r` 18%; accepted 24%, pairing 38%, each error 10% to 14% | `z = 1` 2% |
| kzg proof of a blob | 50 | made 98%, accepted 90% | **refused by the pairing 8%, error 2%, invalid blob 0%** |
| kzg batch verification of blobs | 50 | -- | **no blob 86%, one blob 14%, two or three 0%; never refused** |
| kzg recovery | 20 | recovered 50% (64 cells 40%), three errors 10% to 20% | 65 to 127 cells 5%, 128 cells 5% |
| kzg batch verification of cells | 20 | -- | **no cell 100%: the property never verified a cell** |
| poly cosets, poly of a cell | 250 | -- | cell index 0 or 127 at 2% |
| xmss verifies | 1000 | accepted 11%, bottom not a codeword 27%, top 27%, other root 21%, length 14% | bottom randomizer 0.1%, siblings 2% |
| xmss codewords | 1000 | codeword 32%, sum 105 13%, 107 13%, tail 27% | none that matters |
| xmss one-time signature | 5 | -- | **top layer 0%** (5 cases) |
| vrf verifies | 1000 | accepted 21%, each change 6% to 23% | none |
| sphincs signs and verifies | 20 | bottom not a codeword 100%, middle 55%, top 25% | **the last comparison with the root: 10%, 2 cases; top sibling 5%** |
| G1 accumulator | 250 | every step 9% to 49% | none |
| RFC 6979 nonces | 1000 | second candidate 81%, ten or more 20% | a candidate `≥ n` 0% (it has probability `2^-128`) |
| BLS signers, madhouse | 50 | -- | **a signature made 6%, a second key 4%, an aggregate of several keys 0%, tamper 0%** |
| KZG blob store, madhouse | 20 | a blob stored 35% | **two blobs 5%, a batch of two 0%, a sample 0%, a recovery 0%** |

What the table says:

- Two properties were vacuous or nearly so, and passed: the batch verification of cells (no cell in any case) and the batch verification of blobs (never two blobs, never a refusal).
- So were the two scenarios: most commands were skipped, since no key or blob was there yet.
- The cause is the same in each: a slow property ran 20 or 50 cases, a run starts at size 0, and `Gen.list (.linear 0 5)` at sizes below 20 is the empty list.
- The aggregate verifications had no signer in three cases of four, for the same reason.
- The path parser of ERC-2334 accepted 13 of 1,000 texts.
- No property reached the point at infinity as a recovered key, a `G2` point with a real `y`, the exceptional case of the SWU map on `G2`, or the kernel of an isogeny.

### What changed in the generators

- A length no longer follows the size where a property runs few cases: `Gen.list (.constant 1 6)` with an explicit share of the empty list, in the multi-scalar multiplication, the three aggregate properties, the two batch verifications of KZG and the overrides of a blob.
- The two scenarios run 8 to 20 and 5 to 10 commands at every size, and list the command that makes a key or a blob more than once.
  Their commands give `next`, so a later command is built for the keys, the signatures and the blobs that exist by then (`buildIn`).
- An encoding of a secp256k1 point is drawn by its shape: three valid forms, then one shape per refusal of the decoder.
- Recovery gets a signature made for the point at infinity: `R = k G`, any `s`, and the hash `e = s k`, so that `s R - e G = O`.
- A path of ERC-2334 is valid in a third of the cases, and each of its five refusals has a share.
- The decoder of `G2` gets points whose `y` is real, which the oracle finds by a cube root in `Fp2`, since a random point never has one.
- The map to `G1` gets the two `u` with `Z u^2 = -1`, and the 16 `u` whose point of `E'` is in the kernel of the 11-isogeny, which the oracle finds by the roots of the denominators.
- A multi-scalar multiplication draws the bit length of its largest scalar first, evenly from 1 to 255, so that the count of windows is spread from 1 to 32 and not 32 in most cases.
- A signature of leanXMSS or leanSPHINCS is changed in a field drawn by its kind first: a randomizer, a counter and a sibling are as common as a chain value.
  The first round drew the field of leanXMSS from 149 of 151, so the last two siblings of the top layer were reached only by the change of any bit of the signature.
- The nonce generator of RFC 6979 runs at any order of 256 bits, not only that of secp256k1.

A run of 500 cases or more now requires a minimum share of each class that matters.
The minimums are in `Property/Curves/Minimums.lean`, by the name of the property, at about a third of the share seen.
A property of 20 or 50 cases has lower minimums, each at a count that a binomial of its share misses about once in a thousand runs or less.
The full runs of this round met them all; a minimum that fails on a later seed with no change of the code is set too high, and says nothing of EthLib.

### After: the shares of the last full run

`lake exe curves-property 1000`: 101 properties, all pass, with every minimum met, in 20 minutes.
The table is of a run of the same binary with one process for each group, which takes 5 minutes on 13 cores.
A share moves by a few points from one run to the next.

| Property | Cases | Shares, with the minimum asked where one is |
| --- | --- | --- |
| Montgomery limbs are the integers mod p | 1000 | a is p or more, so it is reduced 18.9%; a is zero mod p 24%; a + b is p or more 23%; a is below b, so the difference borrows 47.1% |
| Montgomery limbs read bytes at an offset | 1000 | refused: exactly p 7.4% (min 1); refused: above p 6.4% (min 2); the buffer ends before the 32 bytes 23.9% (min 8); read: a number below p 86.2% |
| the Euclidean inverse gives the gcd | 1000 | coprime, so an inverse 66.3%; not coprime, so no inverse 33.7%; zero 16%; the modulus is 1 1.6% |
| Jacobian formulas over 7 | 1000 | P = Q, a doubling 31.7%; P = -Q, the point at infinity 33.3%; P is at infinity 10.1%; Q is at infinity 8%; P has order two 13.9%; a = 0 13.5%; the scalar is zero 2% |
| Jacobian formulas over 23 | 1000 | P = Q, a doubling 26.3%; P = -Q, the point at infinity 27.7%; P is at infinity 10%; Q is at infinity 8.5%; P has order two 4.8%; a = 0 4%; the scalar is zero 1.7% |
| Jacobian formulas over 251 | 1000 | P = Q, a doubling 21.5%; P = -Q, the point at infinity 21.5%; P is at infinity 11.7%; Q is at infinity 8.1%; P has order two 0.2%; a = 0 0.5%; the scalar is zero 2.9% |
| k1 signs as RFC 6979 with low s | 1000 | the key is zero, refused 24.5% (min 6); the hash is n or more, so it is reduced 17.4% (min 5); s was above n / 2 and is negated 49.7% (min 15); s was at most n / 2 and is kept 43.4% (min 14); the key is 1 or n - 1 10.2%; the hash is zero mod n 25%; the recovery bit is 1 39.4% |
| k1 verifies as SEC 1 | 1000 | accepted 32.1% (min 9); accepted with s above n / 2 11.7% (min 3); refused: r is n 5.9% (min 1); refused: the equation fails 25.4% (min 8); refused: r is zero 6.4% (min 1); refused: r is above n 5.2% (min 1); refused: s is zero 4.5% (min 1); refused: s is n 5.5% (min 1); refused: the key is off the curve 10% (min 2); refused: the key is at infinity 5% (min 2) |
| k1 verifies a signature with x_R >= n | 1000 | recovery with x = r finds another key 57.1% (min 15); recovery with x = r finds no point 42.9% (min 12); r is 1, 2 or 3 20.5%; r is in the upper half of [1, p - n) 34.5%; s is above n / 2 51.4% |
| k1 low-s rule | 1000 | s is exactly (n - 1) / 2, the last low one 13.2% (min 3); s is exactly (n + 1) / 2, the first high one 12% (min 3); s is at most n / 2 48.5%; s is n or more 15.9% |
| k1 recovers as SEC 1 | 1000 | recovered the signer's key 34.4% (min 10); recovered another key 47.4% (min 12); refused: scalarOutOfRange 16.1% (min 5); changed: nothing 43.5%; the recovery id is the other one 48.9%; the recovery id is 1 50.2%; changed: the key to infinity 5% |
| k1 recovers at the edges | 1000 | r is in [n, p), an x that recovery never tries 9.9% (min 3); refused: scalarOutOfRange 43.8% (min 12); refused: pointAtInfinity 11% (min 3); refused: noPointWithX 13.4% (min 4); recovered a key 31.8% (min 10); r is inside 73.9%; s is the modulus 6.7% |
| k1 decodes SEC 1 encodings only | 1000 | decoded with prefix 3 9.6% (min 3); decoded with prefix 2 9.4% (min 3); decoded with prefix 4 13.5% (min 4); refused: noPointWithX 4.7% (min 1); refused: notOnCurve 8.1% (min 2); refused: pointAtInfinity 7.6% (min 1); refused: coordinateTooLarge 13% (min 3); refused: invalidPrefix 16.4% (min 6); refused: invalidEncodingLength 17.7% (min 6) |
| k1 encodings read back | 1000 | -- |
| k1 group law | 1000 | P + Q with P = Q, a doubling 22.1% (min 7); P + Q with P = -Q, the point at infinity 20.6% (min 7); P + Q with two other points 25.9% (min 7); the wide scalar is n 9.4% (min 2); the wide scalar is above n 9.1% (min 2); P is at infinity 23.5%; Q is at infinity 22.9% |
| k1 ECDH | 1000 | refused: pointAtInfinity, by a zero key 16.4% (min 4); a shared secret 52.4% (min 18); refused: notOnCurve, by the public key 14.9% (min 4); refused: pointAtInfinity, by the public key 16.3% (min 4) |
| k1 address | 1000 | the key is zero, with no address 22.7%; the key is 1 or n - 1 10.3% |
| k1 field kernels | 1000 | a is zero mod p 22.4%; a is p or more 17.6%; a is a square mod p 42.4%; a is not a square mod p 35.2%; the exponent is zero 15.3% |
| k1 operations on bytes, as the bindings call them | 1000 | verify: 1 50.5% (min 12); recover: a key 46.4% (min 10); recover: refused by a recovery id above 1 17.8% (min 4); refused by the length of the hash 14.3% (min 4); refused by the length of the signature 16.3% (min 4); the key is n or more, refused 5.2% (min 1); the key is zero, refused 3.7% (min 1); the key has another length, refused 16.7% (min 4); sign: a signature 63.6% (min 15); ecdh: a secret 70.2% (min 18); verify: 0 16.8% (min 3) |
| r1 signs as RFC 6979 | 1000 | the key is zero, refused 21.1%; the key is 1 or n - 1 9.7%; the hash is n or more, so it is reduced 18.7%; the hash is zero mod n 25.2%; s is above n / 2, and is kept 38.4% |
| r1 verifies as SEC 1 | 1000 | accepted 28.1% (min 9); accepted with s above n / 2 13.9% (min 3); refused: the equation fails 27.6% (min 8); refused: r is zero 4.6% (min 1); refused: r is n 6.1% (min 1); refused: r is above n 5.1% (min 1); refused: s is zero 5.2% (min 1); refused: s is n 5.4% (min 1); refused: the key is off the curve 12% (min 2); refused: the key is at infinity 5.9% (min 2) |
| r1 verifies a signature with x_R >= n | 1000 | s is above n / 2 47.9% (min 10); r is 1, 2 or 3 37.6%; r is in the upper half of [1, p - n) 36.2% |
| r1 verifies at the edges | 1000 | r is inside 68.4%; s is inside 65.7%; accepted 0%; r is the modulus 9.2%; s is zero 15%; s is the modulus 9%; s is above the modulus 10.3% |
| r1 decodes the uncompressed encoding only | 1000 | decoded 30.9% (min 10); refused: x is p or more 7.4% (min 2); refused: y is p or more 6.3% (min 2); refused: off the curve 7.3% (min 2); refused: the prefix is not 04 31.1%; refused: the prefix is 02 or 03, a compressed form 5.6%; refused: another length 23.6% |
| r1 group law | 1000 | P + Q with P = Q, a doubling 24% (min 7); P + Q with P = -Q, the point at infinity 23.1% (min 7); P + Q with two other points 24.1% (min 7); the wide scalar is n 8.9% (min 2); the wide scalar is above n 7.8% (min 2); P is at infinity 22.1%; Q is at infinity 21.2% |
| r1 verification on bytes, as the bindings call it | 1000 | refused by a coordinate of p or more 11.7% (min 2); refused by a length 39.3% (min 10); verify: 1 36% (min 8); verify: 0 13% (min 2); verify: error 51% |
| bn G1 group law | 1000 | P + Q with P = Q, a doubling 17.1% (min 5); P + Q with P = -Q, the point at infinity 16.8% (min 5); the scalar is r 16.5% (min 6); P + Q with two other points 26.9%; P is at infinity 26%; Q is at infinity 30.6%; the scalar is 1 3.2% |
| bn G2 group law | 250 | P + Q with P = Q, a doubling 12.4% (min 3); P + Q with P = -Q, the point at infinity 14.4% (min 5); P + Q with two other points 24.8%; P is at infinity 28.8%; Q is at infinity 43.2%; the scalar is 1 4%; the scalar is r - 1 3.2% |
| bn twist outside the subgroup | 250 | P + Q with P = Q, a doubling 17.6% (min 5); P + Q with P = -Q, the point at infinity 20% (min 5); P + Q with two other points 33.6% (min 8); the scalar is r, and the multiple is not the point at infinity 26.4% (min 5); Q is at infinity 24%; the scalar does not fit the fuel 13.6%; no fuel 5.6% |
| bn pairing value | 50 | -- |
| bn pairing check | 50 | the product is one 82% (min 25); the product is not one 18% (min 2); no pair 12%; one pair 12%; three pairs 38%; a pair with the point at infinity of G1 18%; a pair with the point at infinity of G2 20% |
| bls Fr and Fp are the integers mod r and p | 1000 | Fr: 32 bytes of exactly r, refused 9.4% (min 2); Fr: 32 bytes of a number above r, refused 23.1% (min 6); Fp: 48 bytes of exactly p, refused 9.9% (min 3); Fp: 48 bytes of a number above p, refused 29.1% (min 9); Fr: 32 bytes of a number below r, decoded 67.5%; Fr: zero 24.4%; Fr: a division by zero 23.3% |
| bls batch inverse | 1000 | no element 26.6%; one element 16.8%; a zero among the elements 58.6%; a zero first 32.7%; a zero last 33.8%; only zeros 12% |
| bls square root in Fp2 | 1000 | real, not a square of Fp: the root is imaginary 13.1% (min 4); not real, not a square: refused 12.2% (min 4); not real, a square, the half is a square of Fp 15.8% (min 5); not real, a square, the half is not a square of Fp 24.8% (min 7); real, a square of Fp: the root is real 34.1%; zero 10.7% |
| bls G1 decompression and key validation | 1000 | refused: the compression flag is clear 42.9% (min 12); refused: the infinity flag with another bit set 9% (min 2); refused: x is p or more 3.9% (min 1); refused: no point has this x 9.4% (min 3); decoded: a point of the subgroup 17% (min 6); decoded: a point of the curve outside the subgroup 12.6% (min 3); decoded: the point at infinity 5.2% (min 1) |
| bls G2 decompression | 1000 | decoded: a point of the subgroup 20.2% (min 6); decoded: a point of the twist outside the subgroup 22.4% (min 6); decoded: y is real, so its sign is that of c0 8.3% (min 2); refused: the first half is p or more 5.6% (min 1); refused: the second half is p or more 7.7% (min 3); refused: no point has this x 11.2% (min 4); decoded: the point at infinity 4.1% |
| bls G1 group law | 250 | P + Q with P = Q, a doubling 16.8% (min 5); P + Q with P = -Q, the point at infinity 18.8% (min 5); Q has Z = 1, the mixed formulas 36% (min 10); Q has another Z, the general formulas 38.8% (min 12); P is outside the subgroup 32% (min 10); P is at infinity 24.4%; Q is at infinity 25.2% |
| bls G2 group law | 250 | P + Q with P = Q, a doubling 16.8% (min 4); P + Q with P = -Q, the point at infinity 19.2% (min 7); P is outside the subgroup 40% (min 10); P is at infinity 25.6%; Q is at infinity 26%; P + Q with two other points 28.4%; the scalar is zero 15.2% |
| bls multi-scalar multiplication | 250 | 2 to 8 windows 10.8% (min 4); 9 to 16 windows 10% (min 5); 17 to 31 windows 22% (min 8); 32 windows 20.4% (min 7); a zero scalar among others 36.4% (min 13); a point twice 38.4% (min 12); no term 14% |
| bls pairing check | 250 | the product is one 79.2% (min 25); the product is not one 20.8% (min 5); no pair 7.2%; one pair 16.4%; three pairs 30.8%; a pair with the point at infinity of G1 13.6%; a pair with the point at infinity of G2 13.2% |
| bls expand_message_xmd | 1000 | length 0, no block kept 3.6% (min 1); length of whole blocks, two or more 19.4% (min 6); length 8160, the 255 blocks 3.6% (min 1); refused: 8161 to 65535, too many blocks 7.2% (min 1); refused: above 65535 8.1% (min 3); tag empty 6.9% (min 1); tag of 255 bytes, the longest kept 4.8% (min 1); tag of 256 bytes, the shortest hashed 5.2% (min 1); tag above 256 bytes, hashed 10.2% (min 3) |
| bls hash to G2 | 50 | u0: g(x1) is a square, so x1 48% (min 12); u0: g(x1) is not a square, so x2 52% (min 12); u0: the exceptional case, a zero denominator 0%; u0: the sign of y is changed 38%; u0: the sign of y is kept 62%; u0: y has c0 = 0, so its sign is that of c1 0%; u0: the isogeny has a zero denominator 0% |
| bls map to curve | 50 | G2: the exceptional case, a zero denominator 28% (min 2); G1: the exceptional case, a zero denominator 48% (min 2); G1: g(x1) is a square, so x1 70% (min 10); G1: g(x1) is not a square, so x2 30% (min 10); G1: the isogeny has a zero denominator 18% (min 4); G2: g(x1) is a square, so x1 56%; G2: g(x1) is not a square, so x2 44% |
| bls secret keys | 250 | 32 bytes of a number in [1, r - 1], accepted 39.2% (min 12); refused: zero 10.8% (min 2); refused: exactly r 5.6% (min 1); refused: above r 16.8% (min 4); refused: 31 bytes 10%; refused: 33 bytes 9.2%; refused: no byte 8.4% |
| bls signs | 50 | message above 55 bytes 52% (min 8); message empty 18%; message of 1 to 55 bytes 30%; the key is 1 or r - 1 14% |
| bls verifies | 50 | accepted 26% (min 2); refused: the pairing 16% (min 2); refused: the pairing, with the signature at infinity 18%; refused with a key and a signature that are valid points 16%; the message is another one 14%; proof of possession: accepted 26%; proof of possession: refused 74% |
| bls aggregates | 50 | refused: a signature does not decode 16% (min 2); aggregated 70% (min 25); aggregated with a point at infinity 24% (min 5); refused: no signature 14%; aggregated one signature 12%; aggregated with a point outside the subgroup 10%; the aggregate is the point at infinity 16% |
| bls aggregate verification | 50 | accepted 28% (min 6); refused: the signature changed 46% (min 15); accepted with two signers or more 26% (min 2); accepted with a message twice 18%; accepted with one signer 2%; refused: no signer 8%; refused: fewer messages than keys 24% |
| bls fast aggregate verification | 50 | accepted 24% (min 4); no key, and the signature at infinity: Ethereum accepts, the draft refuses 2%; no key, and another signature: both refuse 2%; refused: a key fails validation 8%; refused: the keys sum to the point at infinity 26%; refused: the signature changed 42%; one key 16% |
| bls key generation | 1000 | refused: fewer than 32 bytes 15% (min 5); exactly 32 bytes 20.3% (min 6); more than 32 bytes 64.7%; key info given 28.8% |
| bls ERC-2333 derivation | 250 | refused: a seed below 32 bytes 20.8% (min 4); two or three indices 48% (min 15); the master key, no index 24.8%; one index 27.2%; an index of 2^31 or more 34%; the index 2^32 - 1 8%; the index 0 24% |
| bls ERC-2334 paths | 1000 | accepted 30.9% (min 9); accepted with exactly four indices 7.3% (min 2); refused: invalidPurpose 7.2% (min 2); refused: tooShort 37.3% (min 10); refused: invalidRoot 15.7% (min 5); refused: invalidIndex 5.3% (min 2); refused: indexOutOfRange 3.6% (min 1) |
| kzg commitment of a blob | 50 | blob: an element above r, refused 14% (min 6); blob: valid 72% (min 20); blob: every element zero 10%; blob: one value in every element 8%; blob: an element of exactly r, refused 20%; blob: an element of r - 1 2%; blob: element 0 or 4095 set apart 40% |
| kzg proof at a point and its verification | 50 | proof: z is a root of unity of the domain 42% (min 10); proof: z is outside the domain 38% (min 6); verify: error invalidProof 6% (min 2); verify: accepted 18% (min 4); verify: refused by the pairing 56% (min 8); verify: error invalidCommitment 10% (min 2); blob: every element zero 12% |
| kzg proof of a blob and its verification | 50 | verify: accepted 88% (min 25); blob: every element zero 6%; blob: one value in every element 12%; blob: an element of exactly r, refused 0%; blob: an element above r, refused 2%; blob: an element of r - 1 0%; blob: element 0 or 4095 set apart 34% |
| kzg batch verification of blobs | 50 | accepted 68% (min 15); accepted with two or three blobs 28% (min 8); refused by the pairing with two or three blobs 6%; refused by the pairing 6%; error invalidFieldElement 4%; error inputLengthMismatch 16%; error invalidCommitment 6% |
| kzg cells and their proofs | 20 | blob: valid 85% (min 15); blob: every element zero 15%; blob: one value in every element 15%; blob: an element of exactly r, refused 10%; blob: an element above r, refused 15%; blob: an element of r - 1 0%; blob: element 0 or 4095 set apart 15% |
| kzg recovery of cells | 20 | recovered 50% (min 10); error notEnoughCells 30%; cells of no polynomial: the proofs agree, and the cells are those of the text 0%; recovered from the even cells or the odd ones 5%; recovered from exactly 64 cells 35%; recovered from 65 to 127 cells 5%; recovered from all 128 cells 10% |
| kzg batch verification of cells | 20 | accepted 65% (min 15); error invalidFieldElement 5%; accepted with no cell 20%; accepted with cells of two blobs 35%; accepted with a commitment twice 35%; accepted with a cell twice 15%; the cell index 0 35% |
| poly sums, products and values | 1000 | the first is longer 35.1%; the second is longer 38.6%; the two have one length 26.3%; the first is empty 26.8%; the second is empty 26.6%; the point is zero 15.6% |
| poly product bound | 50 | the sizes sum to exactly 8192, the last accepted 8%; the sizes sum to 8193, the first refused 8%; accepted 74%; refused 26% |
| poly division | 1000 | divided 81.8%; refused: the divisor ends in zero 18.2%; the divisor is a constant 35.3%; the remainder is zero 57.6% |
| poly interpolation and vanishing polynomial | 1000 | no point 30.3%; one point 21%; several points 48.7%; the point zero among them 21.3% |
| poly bit reversal, roots of unity and cosets | 250 | the cell index 0 or 127 18.8%; refused: a cell index of 128 or more 14% |
| poly FFT | 1000 | -- |
| poly evaluation form | 100 | the point is in the domain, so the value is an entry 51%; the point is outside the domain, the barycentric formula 41%; the point is zero 7%; refused: not 4096 values 16%; the polynomial is zero 51% |
| poly of a cell | 250 | refused: 63 values 9.2%; refused: 65 values 10.4%; the cell index 0 or 127 20.8% |
| poly packed indices | 1000 | decoded 21%; decoded: no index 4.6%; refused: a ragged buffer 79%; an index of 2^63 or more 42.3% |
| xmss verifies valid signatures only | 1000 | accepted 10.2% (min 3); refused: a wrong length 13.8% (min 4); refused: the bottom digest is not a codeword 33.5% (min 8); refused: the top digest is not a codeword 22% (min 7); refused: the path ends at another root 20.5% (min 6); changed: the length of the message 4.1%; changed: the leaf index 9.3% |
| xmss codewords | 1000 | a codeword 32.8% (min 10); refused: the sum is 105 16.8% (min 4); refused: the sum is 107 14.8% (min 4); refused: the sum is 106 and a last digit is not zero 23.4% (min 7); refused: another sum 12.2%; refused: only digit 63 is not zero, at sum 106 1.8% |
| xmss path to the root | 1000 | the bottom layer 49.5% (min 15); the top layer 50.5% (min 15); a key index below 2^16 47.2% (min 14); a key index of 2^16 or more, past the 16 levels 52.8% (min 14); the key index 2^32 - 1 6.8%; the key index 0, a left child at every level 20%; the key index 65535, a right child at every level 13.3% |
| xmss leaf of a one-time signature | 50 | a leaf, from a codeword 46% (min 15); refused: the digest is not a codeword 54% (min 10); a message of 32 bytes 68%; a message of 16 bytes, a root 32%; the top layer 50%; a chain starts at digit 0 46%; a chain starts at digit 1 46% |
| xmss public parameter and subtrees | 50 | the top layer 46%; the last node of its level 28% |
| xmss one-time signature | 5 | the top layer 80%; a message of 16 bytes, a root 60% |
| vrf verifies valid openings only | 1000 | accepted 20.5% (min 6); refused 79.5% (min 25); changed: nothing 20.5%; accepted after a change 0%; the index 0, a left child at every level 10.5%; the index 2^32 - 1, a right child at every level 4%; an index of 2^31 or more, the last level 40.5% |
| vrf secret, output and mix | 1000 | the index 0 17.4%; the index 2^32 - 1 4.8%; an index of 2^24 or more, four bytes 65.7% |
| sphincs signs, verifies and refuses changes | 20 | refused: the top digest is not a codeword 55% (min 10); refused: the bottom digest is not a codeword 100% (min 25); refused: the path ends at another root 55% (min 20); refused: the middle digest is not a codeword 60% (min 8); accepted 100%; changed: a length 85%; refused: a wrong length 85% |
| sphincs digest fields | 1000 | every bit clear 17.3%; every bit set 19.2%; byte 30 has a bit above the 18 of the tree 81.9% |
| G1 accumulator against a scalar (StateMachine) | 250 | add: the accumulator itself, a doubling 13.6% (min 4); add: its opposite, the point at infinity 16.4% (min 4); add a Jacobian form: the accumulator itself, a doubling 15.2% (min 3); a step from the point at infinity 72.4%; double 48.4%; multiply by zero 22%; multiply by one 6.8% |
| RFC 6979 nonce generator (StateMachine) | 1000 | a second candidate or a later one, after a rejection 80.3% (min 25); the hash is the order or more, so it is reduced 22.4% (min 4); another order of 256 bits 53% (min 8); ten candidates or more 19.6%; a candidate of the order or more, which a signer rejects 33%; the order of secp256k1 23.3%; the order of P-256 23.7% |
| BLS signers (Command, madhouse) | 50 | a signature is made 78% (min 20); a second key or a later one is registered 80% (min 20); one message: the aggregate of several keys verifies 32% (min 10); one message: the keys sum to infinity, refused 14% (min 2); several messages: an aggregate of two or more 30% (min 2); tamper refused: the pairing 32% (min 4); the empty set 74% |
| BLS signers (Command, deterministic) | 1 | a second key or a later one is registered 100%; a signature is made 100%; a message is signed a second time 100%; the opposite of a key is registered 100%; tampered: a bit of the key 100%; tamper refused: the key is outside the subgroup 100%; one message: the aggregate of one key verifies 0% |
| KZG blob store (Command, madhouse) | 20 | a blob is stored 95% (min 30); a second blob or a third is stored 70% (min 25); sample: cells verify 45% (min 5); a blob is stored twice 35%; a constant blob is stored, whose proof is the point at infinity 25%; batch: no blob 30%; batch: one blob verifies 45% |
| KZG blob store (Command, deterministic) | 1 | a blob is stored 100%; a second blob or a third is stored 100%; a blob is stored twice 100%; a constant blob is stored, whose proof is the point at infinity 0%; batch: no blob 0%; batch: one blob verifies 100%; batch: two or three blobs verify 100% |
| every: the two tags of the proof-of-possession scheme | 1 | -- |
| every: core BLS operations under any tag | 50 | verified under its own tag 20% (min 15); refused under another tag 40% (min 4); an aggregate verified under its own tag 60% (min 20); the tag of the message scheme of Ethereum 10%; the tag of another scheme of the draft 28%; no tag 12%; a tag of 255 bytes, the longest kept 10% |
| every: a signature is no proof of possession | 20 | -- |
| every: any count of field elements | 250 | 63 to 65 elements 34.8%; refused: more than 255 blocks 22.4%; 2 elements 9.6%; 5 elements 10.4%; 4 elements 10.8%; 1 elements 10.8%; 3 elements 10.4% |
| every: the sign of a coordinate | 1000 | Fp2: the imaginary part is zero, so the real part decides 39% (min 12); Fp2: the imaginary part decides 61% (min 20); a real part of (p - 1) / 2, the last smaller one 6.3% (min 1); a real part of (p + 1) / 2, the first larger one 4.1% (min 1); sgn0: the real part is zero, so the imaginary part decides 5.8% (min 2); zero 2.2% |
| every: powers in any modulus | 1000 | the exponent does not fit the fuel 38.5% (min 5); the modulus is 1 1.5%; the modulus is even 48.5%; no fuel, so the power is one 3.4%; the exponent is zero 3.2%; the base is zero mod the modulus 5.9% |
| every: the cofactor of G2 is h_eff | 50 | a point outside the subgroup 30% (min 8); a point of the subgroup 38% (min 8); the point at infinity 32% |
| every: a child key of any parent | 250 | the parent has a leading zero byte 58.4% (min 18); the parent is one byte 18% (min 4); the parent is r - 1 6%; the index 0 26.8%; the index 2^32 - 1 7.6%; an index of 2^24 or more, four bytes 49.6% |
| every: all 128 cells of a blob | 4 | a proof of a neighbour is refused 75%; a proof of a neighbour is the same proof 25%; 128 cells verified 100% |
| every: the coset of every cell index | 1 | -- |
| every: the evaluation form over any domain | 1000 | the point is in the domain 57.1% (min 18); the point is outside the domain 42.9% (min 13); the point is the last of the domain 5.8% |
| every: the FFT of any length | 250 | a length that is no power of two 85.6% |
| every: the FFT in G1 | 50 | a point at infinity among them 74% |
| every: addresses of leanXMSS | 1000 | a type that the scheme uses 72.6%; another type 27.4%; a chain position above zero 86.3%; the third field has bit 23, the layer bit 36.5%; the last field is 2^32 - 1 7.2% |
| every: paths of a small subtree of leanXMSS | 50 | the top layer 40%; the last subtree of its level 34% |
| every: codewords of leanSPHINCS | 1000 | a codeword 40.3% (min 12); refused: the sum is 127 19.6% (min 6); refused: the sum is 129 19.4% (min 4); refused: another sum 20.7%; every digit zero, or every digit three 10.9% |
| every: addresses of leanSPHINCS | 1000 | the tree has more than 32 bits 61.3%; the tree is 2^64 or more, so it is reduced 17.8%; a word of 2^32 or more, so it is reduced 78%; an index of 2^26 or more, past the hypertree 16.8% |

Classes that stay at 0%, and why:

- `bls hash to G2`: the exceptional case of the SWU map, a `y` with `c0 = 0` and the kernel of the isogeny cannot be reached through a hash; the map to curve reaches the first, the sign function is tested by itself, and the third is unreachable (see below).
- `r1 verifies at the edges`: no case is accepted, since `r` and `s` are numbers at the edges and not a signature; `r1 verifies as SEC 1` accepts 30%.
- `vrf verifies`: no changed opening is accepted, which is the claim.
- A candidate nonce of the order or more is common in the state machine (30%), where the order is any; in `sign` it has probability `2^-128`.

### The every-parameter rule: what was added

Each row is a general function that the first round tested at the values in use only.
All pass.

| Property | EthLib definitions | Parameters varied | Reference | Cases |
| --- | --- | --- | --- | --- |
| every: the two tags of the scheme | `Signatures.DST`, `POP_DST` | -- | py_ecc `G2ProofOfPossession` | 1 |
| every: core BLS operations under any tag | `coreSign`, `coreVerify`, `coreAggregateVerify`, `aggregate` | the tag: the four of the draft (`NUL`, `AUG`, `POP`, the proof tag), none, 1 to 40 bytes, 255, 256 and 300 bytes; another tag, message or key at verification | py_ecc `_CoreSign`, `_CoreVerify`, `_CoreAggregateVerify`; the hash to `G2` under any tag by py_ecc's maps | 50 |
| every: a signature is no proof of possession | `sign`, `verify`, `popProve`, `popVerify` | the key | the claim: each verifies under its own tag only | 20 |
| every: any count of field elements | `HashToCurve.hashToFieldFp2`, `fpFromBytesL` | a count of 0 to 5, and 63, 64 and 65 at the limit of 255 blocks; any tag | the bytes of the expansion read on `Nat` | 250 |
| every: the sign of a coordinate | `Fp.signBit`, `Fp2.signBit`, `HashToCurve.sgn0Fp`, `sgn0Fp2` | both halves of the field at their edges, an imaginary part of zero, a real part of zero | the Zcash encoding; RFC 9380 section 4.1, on `Nat` | 1000 |
| every: powers in any modulus | `Secp256k1.Fin.powBits` | any modulus from 1 to `2^300`, any fuel from 0 to 300, an exponent past the fuel | `Nat` | 1000 |
| every: the cofactor of G2 is h_eff | `HashToCurve.clearCofactor`, `H_EFF_G2`, `psi`, `psi2`, `mulNegX` | any point of the twist, also outside the subgroup | py_ecc `multiply` by the number of RFC 9380 section 8.8.2 | 50 |
| every: a child key of any parent | `KeyDerivation.deriveChildSk`, `parentSkToLamportPk`, `ikmToLamportSk` | the parent key: 1, 255, 256, `2^248 - 1`, `2^248`, `r - 1`, any; the index at the edges of 32 bits | model of ERC-2333 | 250 |
| every: all 128 cells of a blob | `computeCellsAndKzgProofs`, `verifyCellKzgProofBatch`, `recoverCellsAndKzgProofs` | every cell index from 0 to 127, in 8 batches of 16; a proof of the next cell at one place; recovery from 64 cells in a row, from 63 and from 129 | c-kzg-4844 | 4 blobs |
| every: the coset of every cell index | `cosetForCell` | every index from 0 to 127; 128, 129, 255, 256, 8191, 8192, `2^32`, `2^64` refused | powers of 7 on `Nat` | 1 |
| every: the evaluation form over any domain | `evaluatePolynomialInEvaluationFormAux`, `rootsOfUnityBrp`, `Fr.batchInverse` | a domain of 1 to 128 points; a point in it, the last of it, outside it | Horner's rule on `Nat` | 1000 |
| every: the FFT of any length | `fftField`, `fftFieldIter`, `cosetFftField`, `shiftVals` | 1 to 128 values; a length that is no power of two; roots of another length | the sum it stands for; the docstring for the other shapes | 250 |
| every: the FFT in G1 | `fftG1`, `fftG1Vector` | 1, 2, 4 and 8 points, the point at infinity among them; 3 points | py_ecc, by the scalars | 50 |
| every: addresses of leanXMSS | `encodeAddress`, `layerHi`, `AddressType.code` | every type from 0 to 31, every position from 0 to 7, both other fields at their edges, both layers | model | 1000 |
| every: paths of a small subtree of leanXMSS | `Xmss.build`, `Merkle.Built.path`, `Merkle.path`, `Merkle.climb`, `nodeHash`, `leaves` | levels 0 to 4, both layers, the first subtrees and the last, every leaf below | the model's node; the two paths against each other and against the climb | 50 |
| every: codewords of leanSPHINCS | `Sphincs.codeword?`, `Internal.digits`, `digitSum` | sums 127, 128 and 129, any sum, all zeros and all threes | model of FIPS 205 Algorithm 4 | 1000 |
| every: addresses of leanSPHINCS | `Sphincs.adrs`, `encodeAdrs`, `OtsKey.ofIndex`, `adrsFors`, `adrsNode`, `AdrsType.code` | each of the 8 types and 3 layers; a tree up to `2^64 + 1`; words up to `2^33`; an index up to `2^40` | model | 1000 |
| bn twist outside the subgroup | `AltBn128.Point2.add`, `mulBits`, `isOnCurve` | points of the twist outside `G_2`; equal, opposite, at infinity; a fuel of 0, 1, 8, 255, 256 and 257 | py_ecc | 250 |
| r1 verifies a signature with `x_R >= n` | `Secp256r1.verify`, the comparison of `x_R mod n` with `r` | a crafted `R` whose `x` is in `[n, p)`, which has probability `2^-128` from a signer; then `r + n` in place of `r` | model of SEC 1; OpenSSL | 1000 |
| k1 operations on bytes, as the bindings call them | `Secp256k1.Exports.verifyExport`, `isLowSExport`, `recoverExport`, `signExport`, `ecdhExport`, `addressExport`, `readHash`, `readPrivateKey`, `readSignature` | a hash, a signature and a key one byte short, one long and empty; a recovery id of 2, 3, 27, 28 and 255; a key of 0 and of `n` or more; every encoding of a public key | coincurve, eth-keys and the model, with the lengths checked in the property | 1000 |
| r1 verification on bytes, as the bindings call it | `Secp256r1.Exports.verifyExport`, `readPublicKey`, `readCoordinate`, `readHash`, `readSignature` | the same lengths; a coordinate of `p` and of `p + 1` | OpenSSL and the model | 1000 |
| RFC 6979 nonce generator, extended | `Rfc6979.nonceSeed`, `nonceNext`, `nonceReject` | the order: secp256k1, P-256, `2^255`, `2^256 - 1`, any of 256 bits | model of RFC 6979 | 1000 sequences |
| bls map to curve, extended | `mapToG1`, `simpleSwuG1`, `isoMapG1`, `mapToG2`, `simpleSwu` | `u = 0`, `Z u^2 = -1`, the kernel of the 11-isogeny | py_ecc; arkworks outside the kernel | 50 |
| bls G2 decompression, extended | `G2.uncompress`, `compress`, `Fp2.signBit` | a real `y`, with either sign flag | py_ecc; arkworks | 1000 |
| bls multi-scalar multiplication, extended | `G1.msm`, `msmMaxBits`, `msmDigits`, `msmBuckets`, `msmRunning`, `msmCombine` | the count of windows, by a largest scalar of 0 to 255 bits; a point twice; a point and its opposite | py_ecc, term by term | 250 |
| kzg recovery, extended | `recoverCellsAndKzgProofs` | the even cells, the odd ones, each half, 63 and 129 cells among the drawn shapes | c-kzg-4844 | 20 |

The new properties were checked for sensitivity by breaking a reference in four places.
A model of leanSPHINCS that takes the sum 129 for a codeword failed, shrunk to the digest `ff...fc00...00` in 107 shrinks.
A child key derived from a parent without its leading zero bytes failed, shrunk to the parent 1 and the index 0 in 3 shrinks.
A verification that takes any signature under a tag of 43 bytes failed, shrunk to the key 1 and the empty message in 4 shrinks.
An address of leanXMSS with its third field in big-endian bytes failed, shrunk to the fields `(1, 0)` in 29 shrinks.
Each reference was then restored and compared with its copy.

### Findings of the third round

No property found a place where EthLib deviates from its source.
Two references disagreed with EthLib, each once, and each time the text decides for EthLib.

#### 3. HARNESS (reference quirk): py_arkworks answers `(0, 0)` in the kernel of the 11-isogeny

- Definition: `MapToCurve.isoMapG1`, `EthLib/Cryptography/Bls/MapToCurve.lean:206`, and `mapToG1` at line 221.
- Shrunk counterexample: `u = 3140998864168905305116999238341094082253376923310959579796412851201896533814081908310962784672298826054629918684568`, one of 16 such `u`.
  Its point of `E'` has an abscissa that is a root of both denominators of the isogeny.
- EthLib: the identity point.
- py_ecc 8.0.0: the identity point.
- py_arkworks_bls12381 0.5.0, `G1Point.map_from_fp_be`: a point whose coordinates read `(0, 0)`, that is not equal to its identity and is not in the subgroup.
- The source decides for EthLib: RFC 9380 section 6.6.3, "Exceptional cases of iso_map are inputs that cause the denominator of either rational function to evaluate to zero; such cases MUST return the identity point on E."
- The encoding of EIP-2537 writes the identity as zeros, so a precompile built on either answer returns the same bytes; the difference is in the binding's value, not in an output of Ethereum.
- The oracle now takes py_ecc's answer where py_ecc gives the identity, and requires arkworks to give the identity or `(0, 0)` there.
- Reproduction:

```lean
import EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls

-- A `u` whose point of `E'` is in the kernel of the 11-isogeny: the map gives the identity.
#eval (MapToCurve.mapToG1 (F := Fp) (Fp.ofNat
  3140998864168905305116999238341094082253376923310959579796412851201896533814081908310962784672298826054629918684568)).toOption.map
    (·.isInfinity)
```

- It prints `some true`.
- Command: `HEDGEHOG_ONLY="bls map to curve" lake exe curves-property 1000`, where "G1: the isogeny has a zero denominator" is 12% to 26% of the 50 cases.

#### 4. HARNESS (reference quirk, and a correction of finding 1): c-kzg answers the values it recovered

- Definition: `recoverCellsAndKzgProofs`, `EthLib/Cryptography/Kzg/Recovery.lean:138`, and `recoverPolynomialcoeff` at line 61.
- Counterexample, after 26 shrinks: the zero blob, 65 of its cells (the indices 1, 2, 4, 5, 6, 8 and 59 more, in order), and element 0 of the first of them replaced by 1.
  So the 65 cells are the values of no polynomial of degree below 4096.
- EthLib: cells with SHA-256 `298514bc...`, proofs with SHA-256 `1a435c00...`.
- c-kzg-4844 2.1.8: cells with SHA-256 `09a27b4d...`, and the same proofs.
- The source decides for EthLib.
  `specs/fulu/polynomial-commitments-sampling.md` of consensus-specs ends `recover_polynomialcoeff` with "`return PolynomialCoeff(reconstructed_poly_coeff[:FIELD_ELEMENTS_PER_BLOB])`", and `recover_cells_and_kzg_proofs` with "`# Recompute all cells/proofs`" and "`return compute_cells_and_kzg_proofs_polynomialcoeff(polynomial_coeff)`".
  I read these lines in the releases v1.5.0, v1.6.0 and v1.7.0-alpha.12, and at the revision that EIP-7594 links.
  So the cells of the text are the values of the polynomial cut to 4096 coefficients; c-kzg answers the 8192 values it recovered, and makes its proofs from the cut polynomial.
- Evidence that EthLib's cells are those of the text, with no trust in EthLib: c-kzg, given the 64 odd cells of EthLib's answer, recovers EthLib's 128 cells and 128 proofs.
  64 cells are always the values of one polynomial, so c-kzg has no choice there.
- The first round met this with all 128 cells, where c-kzg's answer is a copy of its input, and took it for a rule of 128 cells.
  Its exemption let the case of 65 to 127 cells fail: about one run in five of the 20 cases drew it, and it showed in the fifth full run of this round.
- The inputs concerned are the cells of no blob, so a caller that verified its cells never meets one, and no vector holds one.
- The property now requires the proofs to agree, and EthLib's cells to come back from c-kzg as above; it is the stronger test, and it runs wherever the two answers differ (the class "cells of no polynomial").
- This touches the question that `EthLib/Cryptography/Kzg/README.md` leaves open under "The normative text".
  From v1.7.0-beta.4 on, consensus-specs has no text of this function, and its Python package calls c-kzg for it.
  Under the readings 1 and 3 of that page EthLib is right; were the library that consensus-specs runs the reference, the two would differ on these inputs.
- Command: `HEDGEHOG_ONLY="kzg recovery of cells" lake exe curves-property 1000 kzg`; the class "cells of no polynomial" is now drawn in one run of two or three.

#### Observations that are not deviations

- At the revision of consensus-specs that EIP-7594 links, and in v1.5.0, `recover_cells_and_kzg_proofs` takes cell indices in any order, without duplicates.
  From v1.6.0 on the text requires ascending order ("`assert cell_indices == sorted(cell_indices)`"), as EthLib (`indicesNotAscending`) and c-kzg do.
  `EthLib/Cryptography/Kzg/README.md` names one rule on which its three readings of the normative text differ, the byte order of a field element; the order of the indices is a second one, under its first reading.

- The branch of `isoMapG2` for a zero denominator cannot be reached from the SWU map.
  The two denominators of the 3-isogeny have one root in `Fp2`, and `g` of that root is not a square, so no point of `E'` over `Fp2` has that abscissa.
  The oracle computes this (`swuroot g2` answers `none`); it is a computation of this round, not a statement of RFC 9380.
- `KeyPath.parsePath` accepts an index with leading zeros, such as `m/012381/3600/0/0`, and `Path.toString` writes it back without them.
  ERC-2334 gives no grammar of an index, so this is a choice and not a deviation; 7% of the generated paths have such an index, and the model accepts them too.
- `aggregateVerify` accepts an aggregate of one message under keys that sum to the point at infinity, as py_ecc and milagro do, and `fastAggregateVerify` refuses it.
  The draft leaves this to the proofs of possession.

### Not covered, after the third round

- leanXMSS `keyGen`, `sign` and `path` at their real height, and the VRF's `keyGen`, `prove` and `root`: `2^16` and `2^32` leaves.
  The parts run at heights 0 to 6 against the model, and the paths of a subtree of up to 16 leaves against the climb.
- leanSPHINCS signing has still no reference of its own: FORS, the PRF and the hypertree are compared through the model of verification, the address encoding and the repository's vectors.
- `Ecdsa.signWith` beyond its first candidate: a rejected nonce, `unrecoverableNonce` (`x_R ≥ n`) and `noNonce` have probability `2^-128`; only the generator's rejection step is tested, by itself.
- `keyGenLoop` beyond its first salt, for the same reason.
- The opening of a blob at each of the 4096 points of the domain: the points are drawn, with `1` and `r - 1` named.
- Every cell is verified for 4 blobs a run, and a recovery from all 128 cells is a few of 20 cases.
- The three properties `Jacobian formulas over 7, 23, 251` of this driver keep their first-round generators, with a point of order two and `a = 0` under 1% over 251; the kernels driver tests the same definitions on any curve, with minimums.
- A sibling of leanXMSS and of leanSPHINCS is labelled by its layer and not by its level; the VRF's siblings are labelled in four groups of eight levels.
- The exports of BLS, KZG, leanXMSS, leanSPHINCS, the VRF and the key derivations (`Cryptography/Exports`): only those of secp256k1 and P-256 are tested, on bytes.
- `G1.msm` under a constrained thread pool, and constant time.
- The minimums are not asked of a run below 500 cases, and a property of 5 cases (`xmss one-time signature`) has none.

### Notes on lean-hedgehog 0.3.0

Coverage:

- `classify` and `label` were the piece that mattered: one labelled run showed two vacuous properties and two scenarios that skipped most of their commands, all green since the first round.
- A label with a computed name is cheap: `label s!"refused: {ctorName e}"` on the constructor of an error gave every refusal of a decoder its own row with no list to maintain.
- The report lists labels in the order they were first seen, so the rows of two runs do not line up and families of labels interleave.
  A sorted report, or a grouped one (`classify` under a named dimension), would read better; I gave the names prefixes.
- `cover` asks its minimum of every run, and a short run cannot meet it.
  Both this driver and the kernels driver wrote the same wrapper, `withMinimums cases minimums property`, which adds `cover n name false` after the test when the run has 500 cases or more.
  A `Property.withMinimums`, or a minimum that is asked only from a number of tests on, belongs in the library.
- A minimum for a name that no case has fails at 0%, which catches a misspelt name; a minimum for a property that does not exist is silent, so the driver checks the names itself.
- The root cause of the vacuous properties is the size: a property of 20 tests sees sizes 0 to 19 only, where `Range.linear 0 5` is 0.
  USAGE says so under COVERAGE, and the trap is still easy to fall in for a slow property.
  A run of `n < 100` tests that spreads its sizes over 0 to 99 would have avoided every one of these.

Commands:

- The context in `check`, `apply` and `next` removed the `oracle` or `env` field from all twelve commands, and `build _` is now the usual case.
- `next` and `buildIn` work as documented: a `SIGN` is built for a key that exists by then, a `TAMPER` for a signature made, a `SAMPLE` for the blobs stored.
- `next` is applied to a command whether or not its `check` holds, so each `next` here repeats the condition of its `check` by hand (`if ... then push else s`).
  The library could thread `if check then next else same`; a `next` that forgets the condition builds later commands for a state that never exists, in silence.
- `next` cannot know what `apply` computes: the state it builds holds a placeholder for a signature and for the cells of a blob.
  That is fine while `buildIn` reads only the counts, and the docstring could say so.
- `scenario mode ctx commands (.constant 8 20)` fixed the short sequences.
  A count of the commands that `check` skipped, in the report, would have shown the problem without labels.
- `StateMachine.applySut` with the state before the transition made the classes of the accumulator direct: whether the point added is the accumulator itself or its opposite is a fact of the state before.

Selection:

- `Selection.fromEnv` worked at once, next to the driver's own filter of groups by a word.
- The failure report prints `recheck 12 ⟨2219235471092472968, 16393493468854217317⟩ <property>`, the Lean form.
  A second line in the form of the environment, `HEDGEHOG_RECHECK="12 2219235471092472968 16393493468854217317"`, could be pasted as it is.
- `mustFail` was not needed: no property of this driver fails by design.

Shrinking and reports:

- The disagreement with arkworks shrank from a random pair to `(u, 0)` in 2 shrinks, with `u` an element of a list: `Gen.element` shrinks to the first element, which here is the readable answer.
- A group prints nothing until the process ends when its output is a file: the reports are not flushed.
  A run of 30 minutes shows an empty file; a flush after each property would help a long campaign.
- The one real failure of this round was in a property whose case takes seconds.
  It shrank 26 times in 13 minutes, with nothing printed meanwhile, and the limit of 1,000 shrinks would have allowed hours.
  The driver now sets `withShrinks 40` on its slow properties; a limit in time, and a line when shrinking starts, would be the natural interface.
- The counterexample of that failure was good after 26 shrinks: the zero blob, no change of the count, and the element replaced by 1.
  The list of 65 indices did not shrink to 65 in a row, since another list of indices is another recovery of several seconds.

Bugs in the library: none met.

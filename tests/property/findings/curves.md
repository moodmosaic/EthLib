# Public-key cryptography: what the property tests found

The driver is `Property/Curves.lean`, with its modules under `Property/Curves/`.
The oracle is `oracle/curves.py`, with `curves_model.py`, `curves_bls.py`, `curves_kzg.py` and `curves_xmss.py`.
`oracle/requirements-curves.txt` lists the references and their versions.

```bash
cd tests/property
lake exe curves-property 1000            # Every group.
lake exe curves-property 1000 kzg        # Only the groups whose name contains `kzg`.
```

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
- The quoted lines were read from consensus-specs at commit `9d377fd5`, the one EIP-7594 pins; the specification itself was not run, so "EthLib follows the text" rests on reading `Recovery.lean` against it.

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
- The value of the BLS12-381 pairing in `Fp12` was not compared (the two towers differ in representation); only `pairingCheck`, through arkworks, and every verification built on it.
- `G1.msm` runs its windows as tasks; nothing here tests it under a constrained thread pool.
- `Bls.Fp6`, `Fp12` and `Bls.Pairing.millerLoop` are reached only through the pairing check.
- The precompile-shaped wrappers (`Execution/Evm/Precompiles`: padding of short input, the 192-byte pairs, P256VERIFY) belong to the EVM layer and its driver.
- `Cryptography/Exports` and the proofs were out of scope.
- Constant time: none of this measures time.
- `computeChallenge`, `computeVerifyKzgProofBatchChallenge` and `computeVerifyCellKzgProofBatchChallenge` are reached only through the proofs and verifications that use them.
- `hashToG2` with an empty tag is compared with the model of `expand_message_xmd` only through `expand`, since py_ecc is not asked for an empty tag.

## Notes on lean-hedgehog

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

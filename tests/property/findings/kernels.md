# The fundamental primitives at every parameter: what the property tests found

The driver is `Property/Kernels.lean`, with its modules under `Property/Kernels/`.
The references are in `oracle/kernels.py` and `oracle/kernels_*.py`, and `oracle/requirements-kernels.txt` lists what they import.

```bash
cd tests/property
lake exe kernels-property 1000                       # Every group, about 7 minutes.
HEDGEHOG_ONLY=montgomery lake exe kernels-property 1000
HEDGEHOG_ONLY=finding lake exe kernels-property      # The finding, with its counterexample.
ETHLIB_UCD=$PWD/UnicodeData.txt HEDGEHOG_ONLY=unicode lake exe kernels-property
```

The rule of this round is that a general function runs at every value of its parameters.
So the modulus of the Montgomery arithmetic, the limb count, the rate of the sponge, the generator of a CRC, the coefficient `a` of a curve, the parameter of a Miller loop and the width of a byte field are all generated.

## Result

One finding, a BUG in data: `ChainConfig.hoodi` activates Glamsterdam at a time that both of its sources have withdrawn.
No other property found a place where EthLib deviates from its source.
Every arithmetic kernel, every constant table and every hash internal of this area agrees with its reference on the inputs generated.
That is a negative result on those inputs, not a proof: see Not covered.

65 properties: 61 pass, 2 state the finding and fail by design, 2 pin a condition that a docstring states and fail by design.

## What was tested

Cases are those of the last full run, `lake exe kernels-property 1000`, which took 7 minutes.
Shares are those of a full run at 1,000 cases; they move by a few points from one run to the next.
A share is the part of the test cases that a label counts; for a state machine a test case is a sequence, so a share counts the sequences in which the branch ran at least once.
"min" is a minimum that the property requires with `cover`, set at about a third of the share seen.
Every row passed.

### Montgomery arithmetic (`Cryptography/Montgomery.lean`, `Montgomery/Fin.lean`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| machine: any modulus of 8 limbs | `Montgomery.ofNat`, `toNat`, `mul`, `add`, `sub`, `neg`, `inv`, `pow`, `powLimbs`, `toBytesBE`, `ofBytesBE`, `ofFin`, `toFin`, `Limbs.ofNat`, `Limbs.val`, `Modulus` | any odd modulus below `2^256`: nine named ones, just below `R`, either side of `R / 2`, tiny, limb patterns, any; operands by integer and by Montgomery form | `Nat` | 1000 sequences of 1 to 50 | `2 p > R` 49%; mul: final subtraction fired 46% (min 15), did not fire 69% (min 20), a word above the limbs 22% (min 5); add: sum of forms `≥ p` 46% (min 15), exactly `p` 7% (min 2), `≥ R` 12%; sub: borrows 61% (min 20), equal forms 23%; inv of zero 6%, of an element with no inverse 11% |
| machine: any modulus of 12 limbs | the same | any odd modulus below `2^384` | `Nat` | 1000 sequences | fired 48%, a word above 22%, sum `≥ p` 46%, exactly `p` 8%, borrows 62% |
| machine: the field of secp256k1 | the same at `Secp256k1.Fp.params` | operands | `Nat` | 1000 sequences | fired 60%, a word above 63%, sum `≥ R` 39% |
| machine: `Fr` of BLS12-381 | the same at `Bls.Fr.params` | operands | `Nat` | 1000 sequences | fired 57%, sum `≥ p` 45%, borrows 61% |
| machine: `Fp` of BLS12-381 | the same at `Bls.Fp.params`, whose product is `mulHigh` after `mulLow` | operands | `Nat` | 1000 sequences | fired 57% (4.6% before the generator was fixed, see Findings), sum `≥ p` 46% |
| bytes: any modulus of 8 and of 12 limbs | `Montgomery.ofBytesBE`, `wordBE`, `limbBE`, `ltWords` | modulus, offset, a buffer that ends early | `Nat` | 2 x 1000 | below `p` 55%, exactly `p` 23%, above 22%, ends early 32% |
| words: the product on 1 to 16 limbs | `Montgomery.mulWords`, `step`, `reduce`, `Words`, `num` | the limb count from 1 to 16, the modulus, `b ≥ p` | `Nat` | 1000 | fired 27% (min 5), a word above 8%, each count 4% to 9% |
| split: 8 and 12 limbs at every row | `Montgomery.mulLow`, `mulHigh`, `mulRows` | the row of the split from 0 to `n`, the modulus | `Nat` | 2 x 1000 | `2 p ≤ R` 51% (min 15), fired 30%; above `R / 2` the parts gave the product in 42% and another number in 6% |

The shares of a branch in the model come from a simulation of the rows on `Nat` (`Mont.ciosBranches`), not from EthLib.

### Forks and chain configurations (`Base/Fork.lean`, `Base/ChainConfig.lean`, `Execution/Fees/BlobBaseFee.lean`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| fork order and comparison | `Fork`, `<`, `≤`, `compare`, `==`, `Fork.name` | every pair of the 29 forks | the list of names in the oracle, from EIP-7568 and the meta EIPs | 1000 | `a < b` 49%, `a = b` 4% |
| fork names read back | `Fork.ofName?` | names, other cases, names of one layer | the list | 1000 | the text is a name 28% |
| active fork: mainnet | `ChainConfig.mainnet`, `activeFork`, `Activation.reached` | block number and timestamp on, one before and one after each activation | a table from EIP-6953, EIP-7600, EIP-7607 | 1000 | on an activation or one before 69% (min 25), a time fork active 66% (min 20), timestamp past a fork the number is not 59% |
| active fork: hoodi, before 1793036568 | `ChainConfig.hoodi` | the same, timestamps below the Glamsterdam time | the genesis file, EIP-7600, EIP-7607 | 1000 | on an activation or one before 74% |
| network constants | `mainnet`, `hoodi`: chain ID, deposit contract, every activation, `Ordered`, `activationsOrdered` | -- | the tables | 2 x 1 | -- |
| active fork: generated configurations | `activeFork`, `Ordered`, `activationsOrdered`, `Activation.le` | any list of forks and activations, ordered or not, ties, forks never reached | the latest reached fork; the last reached in an ordered list | 1000 | ordered 80% (min 25), no fork active 24% (min 8), two reached forks share an activation 41% (min 12) |
| blob schedule of a chain at a block | `blobScheduleAt`, `chainBlobSchedule` | any list of schedules, ties | the last reached in the list | 1000 | sets one 52% (min 15), sets none 48%, a tie 9% (min 3) |
| blob schedule of every fork | `BlobBaseFee.blobSchedule` | every fork | EIP-4844, EIP-7691, EIP-8134, EIP-8135 | 1000 | before Dencun 65% |

### The base layer (`Base/`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| big-endian bytes at any width | `natToBytes`, `natToBytes4`, `bytesToNat` | width 0 to 40, a number that fits and one that does not | digits on `Nat` | 1000 | fits 46%, does not fit 54% (min 18), width zero 12% |
| little-endian bytes at any width | `uintToBytes`, `bytesToUint`, `bytesToUint64` | width 0 to 40, every width from 0 to 8 | `Nat` | 1000 | does not fit 57%, each width 0 to 8 about 9% |
| 32-bit word helpers | `rotl32`, `uint32OfBytes`, `uint32Byte` | shifts 0 to 255 | `Nat` | 1000 | shift 0 mod 32 6%, 32 or more 26% |
| a word, its bytes, its address | `U256.toBeBytes`, `fromBeBytes`, `toSigned`, `fromSigned`, `toAddressMasked`, `Address.toU256` | 0, 1, `2^255 - 1`, `2^255`, `2^256 - 1`, `2^160`, any | `Nat`, `Int` | 1000 | `≥ 2^255` 40%, `≥ 2^160` 79% |
| an integer as a signed word | `U256.fromSigned` | integers inside and outside `[-2^255, 2^255)` | `Int` | 1000 | outside 46% |
| byte strings | `packBytes`, `exactBytes?`, `readBytes`, `byteAt`, `xorBytes`, `xorByteArray` | unequal lengths, a read that ends at the end | lists | 1000 | second shorter 26%, longer 26% (min 8 each) |
| hexadecimal | `hexString`, `hexNat`, `hexValue?`, `byteHexDigits` | width below, at and above the digits | `Nat` | 1000 | below 35%, at 23%, above 42% |
| bounds on a length | `Length.hasAtLeast`, `decideLeLength`, `decideLengthLt` | bound below, at and above the length | `List.length` | 1000 | 31%, 29%, 40% |
| 64-bit helpers | `Uint64.ofNatChecked`, `saturatingSub`, `subChecked`, `integerSquareroot`, `GWEI_TO_WEI`, `ensure` | `2^64 - 1`, `2^64`, equal operands, squares and their neighbours | `Nat` | 1000 | exactly `2^64` 9%, equal operands 34% |
| the gas limit toward a target | `gasLimitToward` | parent at multiples of 1024, target one step away and one past it | `is_gas_limit_target_compatible` of the consensus specifications, transcribed; the strict bound of EIP-1559 | 1000 | above the step 29%, below 29% (min 9 each), exactly one step 16%, one past 15%, parent below 2048 19% |

`Property/Base.lean` of the first round covers base64, the byte reader and the checked arithmetic.

### Hash internals (`Cryptography/Hash/`, `Cryptography/Aes/Block.lean`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| every constant table | `Sha256.K`, `IV`; `Ripemd160.K`, `K'`, `r`, `r'`, `s`, `s'`, `IV`; `Keccak.RC`, `RHO`, `Internal.roundConstant`, `rhoOffsets`; `Blake2b.IV`, `SIGMA`; `Aes.SBOX`, `INV_SBOX`, `sbox`, `invSbox`, `Internal.sbox`, `rcon`, `mul` | every entry, the 65,536 products of GF(2^8) among them | tables computed from the definitions: cube and square roots of primes, the LFSR and the walk of FIPS 202, the permutations of the RIPEMD-160 paper, the inverse and affine map of FIPS 197 | 1 test, all entries | -- |
| sha256: compression on any state | `Sha256.compress`, `Window.ofBlock`, `Window.next`, `rounds` | any 8 words of state, any block, an offset | FIPS 180-4 §6.2.2 transcribed, checked against hashlib at start | 1000 | the initial hash value 18% |
| ripemd160: compression on any state | `Ripemd160.compress`, `line`, `step`, `f` | any chaining value, any block | the authors' pseudo-code transcribed, checked against pycryptodome | 1000 | -- |
| keccak: steps, rounds and permutation | `theta`, `rho`, `pi`, `chi`, `round`, `keccakF` | any state, a single lane set, every round index | FIPS 202 §3.2 transcribed, checked against hashlib SHA3-256 | 1000 | each round about 4% |
| keccak: the sponge at every rate | `spongeAbsorb`, `Internal.absorbBlock`, `absorbBlocks`, `pad`, `blockCount` | every rate of whole lanes, 8 to 192 bytes; lengths around a block | the sponge transcribed, checked against pycryptodome at 144, 136, 104 and 72 | 1000 | rate above 136 26% (min 9), below 72 28% (min 9), message fills its last block 22% (min 7) |
| keccak: the padding at every rate | `padding`, `paddingByte` | rates 1 to 250, lengths to `2^70` | FIPS 202 §5.1 | 1000 | one byte 10%, a whole block 18% |
| keccak: the hasher and both digests | `Hasher256`, `keccak256`, `keccak512`, `squeeze256`, `squeeze512` | chunks around 136 and 272 bytes | the sponge | 1000 | a block exactly 6% |
| crc: any generator | `Crc.digest`, `value`, `remainder`, `shift`, `shiftByte`, `reverseBits`, `Crc32.crc32`, `Crc32c.crc32c` | any generator polynomial of degree 32 | a bitwise CRC, checked against zlib and crc32c | 1000 | a named generator 18%, shorter than 32 bits 34% |

### Extension fields and pairings (`Cryptography/Bls/`, `Cryptography/AltBn128/Pairing.lean`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| constants of the curves | moduli, orders, generators, `b`, twist constants, loop counts and final exponents of BLS12-381 and alt_bn128; `blsX`, `BN_U`, `H_EFF_G1` | -- | py_ecc; the polynomials of the two families | 1 | -- |
| `Fp12` of BLS12-381 | `Fp12.mul`, `square`, `add`, `sub`, `neg`, `inverse`, `frobenius`, `conjugate`, `isOne` | dense and sparse elements, zero | py_ecc `FQ12`, coefficient by coefficient | 1000 | zero 9%, in `Fp6` 34% |
| `Fp2` and `Fp6` of BLS12-381 | `Fp2.mul`, `inverse`, `conjugate`, `powNat`, `mulByOnePlusI`; `Fp6.mul`, `inverse`, `mulByV`; `frobeniusCoeff` | elements, exponents | py_ecc, as subfields | 1000 | `Fp2` zero 20%, `Fp6` zero 14% |
| final exponentiation and cyclotomic formulas | `finalExponentiation`, `cyclotomicSquare`, `cyclotomicPow` | any element; exponents 0 to 5, `blsX`, 64 bits | py_ecc powers | 250 | zero 6% |
| the value of the BLS12-381 pairing | `Bls.pairing`, `millerLoop`, `G1.mulNat`, `G2.mulNat`, `toAffine` | multiples of both generators | py_ecc `pairing`, all 12 coefficients, and bilinearity | 50 | -- |
| the Miller loop of any parameter | `millerLoop`, `millerSteps`, `millerDouble`, `millerAdd`, `lineValue` | `s` from 1 to `2^64`, powers of two, all bits set | the Miller function by py_ecc's affine lines | 50 | `s = blsX` 12%, power of two 38%, all bits set 30% |
| `Fp12` and `Fp2` of alt_bn128 | `Fp12.mul`, `add`, `sub`, `inverse`, `frobenius`, `frobeniusPow`, `powBits`, `scale`, `ofFp2`; `Fp2.mul`, `inv`, `conj`, `powBits` | elements, exponents, 0 to 12 Frobenius maps | py_ecc | 1000 | zero 8% |
| scenario: an accumulator in `Fp12` (`Command`) | 7 commands over both curves: multiply, square, invert, Frobenius, easy part, cyclotomic square, cyclotomic power | sequences of 1 to 20 | py_ecc | 1 in order, 2 x 250 madhouse | reached the cyclotomic subgroup 62%, a cyclotomic square ran 27%, a cyclotomic power 16%, an inverse of zero 4% |

### Key derivations (`Cryptography/Hash/`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| HMAC-SHA-256 | `Hmac.hmac`, `hmac32`, `blockKey` | key and message around 0, 64, 128, 192 bytes | hmac | 1000 | key exactly a block 6% (min 1), one byte longer 4%, longer 43% (min 15), empty 24% |
| HKDF | `Hkdf.expand`, `hkdf`, `extract`, `expandBlocks` | output 0, around multiples of 32, around `255 * 32`, larger; key around 32; empty info and salt | RFC 5869 §2.3 transcribed | 1000 | exactly 255 blocks 8% (min 2), longer 20% (min 6), key shorter than 32 29% (min 8), output empty 10% |
| PBKDF2 | `Pbkdf2.pbkdf2`, `block`, `blocks`, `iterate` | iterations 0 to 40, output around multiples of 32, long passwords, empty salt | hashlib | 1000 | no iteration 20% (min 6), one 16%, several blocks 58% (min 20) |
| the Concatenation KDF | `ConcatKdf.concatKdf`, `blocks` | output around multiples of 32, empty secret and info | SP 800-56C §4.1 transcribed | 1000 | several blocks 60%, empty output 18% |
| the limits of the lengths | `Pbkdf2.MAX_LENGTH`, the refusals of `pbkdf2`, `concatKdf`, `scrypt` | `(2^32 - 1) * 32` and one past it | the texts | 50 | one past 36% |
| scrypt | `Scrypt.scrypt`, `validCost` | `N` from 0 to `2^17`, `r` from 0 to 4, `p` from 0 to 3, output around multiples of 32 | hashlib, and the rules of RFC 7914 §2 | 250 | accepted 38%, `N = 2^15` at `r = 1` 2%, `N = 2^16` at `r = 1` 4%, several blocks mixed 53% |

### Jacobian formulas (`Cryptography/Jacobian.lean`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| constants of secp256k1 and P-256 | moduli, orders, `a`, `b`, generators | -- | py_ecc, OpenSSL | 1 | -- |
| any curve over a small prime | `Jacobian.add`, `double`, `mulBits`, `mulAdd`, `toAffine`, `ofAffine`, `infinity` | 19 primes, any `a` and `b`, any `Z`, the fuel | the affine law of SEC 1 §2.2.1 on `Nat` | 1000 | `a = 0` 32%, `a = -3` 29% (min 10 each), `P = Q` 24% (min 6), `P = -Q` 25% (min 7), `P` at infinity 12% (min 4), order two 15% (min 1), `Q` with `Z = 1` 32%, scalar is the order 16% (min 5), scalar beyond the fuel 20% |
| generators at the edges of the order | `Secp256k1.Point.mulBits`, `mulAdd`; `Secp256r1.Point.mulBits` | scalars 0, 1, `n - 1`, `n`, `n + 1`, `2^256 - 1`, any | py_ecc, OpenSSL | 250 | scalar 0 mod `n` 16% and 21%, above `n` 16% and 23%, the two products cancel 50% |

### Unicode (`Base/Unicode.lean`, `Base/Unicode/Data.lean`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| every code point | `Unicode.decompose`, `combiningClass`, `lookup`, both tables | all 1,114,112 code points but the 2,048 surrogates | `unicodedata` 15.1.0: 287,346 code points compared; or `UnicodeData.txt` of 16.0.0: all 1,112,064 | 1 test | 68 entries unknown to 15.1.0 |
| the order of marks | `Unicode.nfkd`, `canonicalOrder`, `insertMark` | strings of marks of the tables, starters, decomposing code points, Hangul | the same | 1000 | two marks out of order 14%, of one class 16% (min 5 each), a starter between marks 15% |

### Trusted setup and signature frame (`Cryptography/Kzg/TrustedSetup*.lean`, `HashSig.lean`, `Wots.lean`)

| Property | EthLib definitions | Parameters varied | Reference | Cases | Shares |
| --- | --- | --- | --- | --- | --- |
| every point of the ceremony | `g1LagrangeHex`, `g1MonomialHex`, `g2MonomialHex` | all 8,257 points | the preset that eth-consensus-specs ships | 1 | -- |
| the decoded points | `TrustedSetup.ofHex`, `ofBytes`, `bitReversalPermutation` | 24 indices, all 65 points of `G2` | the text; the sum of the Lagrange points is the generator | 1 | -- |
| chains, search and ordered vectors | `Wots.chain`, `findFirst`, `HashSig.ofFnInOrder`, `unpackBytes?` | start, steps, fuel, offsets | lists, and the count of calls | 1000 | chain reaches the last position 34%, a trial passes 19%, the object ends at the end of the buffer 34% |

The harness was checked for sensitivity by breaking a reference in three places.
A sponge that absorbs only 136 bytes at rates above 144 failed the sponge property, shrunk to rate 152 and the empty message in 8 shrinks.
A Homestead block of 1,150,001 failed the mainnet property, shrunk to block 1,150,000 and time 0 in 3 shrinks.
One changed entry of the inverse S-box failed the table test with its index.
A model whose negation of zero is `p` failed both machines, shrunk to the accumulator 0 and one `neg`.
Each reference was then restored and compared with its copy.

## Findings

### 1. BUG (stale data): Hoodi activates Glamsterdam at a time its sources withdrew

Reported upstream as issue #3490.

- Definition: `ChainConfig.hoodi`, `EthLib/Base/ChainConfig.lean:214`, the last activation, line 236: `(.glamsterdam, .time 1793036568)`.
- Shrunk counterexample: block 0, timestamp 1793036568.
- EthLib: `hoodi.activeFork 0 1793036568 = some glamsterdam`, and so for every later timestamp.
- Reference: `bpo2`.
- The text of `hoodi` gives two sources: the genesis file of eth-clients/hoodi at a pinned commit, and "the meta EIP of each later fork gives its time: EIP-7600, EIP-7607 (BPO1, BPO2) and EIP-7773".
- The genesis file at that pinned commit ends at `"bpo2Time": 1762955544` and has no `amsterdamTime`.
  The pinned commit is itself the one titled "chore: unschedule Hoodi Glamsterdam activation (#33)", of 2026-10-22: it removes `"amsterdamTime": 1793036568` from `metadata/genesis.json`, and `GLOAS_FORK_EPOCH: 132352` from `metadata/config.yaml`.
  The commit "feat: schedule Hoodi Glamsterdam activation (#31)" of 2026-10-09 had added both.
- EIP-7773, section Activation, read on 2026-11-20: the row of Hoodi is empty.
  The change "Update EIP-7773: Clear postponed Hoodi activation" of 2026-11-18 replaced `| Hoodi | 132352 | 1793036568 (2026-10-26 17:42:48 UTC) |` with an empty row.
  The table says: "rows in the table above will be filled as activation times are decided by client teams."
- So the value was the one of EIP-7773 when EthLib took it (the change that added `hoodi` is of 2026-11-05), and it is stale since 2026-11-18.
  It disagreed with the pinned genesis file from the start.
- EthLib disagrees with itself: `bindings/python/tests/consensus/test_fork_digest.py` reads `metadata/config.yaml` at the same pinned commit and says "Gloas and Heze are not in the file, so they keep the far future", and expects the digest epochs `[0, 2048, 50688, 52480, 54016, FAR_FUTURE_EPOCH]`.
  So on Hoodi the consensus layer of EthLib has no Gloas while its execution layer has Amsterdam from 2026-10-26, and `Fork.glamsterdam` is one fork of both layers.
- Why no test caught it: `bindings/python/tests/chain/test_hoodi.py` pins the same number, `(1_793_036_568, "bpo2", "glamsterdam")`, and the theorems on `hoodi` (`hoodi_ordered`, `hoodi_dencun_le`) say nothing of the value of the last activation.
- Reach: `hoodi.activeFork` is exported as `eth_hoodi_active_fork` and `hoodi_active_fork`; every reader of the configuration of Hoodi takes a block after 2026-10-26 for a block of Glamsterdam.
- Search upstream: `git log --all -i --grep=hoodi` gives the change that added the configuration, whose message says "Glamsterdam is active on the Hoodi test network since 2026-10-26, as EIP-7773 gives"; nothing later touches the activation, and the CHANGELOG names Hoodi only for the exports of `hoodi_active_fork`.
- The 1793036568 itself is right arithmetic: it is the start of epoch 132352 of Hoodi, whose genesis is at 1742213400.
- Not verified: I read the two repositories over the network on 2026-11-20, not from a pin of `tests/sources.toml`.
  Whether Hoodi runs Glamsterdam today is a fact about the network that I did not observe; I report what the two cited sources say.

Standalone reproduction:

```lean
import EthLib.Base
open EthLib.Base

#eval ChainConfig.hoodi.activeFork 0 1793036567  -- some bpo2
#eval ChainConfig.hoodi.activeFork 0 1793036568  -- some glamsterdam
```

The one command that shows it:

```bash
HEDGEHOG_ONLY=finding lake exe kernels-property
```

```text
✗ finding: Hoodi activates Glamsterdam, which its sources withdrew failed after 1 test and 18 shrinks.
    forAll (0, 1793036568)
    === failed
      lhs: "glamsterdam"
      rhs: "bpo2"
```

The reference in `oracle/kernels_chain.py` holds Hoodi as its genesis file has it, without Glamsterdam.
The passing properties compare Hoodi below that timestamp, and its other activations.
The first version of the reference had copied the number from EthLib, and the property passed: the finding came from reading EIP-7773 for a number I could not confirm from memory.

### 2. Generator (not a deviation): the final subtraction almost never fired at `Fp` of BLS12-381

- The first full run required 30% of the sequences to make the final subtraction of a product fire, and the run failed on that minimum, with every case passing.
- The shares were 23% at a generated modulus of 8 limbs, 18% at 12 limbs, 20% at `Fr`, and 4.6% at `Fp` of BLS12-381.
- Reason: the rows end at `(a b + m p) / R` with `m` uniform below `R`, which is `p` or more with probability about `p / 2R`, and `p` is `R / 8` at `Fp`.
- The generator now solves for it: `Mont.firingForm` aims `m = a b (-p⁻¹) mod R` just below `R`, and checks each candidate on the rows.
- After the change the shares are 46% to 60%, and 57% at `Fp`.
- This is the branch that the brief names, and `cover` is what showed that the first generator rarely reached it.

### 3. Notes: behaviour outside a stated condition, pinned

These are stated in the docstrings, so they are not deviations.
The driver keeps each as a property that fails by design, in a group of its own.

- `Montgomery.mulLow` and `mulHigh` give the product only when `2 p ≤ R`, as the text of `mulLow` and the theorem `mulHigh_mulLow` say.
  Above `R / 2` they gave another number in 6% of the cases: shrunk to `p = 2^256 - 1`, a split at row 1, `a = b = p - 1`, where the parts give `2^256 - 2^32` and the product is 1.
  EthLib splits the product only at `Fp` of BLS12-381, where `2 p < R`, and the instance proves it.
- `Jacobian.mulBits fuel k` asks for `k < 2^fuel`; a larger scalar loses its higher bits, so `mulBits 0 7 P` is the point at infinity.
- `natToBytes len n` and `uintToBytes k n` keep `n mod 256^len`, as both texts say; the properties check exactly that on numbers that do not fit.
- `U256.fromSigned` reduces modulo `2^256` outside the range, as its text says.
- `gasLimitToward` has no floor of 5000.
  That is the rule of Gloas, `is_gas_limit_target_compatible`, which has none either, and `Engine/BuildPayload.lean` raises its target to 5000 before the call and says so.
  With a parent below 5000 the result can be below 5000; such a parent is not a valid block.

### 4. Notes: where two correct references differ

- The value of the BLS12-381 pairing is the inverse of py_ecc's on every case, and a conjugate is an inverse there.
  EthLib conjugates the Miller value because `x` is negative, as the text of `Pairing.lean` says; py_ecc does not.
  The earlier driver could not compare the value because the towers differ; here an element crosses as its 12 coefficients of `w^k`, with `i = w^6 - 1`.
  arkworks has no way to read a value of `GT`, so the convention of EthLib is checked against py_ecc and its own text only.
- Unicode: the host of Python 3.13 has Unicode 15.1.0 and EthLib has 16.0.0.
  Against the host, 287,346 code points agree and 68 entries of EthLib are of code points the host does not assign.
  Against `UnicodeData.txt` of 16.0.0 (`ETHLIB_UCD`), every code point agrees: 5,913 decompositions, 934 combining classes, the Hangul syllables, and every other code point unchanged.

### HARNESS

- `Kzg.BitReversal.reverseBits n order` takes the order, 4096, not the count of bits; the first version passed 12 and the decoded setup failed at index 1.
  The property now reverses the 12 bits itself.
- `Mont.genModulus` subtracted up to `2^41` from `R`, which is 0 at one limb; the product on words then ran at `p = 0` and failed, shrunk to one limb.
  The distance is now bounded by `R / 4`.
- The first reference of Hoodi copied EthLib's Glamsterdam time: see finding 1.

## Not covered

- `Proofs/` and `Exports/`, by the brief.
- Limb counts other than 8 and 12 for the stored form: `Limbs` has two instances.
  The product on words runs at 1 to 16 limbs, and nothing else is generic in the count.
- An even modulus, a modulus of `R` or more: the structure `Modulus` cannot hold one, since its proofs are checked at run time here.
- Moduli of 8 and 12 limbs are generated, but a modulus is compiled into EthLib at three instances only; the generic code ran unspecialized (`@[nospecialize]`), so the unrolled code of a fourth instance was not exercised.
- Keccak at a rate that is not whole lanes, or of 200 bytes or more: FIPS 202 defines no sponge there and the text says so.
  Only the padding runs at those rates.
- SHA-256 and RIPEMD-160 lengths of `2^61` bytes or more; the `inputTooLong` branches of PBKDF2 and the Concatenation KDF: no such buffer can be built.
- BLAKE2b `SIGMA` is compared with a table typed from RFC 7693, which the oracle validates by running BLAKE2b against hashlib; the compression function itself is the first round's.
- The RIPEMD-160 rotation table is typed from the paper (80 numbers by word and round); the orders are derived from the permutations.
  The whole is validated against pycryptodome.
- AES: only the tables and the field product here; the cipher at its three key sizes is the first round's.
  No key size outside FIPS 197.
- scrypt above `N = 2^15`, `r = 4`, `p = 3`; `N = 2^14` and more only at `r = 1`.
- The isogeny constants and the constants `beta`, `c1Psi`, `c2Psi`, `H_EFF_G2` of BLS12-381: every call of hash-to-curve and of the subgroup check reads all of them, and the first round compared those with py_ecc and arkworks.
- The Miller loop for `s` of more than 64 bits, and the alt_bn128 pairing, whose value the first round compared.
- `millerLoop` with `s = 0`.
- Curves over small primes use primes up to 251; `mulAdd` runs with the first scalar reduced below `2^fuel`.
- `Fork`-indexed fields (`Since`, `Until`, `During`, `decEqUnder`): their decision procedures carry proofs.
- `ChainConfig.mainnet`: compared with a table I typed from EIP-6953 and read from EIP-7600 and EIP-7607 on 2026-11-20; the block numbers before the Merge are from memory of EIP-6953 and were not fetched.
- No Sepolia or Holesky configuration exists in `Base` to compare.
- The predecessor of a fork: `Base` has no such function.
- Constant time: nothing here measures time.

## Notes on lean-hedgehog 0.3.0

What helped, concretely:

- The context first in `check`, `apply` and `next`.
  `TowerScenario.Field` holds the oracle, the name of the curve, its modulus and four closures over EthLib's operations.
  Seven command types then serve BLS12-381 and alt_bn128 with no copy of a handle, and `CycloSquare.check f _ s` reads from the context whether the curve has the operation at all.
  In 0.2 each command would have carried the oracle and the closures.
- `applySut sut before after t`.
  The Montgomery machine classifies a product by what the rows do on the forms of the two operands, and that needs the accumulator before the transition.
  Without `before` the model state would have had to keep its previous value, as `ReaderModel.before` does in `Property/Base.lean`.
- Coverage found a real weakness of a generator (finding 2): a property that passed 1,000 sequences had reached the final subtraction at `Fp` in 46 of them.
  `classify` inside `applySut` and inside `Command.apply` works as in a plain property.
- `cover` reports are clear: "passed 1000 tests, with insufficient coverage", and a ✗ on the label below its minimum.
- `Selection.fromEnv`: `HEDGEHOG_ONLY=montgomery`, `HEDGEHOG_ONLY=finding`, `HEDGEHOG_ONLY="tower scenario"` were how I worked; a group with nothing selected prints nothing, which keeps a partial run readable.
- `HEDGEHOG_RECHECK="0 17445416919550470856 3307693301880137653"` with `HEDGEHOG_ONLY` replayed the finding exactly, shrinks included, with no change to the driver.
- `mustFail := true` makes a finding a standing test: the group of findings and the group of pinned conditions print their counterexamples on every run and return true.
- `scenarioFrom` with a generated start state, a range `(.linear 1 20)` and a setup that annotates the state: all three were needed, and the setup is the only place the start state shows in a report.
- `===` on `Except` compared `Uint64.subChecked` and the refusals of the key derivations directly.
- `Gen.bytes` with `forAllWith bytesHex` replaced the list detour of the first round.
- Shrinking: the fault in the sponge shrank to rate 152 (the least above 144) and the empty message; the fork fault to `(1150000, 0)`; the machine fault to `{ p := <secp256k1>, acc := 0 }` and `[neg]`; the finding to `(0, 1793036568)`.

What was awkward:

- A share in a state machine or a scenario counts sequences, not transitions.
  "mul: the final subtraction fired 46%" means 46% of the sequences had one such product, which mixes the branch with the length of the sequence.
  A tally per occurrence (a `tally "name"` that counts every call, reported as a share of calls) is what one wants for a branch of a transition.
- A minimum depends on the run length, as USAGE says, so `cover` cannot sit in a property that is also run at 100 cases.
  I wrapped each property in `withMinimums cases [(15, "name"), ...]`, which appends `cover n name false` after the test only when the run has 500 cases or more.
  That works because a class named twice keeps the greater minimum, which is documented, but it is a trick.
  A `Property.withCoverage [(name, minimum)]`, or a `cover` that is not enforced below a number of tests, would say it directly.
- Labels print in the order they were first named, which changes from run to run in a machine; two reports of the same property do not diff.
  A fixed order, declared or sorted, would help.
- `collect` on a number prints a bare `5` among the labels; I used `label s!"{n} limbs"` instead.
- `next` must repeat by hand what `apply` does to the model, and nothing checks that the two agree.
  `EasyPart.next` sets the cyclotomic flag always, `apply` sets it only for a nonzero element; the scenario then generates a `CycloSquare` that `check` skips at run time, silently.
  An optional check that the state after `apply` matches `next` on the fields a command declares would catch a drifted `next`.
- `buildIn` sees the predicted state only; it was enough for "multiply by one while cyclotomic", but an operand that depends on the value of the accumulator cannot be built, since the value comes from the oracle.
- `mustFail` returns false when a property passes by chance at a small run.
  The pinned property on the split product fails in 6% of the cases, so I run it at 2,000 tests at least; a `mustFail` property would like its own minimum of tests.
- A value drawn after a `discard` or after another draw shrinks less far, as USAGE warns: the pinned property on the fuel shrank the scalar to 7 where 1 fails too, because the point is drawn after it.
- `Selection` has no way to list the names, and no negative selection (`all but the slow ones`).
- `checkGroup` prints no time per property and no totals; the slow properties (pairings, final exponentiation) had to be found by timing groups.
- The count of cases is per property through `withTests`; a slow property divides the driver's argument by hand (`cases / 20`).

What is missing:

- A per-occurrence tally, as above.
- A way to attach a minimum outside the body, as above.
- A generator of a `Vector` or of a fixed-length list that shrinks its elements without changing the length is `Gen.list (.singleton n)`, which works; a named `Gen.vector` would read better.

Bugs of the library: none met.
One trap that is Lean's and EthLib's, not the library's: instantiating the generic machine at 8 limbs inside `main` made the compiler specialize EthLib's unrolled product there and time out at 200,000 heartbeats; `@[nospecialize, noinline]` on the generic definitions fixed it.

## The sponge property against the block step of before #3346, by the coordinator

The first round compared Keccak-256 and Keccak-512 alone, and so passed a block step that XORed lanes 0 to 16 only.
Upstream fixed that step in #3346.
To see what this driver would have said, the step was put back in a copy of this branch: lanes 17 to 24 left alone, the rest of the library as it is.
`HEDGEHOG_ONLY=sponge,rate lake exe kernels-property 1000` there fails after 2 tests and 6 shrinks:

```text
✗ keccak: the sponge at every rate failed after 2 tests and 6 shrinks.
    forAll 144
    forAll 0
    forAll
```

That is the least rate of whole lanes above 136 bytes, and the empty message.
"keccak: the hasher and both digests", which runs the two rates in use, passes on the same copy, as the first round's properties did.
The copy was built and run once on 2026-11-20 and then removed; the branch itself was never changed.

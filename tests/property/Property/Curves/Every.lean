import Property.Curves.BlsSig
import Property.Curves.Kzg
import Property.Curves.KzgPoly
import EthLib.Cryptography.Xmss
import EthLib.Cryptography.Secp256k1
import EthLib.Cryptography.Sphincs

/-!
# Every parameter: the tags, the branches and the indices that the first round left out

A general function is tested at every value of its parameters, not only at those in use today.

- The core BLS operations take a domain separation tag: any tag is generated.
- The sign of a coordinate has a branch for a real `y`, which random points do not reach.
- The cofactor clearing of `G2` has two definitions in RFC 9380, and EthLib computes one.
- A child key is derived from any parent key, also one with leading zero bytes.
- A cell proof is verified at every one of the 128 cell indices.
- The evaluation form, the FFT and the FFT in `G1` take a domain of any size.
- The addresses of leanXMSS and leanSPHINCS are encoded at the edges of every field.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.Every

open Bls Bls.Signatures Bls12

/-! ## BLS signatures under any tag -/

/-- The tags of the three schemes of the BLS signature draft, and that of its proofs. -/
def suiteTags : List ByteArray :=
  ["BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_", "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_AUG_",
    "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_", "BLS_POP_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"
    ].map String.toUTF8

/-- A tag: one of a scheme, none, a short one, or one at the edge where a tag is hashed first. -/
def genTag : Gen ByteArray :=
  Gen.frequency [(4, Gen.element suiteTags), (1, pure ByteArray.empty),
    (2, genBytes (.constant 1 40)), (2, Gen.element [255, 256, 300] >>= genBytesN)]

/-- The two tags of the proof-of-possession scheme are those of the draft, section 4.2.3. -/
def tags (oracle : Oracle) : Property IO := propertyM do
  pure do
    s!"{hex DST} {hex POP_DST}" === (← oracle.ask ["dsts"])

/-- The core signature and the core verification under any tag are the reference's.

A signature verifies under its own tag, key and message, and under no other tag.

A signature of a key as a message is no proof of possession, and a proof is no signature. -/
def coreAnyTag (oracle : Oracle) : Property IO := propertyM do
  let k ← forAll (Gen.frequency [(1, Gen.element [1, r - 1]), (4, genScalar r)])
  let msg ← forAllWith hex (genBytes (.constant 0 40))
  let (dst, other) ← forAllWith (fun (a, b) => s!"{hex a} {hex b}") (Gen.zip genTag genTag)
  let change ← forAll (Gen.element [0, 0, 1, 1, 2, 3])
  classify "the tag of the message scheme of Ethereum" (dst == DST)
  classify "the tag of another scheme of the draft" (suiteTags.contains dst && dst != DST)
  classify "no tag" (dst.size == 0)
  classify "a tag of 255 bytes, the longest kept" (dst.size == 255)
  classify "a tag above 255 bytes, hashed first" (dst.size > 255)
  pure do
    let some sk := secret k | failWith "no key"
    let .ok made := coreSign sk msg dst | failWith "no signature"
    let sig : ByteArray := ⟨made.toArray⟩
    hex sig === (← oracle.ask ["coresign", toString k, hex msg, hex dst])
    let pk := pkOf k
    let (pk', msg', dst') := match change with
      | 1 => (pk, msg, other)
      | 2 => (pk, msg.push 0, dst)
      | 3 => (pkOf (k % (r - 1) + 1), msg, dst)
      | _ => (pk, msg, dst)
    let got := coreVerify pk' msg' sig dst'
    classify "verified under its own tag" (got && change == 0)
    classify "refused under another tag" (!got && change == 1 && dst' != dst)
    classify "the other tag is the same one" (change == 1 && dst' == dst)
    classify "refused: another message" (!got && change == 2)
    classify "refused: another key" (!got && change == 3)
    (if got then "1" else "0") === (← oracle.ask ["coreverify", hex pk', hex msg', hex sig,
      hex dst'])
    ensure (got == (change == 0 || (change == 1 && dst' == dst)))
      "the tag, the key or the message does not decide the verification"
    -- The same under the aggregate verification, with a second signer of another message.
    let k2 := k % (r - 2) + 2
    let some sk2 := secret k2 | failWith "no second key"
    let .ok made2 := coreSign sk2 (msg.push 1) dst | failWith "no second signature"
    let .ok both := aggregate #[made, made2] | failWith "no aggregate"
    let both : ByteArray := ⟨both.toArray⟩
    let pks := [pk, pkOf k2]
    let msgs := [msg, msg.push 1]
    let agg := coreAggregateVerify pks.toArray msgs.toArray both dst'
    classify "an aggregate verified under its own tag" (agg && dst' == dst)
    if dst'.size > 0 then
      (if agg then "1" else "0") === (← oracle.ask ["coreaggverify", listWord (pks.map hex),
        listWord (msgs.map hex), hex both, hex dst'])
    ensure (agg == (dst' == dst)) "the tag does not decide the aggregate verification"

/-- The two tags of Ethereum separate a signature from a proof of possession. -/
def separation : Property IO := propertyM do
  let k ← forAll (genScalar r)
  pure do
    let some sk := secret k | failWith "no key"
    let pk := skToPk sk
    let key : ByteArray := ⟨pk.toArray⟩
    let .ok proof := popProve sk | failWith "no proof"
    let .ok signature := sign sk key | failWith "no signature"
    ensure (popVerify pk proof) "an honest proof is refused"
    ensure (verify pk key signature) "an honest signature is refused"
    ensure (!popVerify pk signature) "a signature of the key is taken for a proof"
    ensure (!verify pk key proof) "a proof is taken for a signature of the key"
    ensure (proof != signature) "the two tags give one signature"

/-! ## Any count of field elements -/

/-- `hash_to_field` gives any count of elements of `Fp2`, each from 128 bytes of the expansion.

The suite asks for two; the function takes a count, and refuses one that needs over 255 blocks.

Each coefficient is 64 bytes read as a number mod `p`, as RFC 9380 section 5.2 says. -/
def fieldElements : Property IO := pureIO do
  let (msg, dst) ← forAllWith (fun (m, d) => s!"{hex m} {hex d}")
    (Gen.zip (genBytes (.constant 0 40)) genTag)
  let count ← forAll (Gen.frequency [(4, Gen.nat (.constant 0 5)), (2, Gen.element [63, 64, 65])])
  label s!"{if count ≤ 5 then toString count else "63 to 65"} elements"
  classify "refused: more than 255 blocks" (count ≥ 64)
  match HashToCurve.hashToFieldFp2 (F := Fp) msg dst count,
      HashToCurve.expandMessageXmd msg dst (count * 128) with
  | .ok us, .ok uniform =>
    us.toList.map (fun u => (u.c0.val, u.c1.val)) === (List.range count).map fun i =>
      (beNat (uniform.extract (128 * i) (128 * i + 64)) % p,
        beNat (uniform.extract (128 * i + 64) (128 * i + 128)) % p)
  | .error _, .error _ => ensure (count * 128 > 8160) "a count that fits is refused"
  | _, _ => failWith "the elements and their bytes disagree on the count"

/-! ## The sign of a coordinate -/

/-- A coordinate at the edges of the two halves of the field. -/
def genCoordinate : Gen Nat :=
  Gen.frequency [(2, Gen.element [0, 1, 2, (p - 1) / 2, (p + 1) / 2, p - 2, p - 1]),
    (3, Gen.nat (.constant 0 (p - 1)))]

/-- The sign of a `y` is that of the Zcash encoding, and `sgn0` is that of RFC 9380 section 4.1.

The larger of `y` and `-y` has the flag.

On `Fp2` the imaginary part decides, and the real part when the imaginary part is zero.

`sgn0` is the parity of the first coefficient that is not zero. -/
def signs : Property IO := pureIO do
  let (a, b) ← forAll (Gen.zip genCoordinate (Gen.frequency [(1, pure 0), (2, genCoordinate)]))
  classify "Fp2: the imaginary part is zero, so the real part decides" (b == 0)
  classify "Fp2: the imaginary part decides" (b != 0)
  classify "zero" (a == 0 && b == 0)
  classify "a real part of (p - 1) / 2, the last smaller one" (2 * a + 1 == p)
  classify "a real part of (p + 1) / 2, the first larger one" (2 * a == p + 1)
  classify "sgn0: the real part is zero, so the imaginary part decides" (a == 0)
  Fp.signBit (Fp.ofNat a) === decide (2 * a > p)
  Fp2.signBit ⟨Fp.ofNat a, Fp.ofNat b⟩ === (if b != 0 then decide (2 * b > p)
    else decide (2 * a > p))
  HashToCurve.sgn0Fp (Fp.ofNat a) === (a % 2 == 1)
  HashToCurve.sgn0Fp2 (F := Fp) ⟨Fp.ofNat a, Fp.ofNat b⟩ === (a % 2 == 1 || (a == 0 && b % 2 == 1))

/-! ## Powers in any modulus -/

/-- `Fin.powBits` is the power mod any modulus, of the low `fuel` bits of the exponent.

The two fields of secp256k1 call it with 256 bits; the function takes any modulus and any fuel. -/
def powers : Property IO := pureIO do
  let m ← forAll (Gen.frequency [(2, Gen.nat (.constant 1 40)), (1, Gen.element [2 ^ 64,
    2 ^ 64 - 1, 2 ^ 256, Secp256k1.Fp.modulus, Secp256k1.Fn.modulus]),
    (2, Gen.nat (.exponential 1 (2 ^ 300)))])
  let fuel ← forAll (Gen.frequency [(1, Gen.nat (.constant 0 8)), (1, Gen.element [255, 256, 257]),
    (1, Gen.nat (.constant 0 300))])
  let (a, e) ← forAll (Gen.zip (Gen.nat (.exponential 0 (2 ^ 300)))
    (Gen.frequency [(1, Gen.nat (.constant 0 8)), (2, Gen.nat (.exponential 0 (2 ^ 300)))]))
  classify "the modulus is 1" (m == 1)
  classify "the modulus is even" (m % 2 == 0)
  classify "no fuel, so the power is one" (fuel == 0)
  classify "the exponent does not fit the fuel" (e ≥ 2 ^ fuel)
  classify "the exponent is zero" (e == 0)
  classify "the base is zero mod the modulus" (a % m == 0)
  if h : m = 0 then discard else
    have : NeZero m := ⟨h⟩
    (Secp256k1.Fin.powBits fuel (Fin.ofNat m a) e).val === modPow m a (e % 2 ^ fuel)

/-! ## The cofactor of `G2` -/

/-- Clearing the cofactor is the multiple by `h_eff`, as RFC 9380 section 7 defines it.

EthLib computes it by the endomorphisms of Appendix G.3, on any point of the twist.

The reference multiplies by the number of section 8.8.2, and so does EthLib's own constant. -/
def cofactor (oracle : Oracle) : Property IO := propertyM do
  let pt ← forAllWith render2 genG2
  pure do
    let cleared := HashToCurve.clearCofactor pt
    classify "a point outside the subgroup" (!G2.inSubgroup pt)
    classify "a point of the subgroup" (G2.inSubgroup pt && !pt.isInfinity)
    classify "the point at infinity" pt.isInfinity
    render2 cleared === (← oracle.ask ["heffg2", render2 pt])
    render2 (G2.mulNat pt HashToCurve.H_EFF_G2) === render2 cleared
    ensure (G2.inSubgroup cleared) "the cleared point is outside the subgroup"

/-! ## A child key of any parent -/

/-- A child key of ERC-2333 is the model's, for any parent key and any index.

A parent below `2^248` is written with leading zero bytes, which the derivation must keep. -/
def childKeys (oracle : Oracle) : Property IO := propertyM do
  let parent ← forAll (Gen.frequency [(2, Gen.element [1, 2, 255, 256, r - 1, 2 ^ 248 - 1,
    2 ^ 248]), (1, Gen.nat (.exponential 1 (r - 1))), (2, genScalar r)])
  let index ← forAll genIndex
  classify "the parent has a leading zero byte" (parent < 2 ^ 248)
  classify "the parent is one byte" (parent < 256)
  classify "the parent is r - 1" (parent + 1 == r)
  classify "the index 0" (index.toNat == 0)
  classify "the index 2^32 - 1" (index.toNat == 2 ^ 32 - 1)
  classify "an index of 2^24 or more, four bytes" (index.toNat ≥ 2 ^ 24)
  pure do
    let some sk := secret parent | failWith "no key"
    let got := match KeyDerivation.deriveChildSk sk index with
      | .ok child => toString child.val.val
      | .error _ => "error"
    got === (← oracle.ask ["derivechild", toString parent, toString index.toNat])

/-! ## KZG at every cell index -/

open Kzg in
/-- Every one of the 128 cells of a blob verifies with its proof, in batches of 16.

A batch with the proof of a neighbour at one place is refused, and the reference agrees.

Recovery gives the cells back from 64 of them in a row, and refuses 63 and 129. -/
def everyCell (setup : TrustedSetup) (oracle : Oracle) : Property IO := propertyM do
  let spec ← forAll (KzgTest.genBlob false)
  let moved ← forAll (Gen.nat (.constant 0 127))
  pure do
    let .ok commitment := blobToKzgCommitment setup spec.blob | failWith "no commitment"
    let .ok (cells, proofs) := computeCellsAndKzgProofs setup spec.blob | failWith "no cells"
    cells.size === 128
    proofs.size === 128
    for batch in List.range 8 do
      let indices := (List.range 16).map (16 * batch + ·)
      let run (proofOf : Nat → Nat) : TestT IO String := do
        let commitments := indices.map fun _ => commitment
        let chosen := indices.map (cells[·]!)
        let shown := indices.map fun i => proofs[proofOf i]!
        let got := KzgTest.verdict (verifyCellKzgProofBatch setup commitments.toArray
          indices.toArray chosen.toArray shown.toArray)
        got === (← oracle.ask ["kzgverifycells", listWord (commitments.map hexVec),
          listWord (indices.map toString), listWord (chosen.map hexVec),
          listWord (shown.map hexVec)])
        pure got
      (← run id) === "1"
      if moved / 16 == batch then
        -- The proof of the next cell, at the place of one cell.
        let other := (moved + 1) % 128
        let got ← run fun i => if i == moved then other else i
        -- A constant blob has one proof for every cell: the point at infinity.
        classify "a proof of a neighbour is refused" (got == "0")
        classify "a proof of a neighbour is the same proof" (got == "1")
        ensure ((got == "1") == (proofs[moved]! == proofs[other]!))
          "a proof of another cell is accepted"
    label "128 cells verified"
    -- The edges of the count of recovery: 63 cells are too few, 64 are enough, 129 too many.
    let recover (indices : List Nat) : TestT IO String := do
      let chosen := indices.map fun i => cells[i % 128]!
      let result := recoverCellsAndKzgProofs setup indices.toArray chosen.toArray
      let got := match result with
        | .ok (all, shown) => s!"{KzgTest.digest all} {KzgTest.digest shown}"
        | .error _ => "error"
      got === (← oracle.ask ["kzgrecover", listWord (indices.map toString),
        listWord (chosen.map hexVec)])
      match result with
      | .ok (all, shown) =>
        ensure (all == cells && shown == proofs) "recovery gives other cells"
        pure "recovered"
      | .error e => pure s!"error {ctorName e}"
    let first := moved % 65
    (← recover ((List.range 64).map (first + ·))) === "recovered"
    (← recover ((List.range 63).map (first + ·))) === "error notEnoughCells"
    (← recover (List.range 129)) === "error tooManyCells"

open Kzg in
/-- The coset of every cell index from 0 to 127 is its block of the bit-reversed domain.

An index from 128 on has none. -/
def everyCoset : Property IO := pureIO do
  for cell in List.range 128 do
    match cosetForCell cell with
    | .ok coset =>
      KzgPoly.ofFr coset === (List.range 64).map fun j =>
        modPow r 7 ((r - 1) / 8192 * KzgPoly.reverseModel (64 * cell + j) 13)
    | .error _ => failWith s!"cell {cell} has no coset"
  for cell in [128, 129, 255, 256, 8191, 8192, 2 ^ 32, 2 ^ 64] do
    ensure (cosetForCell cell).toOption.isNone s!"cell {cell} has a coset"

/-! ## Domains of any size -/

open Kzg in
/-- The evaluation form over a domain of any power of two has the value of the polynomial.

The specification uses 4096 points only, and the function takes any domain. -/
def anyDomain : Property IO := pureIO do
  let k ← forAll (Gen.nat (.constant 0 7))
  let n := 2 ^ k
  let poly ← forAll (KzgPoly.genPoly (.constant 0 n))
  let domain := rootsOfUnityBrp n
  let inside ← forAll (Gen.nat (.constant 0 (n - 1)))
  let z ← forAll (Gen.frequency [(2, pure (domain[inside]!.val)), (3, KzgPoly.genCoeff)])
  let values := domain.map fun d => Fr.ofNat (KzgPoly.horner poly d.val)
  label s!"{n} points"
  classify "the point is in the domain" (modPow r z n == 1)
  classify "the point is outside the domain" (modPow r z n != 1)
  classify "the point is the last of the domain" (n > 1 && z == domain[n - 1]!.val)
  (evaluatePolynomialInEvaluationFormAux values domain (Fr.ofNat z)).val === KzgPoly.horner poly z

open Kzg in
/-- The FFT of any power of two is the sum it stands for, and its inverse undoes it.

Values of another length have no transform and come back as they are.

The FFT over a coset is the FFT of the values times the powers of 7. -/
def anyFft : Property IO := pureIO do
  let k ← forAll (Gen.frequency [(6, Gen.nat (.constant 0 5)), (2, pure 6), (1, pure 7)])
  let n := 2 ^ k
  let vals ← forAll (Gen.list (.singleton n) KzgPoly.genCoeff)
  let roots := computeRootsOfUnity n
  label s!"{n} values"
  let out := fftField (KzgPoly.toFr vals) roots
  let w := modPow r 7 ((r - 1) / n)
  KzgPoly.ofFr out === (List.range n).map fun i =>
    (vals.zipIdx.foldl (fun acc (v, j) => (acc + v * modPow r w (i * j % n)) % r) 0)
  KzgPoly.ofFr (fftField out roots (inv := true)) === vals
  -- Over the coset of 7: the values times the powers of 7, then the same transform.
  let shifted := vals.zipIdx.map fun (v, j) => v * modPow r 7 j % r
  KzgPoly.ofFr (cosetFftField (KzgPoly.toFr vals) roots) ===
    KzgPoly.ofFr (fftField (KzgPoly.toFr shifted) roots)
  KzgPoly.ofFr (cosetFftField (cosetFftField (KzgPoly.toFr vals) roots) roots (inv := true)) ===
    vals
  -- A length that is no power of two, and roots of another length.
  let odd ← forAll (Gen.element [0, 3, 5, 6, 7, 9, 12])
  let other ← forAll (Gen.list (.singleton odd) KzgPoly.genCoeff)
  classify "a length that is no power of two" (odd != 0)
  KzgPoly.ofFr (fftField (KzgPoly.toFr other) (computeRootsOfUnity odd)) === other
  if n > 1 then KzgPoly.ofFr (fftField (KzgPoly.toFr vals) (computeRootsOfUnity (n / 2))) === vals

open Kzg in
/-- The FFT in `G1` of points `s_j G` is the FFT of the scalars, times `G`.

So `out[i] = sum_j [w^(i j)] vals[j]`, as the docstring says, for 1, 2, 4 and 8 points. -/
def fftInG1 (oracle : Oracle) : Property IO := propertyM do
  let k ← forAll (Gen.nat (.constant 0 3))
  let n := 2 ^ k
  let scalars ← forAll (Gen.list (.singleton n)
    (Gen.frequency [(1, pure 0), (4, KzgPoly.genCoeff)]))
  pure do
    label s!"{n} points"
    classify "a point at infinity among them" (scalars.contains 0)
    let roots := computeRootsOfUnity n
    let points := scalars.map (G1.mulNat G1.generator)
    let out := fftG1 points.toArray roots
    out.size === n
    let w := modPow r 7 ((r - 1) / n)
    for i in List.range n do
      let expected := scalars.zipIdx.foldl
        (fun acc (v, j) => (acc + v * modPow r w (i * j % n)) % r) 0
      render1 out[i]! === (← oracle.ask ["g1mul", toString expected, render1 G1.generator])
    -- Points of another length come back as they are.
    let three := (points ++ [G1.generator, G1.generator]).take 3
    ((fftG1 three.toArray (computeRootsOfUnity 3)).toList.map render1) === three.map render1

/-! ## leanXMSS -/

open Xmss in
/-- A field of an address at its edges, below `2 ^ bits`. -/
def genField (bits : Nat) : Gen Nat :=
  Gen.frequency [(2, Gen.element [0, 1, 255, 256, 2 ^ (bits - 1) - 1, 2 ^ (bits - 1),
    2 ^ bits - 1]), (2, Gen.nat (.constant 0 (2 ^ bits - 1)))]

open Xmss in
/-- An address of leanXMSS is its four fields in little-endian bytes, for every type and field.

The layer sets bit 23 of the third field. -/
def xmssAddresses (oracle : Oracle) : Property IO := propertyM do
  let tau ← forAll (Gen.frequency [(2, Gen.element [0, 1, 2, 3, 5, 7, 12]),
    (1, Gen.nat (.constant 0 31))])
  let mu ← forAll (Gen.nat (.constant 0 7))
  let (hi, lo) ← forAll (Gen.zip (genField 24) (genField 32))
  let layer ← forAll (Gen.element [Layer.bottom, Layer.top])
  classify "a type that the scheme uses" ([0, 1, 2, 3, 5, 7, 12].contains tau)
  classify "another type" (![0, 1, 2, 3, 5, 7, 12].contains tau)
  classify "a chain position above zero" (mu > 0)
  classify "the third field has bit 23, the layer bit" (hi ≥ 2 ^ 23)
  classify "the last field is 2^32 - 1" (lo == 2 ^ 32 - 1)
  pure do
    hexVec (encodeAddress (Fin.ofNat _ tau) (Fin.ofNat _ mu) (Fin.ofNat _ hi) (UInt32.ofNat lo))
      === (← oracle.ask ["xmssaddress", toString tau, toString mu, toString hi, toString lo])
    (layerHi layer (Fin.ofNat _ (hi % 2 ^ 23))).val === hi % 2 ^ 23 + 2 ^ 23 * layer.toNat
    -- The codes of the types, as the specification assigns them.
    ([AddressType.prf, .chain, .leaf, .node, .param, .rnd, .msg].map (·.code.val)) ===
      [0, 1, 2, 3, 5, 7, 12]

open Xmss in
/-- The paths of a small subtree are those that climb to its top, for every leaf below it.

A signer reads a path from a built tree, and a verifier climbs it: here on up to 16 leaves.

The path computed sibling by sibling is the same, and the top is the model's node. -/
def xmssPaths (oracle : Oracle) : Property IO := propertyM do
  let seed ← forAllWith hex (genBytesN 32)
  let (layer, level) ← forAll (Gen.zip (Gen.element [Layer.bottom, Layer.top])
    (Gen.nat (.constant 0 4)))
  let j ← forAll (Gen.frequency [(2, Gen.nat (.constant 0 3)),
    (1, pure (2 ^ (16 - level) - 1))])
  label s!"level {level}"
  classify "the top layer" (layer == .top)
  classify "the last subtree of its level" (j == 2 ^ (16 - level) - 1)
  pure do
    let s := (schemeSeed hashId (vec32 (beNat seed))).run
    let prf := seedPrf hashId s
    let pp := (publicParamOf prf).run
    let built := (build hashId pp prf layer level j).run
    hexVec built.value === ((← oracle.ask ["xmsskey", hex seed, toString layer.toNat,
      toString level, toString j]).splitOn " ").getD 1 ""
    for e in (List.range (2 ^ level)).map (j * 2 ^ level + ·) do
      let leaf := (leaves hashId pp prf layer e).run
      let path := built.path level e
      let walked := (Merkle.path (nodeHash hashId pp layer) (leaves hashId pp prf layer) level
        e).run
      ensure (path == walked) s!"the two paths of leaf {e} differ"
      let top := (Merkle.climb (nodeHash hashId pp layer) ⟨0, e⟩ leaf path.toList).run
      ensure (top == built.value) s!"the path of leaf {e} does not climb to the top"

/-! ## leanSPHINCS -/

open Sphincs in
/-- A digest of leanSPHINCS near a codeword: 64 digits that sum to about 128. -/
def genSphincsDigest : Gen (Vector UInt8 16) := do
  let digits ← Gen.list (.singleton 64) (Gen.nat (.constant 0 3))
  let target ← Gen.frequency [(4, pure 128), (2, pure 127), (2, pure 129), (1, pure digits.sum),
    (1, Gen.element [0, 192])]
  let fix (ds : List Nat) : List Nat := Id.run do
    let mut ds := ds.toArray
    for _ in [0:200] do
      let sum := ds.foldl (· + ·) 0
      if sum < target then
        match ds.findIdx? (· < 3) with
        | some i => ds := ds.set! i (ds[i]! + 1)
        | none => pure ()
      else if sum > target then
        match ds.findIdx? (· > 0) with
        | some i => ds := ds.set! i (ds[i]! - 1)
        | none => pure ()
    return ds.toList
  let digits ← Gen.shuffle (fix digits)
  pure (Vector.ofFn fun i : Fin 16 => UInt8.ofNat
    ((List.range 4).foldl (fun acc k => acc * 4 + digits[4 * i.val + k]!) 0))

open Sphincs in
/-- A digest of leanSPHINCS is a codeword exactly when its 64 digits sum to 128.

The digits are those of FIPS 205 Algorithm 4, the first of a byte in its top two bits. -/
def sphincsCodewords (oracle : Oracle) : Property IO := propertyM do
  let digest ← forAllWith hexVec genSphincsDigest
  pure do
    let got := match codeword? digest with
      | some x => String.join (x.toList.map fun d => toString d.val)
      | none => "none"
    let sum := digest.toList.foldl (fun acc b =>
      acc + b.toNat / 64 + b.toNat / 16 % 4 + b.toNat / 4 % 4 + b.toNat % 4) 0
    classify "a codeword" (got != "none")
    classify "refused: the sum is 127" (sum == 127)
    classify "refused: the sum is 129" (sum == 129)
    classify "refused: another sum" (sum != 127 && sum != 128 && sum != 129)
    classify "every digit zero, or every digit three" (sum == 0 || sum == 192)
    got === (← oracle.ask ["sphincscodeword", hexVec digest])

open Sphincs in
/-- An address of leanSPHINCS is its six words in big-endian bytes, for every type and layer.

A word holds its value modulo `2^32`, and the tree modulo `2^64`.

The key of a layer on the way from an index is the tree and the leaf of FIPS 205 section 7. -/
def sphincsAddresses (oracle : Oracle) : Property IO := propertyM do
  let type ← forAll (Gen.element [AdrsType.wotsHash, .wotsPk, .tree, .forsTree, .forsRoots,
    .wotsPrf, .forsPrf, .wotsEnc])
  let layer ← forAll (Gen.element [Layer.bottom, .middle, .top])
  let tree ← forAll (Gen.frequency [(3, genField 64), (1, Gen.element [2 ^ 64, 2 ^ 64 + 1]),
    (1, genField 18)])
  let (key, word2, word3) ← forAll (Gen.zip (genField 33) (Gen.zip (genField 33) (genField 33)))
  let index ← forAll (Gen.frequency [(3, genField 26), (1, genField 40)])
  label s!"type {type.code.toNat}"
  classify "the tree has more than 32 bits" (tree ≥ 2 ^ 32)
  classify "the tree is 2^64 or more, so it is reduced" (tree ≥ 2 ^ 64)
  classify "a word of 2^32 or more, so it is reduced" (key ≥ 2 ^ 32 || word2 ≥ 2 ^ 32 ||
    word3 ≥ 2 ^ 32)
  classify "an index of 2^26 or more, past the hypertree" (index ≥ 2 ^ 26)
  pure do
    hexVec (adrs type layer tree key word2 word3) === (← oracle.ask ["sphincsadrs",
      toString type.code.toNat, toString layer.toNat, toString tree, toString key,
      toString word2, toString word3])
    let found := OtsKey.ofIndex layer index
    s!"{found.tree} {found.leaf}" === (← oracle.ask ["sphincskey", toString layer.toNat,
      toString index])
    -- The addresses of a FORS instance hold the bottom key of the index.
    let bottom := OtsKey.ofIndex .bottom index
    hexVec (adrsFors index word2 word3) === (← oracle.ask ["sphincsadrs", "3", "0",
      toString bottom.tree, toString bottom.leaf, toString word2, toString word3])
    hexVec (adrsNode layer tree word2 word3) === (← oracle.ask ["sphincsadrs", "2",
      toString layer.toNat, toString tree, "0", toString word2, toString word3])

end CurvesProperty.Every

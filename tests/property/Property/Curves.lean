import Property.Curves.Secp
import Property.Curves.Bn
import Property.Curves.Bls
import Property.Curves.BlsSig
import Property.Curves.Kzg
import Property.Curves.Kernels
import Property.Curves.XmssTest
import Property.Curves.VrfTest
import Property.Curves.SphincsTest
import Property.Curves.KzgPoly
import Property.Curves.Machines
import Property.Curves.Every
import Property.Curves.Minimums

/-!
# The public-key layer, on generated inputs

Each property generates inputs and requires an answer that EthLib did not compute.

It is that of a reference implementation (`oracle/curves.py`), or of a model on `Nat`.

    lake exe curves-property              # 100 cases of each
    lake exe curves-property 1000
    lake exe curves-property 1000 bn      # Only the groups whose name contains `bn`.
    HEDGEHOG_ONLY="bls verifies" lake exe curves-property 1000

`HEDGEHOG_ONLY` and `HEDGEHOG_RECHECK` select properties and replay a case.

Every property names the classes of its cases.

A run of 500 cases or more requires a minimum share of the classes that matter.
-/

open Hedgehog Support CurvesProperty

/-- The groups of the driver, each with its properties. -/
def groups (oracle : Oracle) (setup : EthLib.Cryptography.Kzg.TrustedSetup)
    (xmss : List XmssTest.Signed) (special : Specials) (cases : Nat) :
    List (String × List (String × Property IO)) :=
  let slow := max 1 (cases / 20)
  [("curves: kernels", [
    ("Montgomery limbs are the integers mod p", Kernels.montgomery.withTests cases),
    ("Montgomery limbs read bytes at an offset", Kernels.montgomeryBytes.withTests cases),
    ("the Euclidean inverse gives the gcd", Kernels.inverse.withTests cases),
    ("Jacobian formulas over 7", (Kernels.jacobianOn 7).withTests cases),
    ("Jacobian formulas over 23", (Kernels.jacobianOn 23).withTests cases),
    ("Jacobian formulas over 251", (Kernels.jacobianOn 251).withTests cases)]),
   ("curves: secp256k1", [
    ("k1 signs as RFC 6979 with low s", (K1.sign oracle).withTests cases),
    ("k1 verifies as SEC 1", (K1.verify oracle).withTests cases),
    ("k1 verifies a signature with x_R >= n", (K1.verifyWrapped oracle).withTests cases),
    ("k1 low-s rule", K1.lowS.withTests cases),
    ("k1 recovers as SEC 1", (K1.recover oracle).withTests cases),
    ("k1 recovers at the edges", (K1.recoverEdges oracle).withTests cases),
    ("k1 decodes SEC 1 encodings only", (K1.decode oracle).withTests cases),
    ("k1 encodings read back", (K1.encode oracle).withTests cases),
    ("k1 group law", (K1.group oracle).withTests cases),
    ("k1 ECDH", (K1.ecdh oracle).withTests cases),
    ("k1 address", (K1.address oracle).withTests cases),
    ("k1 field kernels", K1.field.withTests cases),
    ("k1 operations on bytes, as the bindings call them", (K1.exports oracle).withTests cases)]),
   ("curves: secp256r1", [
    ("r1 signs as RFC 6979", (R1.sign oracle).withTests cases),
    ("r1 verifies as SEC 1", (R1.verify oracle).withTests cases),
    ("r1 verifies a signature with x_R >= n", (R1.verifyWrapped oracle).withTests cases),
    ("r1 verifies at the edges", (R1.verifyEdges oracle).withTests cases),
    ("r1 decodes the uncompressed encoding only", (R1.decode oracle).withTests cases),
    ("r1 group law", (R1.group oracle).withTests cases),
    ("r1 verification on bytes, as the bindings call it", (R1.exports oracle).withTests cases)]),
   ("curves: alt_bn128", [
    ("bn G1 group law", (Bn.group1 oracle).withTests cases),
    ("bn G2 group law", (Bn.group2 oracle).withTests (max 1 (cases / 4))),
    ("bn twist outside the subgroup", (Bn.twist oracle special).withTests (max 1 (cases / 4))),
    ("bn pairing value", (Bn.pairingValue oracle).withTests slow),
    ("bn pairing check", (Bn.pairingChecks oracle).withTests slow)]),
   ("curves: bls12-381 arithmetic", [
    ("bls Fr and Fp are the integers mod r and p", Bls12.fields.withTests cases),
    ("bls batch inverse", Bls12.batchInverse.withTests cases),
    ("bls square root in Fp2", Bls12.sqrt2.withTests cases),
    ("bls G1 decompression and key validation", (Bls12.g1Decode oracle).withTests cases),
    ("bls G2 decompression", (Bls12.g2Decode oracle special).withTests cases),
    ("bls G1 group law", (Bls12.g1Group oracle).withTests (max 1 (cases / 4))),
    ("bls G2 group law", (Bls12.g2Group oracle).withTests (max 1 (cases / 4))),
    ("bls multi-scalar multiplication", (Bls12.msm oracle).withTests (max 1 (cases / 4))),
    ("bls pairing check", (Bls12.pairingChecks oracle).withTests (max 1 (cases / 4))),
    ("bls expand_message_xmd", (Bls12.expand oracle).withTests cases),
    ("bls hash to G2", (Bls12.hashToG2 oracle).withTests slow),
    ("bls map to curve", (Bls12.mapToCurve oracle special).withTests slow)]),
   ("curves: bls signatures", [
    ("bls secret keys", (Bls12.secretKeys oracle).withTests (max 1 (cases / 4))),
    ("bls signs", (Bls12.signs oracle).withTests slow),
    ("bls verifies", (Bls12.verifies oracle).withTests slow),
    ("bls aggregates", (Bls12.aggregates oracle).withTests slow),
    ("bls aggregate verification", (Bls12.aggregateVerifies oracle).withTests slow),
    ("bls fast aggregate verification", (Bls12.fastAggregateVerifies oracle).withTests slow),
    ("bls key generation", (Bls12.keyGens oracle).withTests cases),
    ("bls ERC-2333 derivation", (Bls12.derives oracle).withTests (max 1 (cases / 4))),
    ("bls ERC-2334 paths", Bls12.paths.withTests cases)]),
   ("curves: kzg", [
    ("kzg commitment of a blob", (KzgTest.commits setup oracle).withTests slow),
    ("kzg proof at a point and its verification", (KzgTest.proves setup oracle).withTests slow),
    ("kzg proof of a blob and its verification", (KzgTest.blobProofs setup oracle).withTests slow),
    ("kzg batch verification of blobs", (KzgTest.batches setup oracle).withTests slow),
    ("kzg cells and their proofs", (KzgTest.cells setup oracle).withTests (max 1 (cases / 50))),
    ("kzg recovery of cells", (KzgTest.recovers setup oracle).withTests (max 1 (cases / 50))),
    ("kzg batch verification of cells",
      (KzgTest.verifiesCells setup oracle).withTests (max 1 (cases / 50)))]),
   ("curves: polynomials of kzg", [
    ("poly sums, products and values", KzgPoly.arithmetic.withTests cases),
    ("poly product bound", KzgPoly.productBound.withTests (max 1 (cases / 20))),
    ("poly division", KzgPoly.division.withTests cases),
    ("poly interpolation and vanishing polynomial", KzgPoly.interpolation.withTests cases),
    ("poly bit reversal, roots of unity and cosets", KzgPoly.domains.withTests (max 1 (cases / 4))),
    ("poly FFT", KzgPoly.fft.withTests cases),
    ("poly evaluation form", KzgPoly.evaluationForm.withTests (max 1 (cases / 10))),
    ("poly of a cell", KzgPoly.cosets.withTests (max 1 (cases / 4))),
    ("poly packed indices", KzgPoly.indices.withTests cases)]),
   ("curves: xmss", [
    ("xmss verifies valid signatures only", (XmssTest.verifies oracle xmss).withTests cases),
    ("xmss codewords", (XmssTest.codewords oracle).withTests cases),
    ("xmss path to the root", (XmssTest.folds oracle).withTests cases),
    ("xmss leaf of a one-time signature", (XmssTest.otsLeaves oracle).withTests slow),
    ("xmss public parameter and subtrees", (XmssTest.subtrees oracle).withTests slow),
    ("xmss one-time signature", (XmssTest.otsSigns oracle).withTests (max 1 (cases / 200)))]),
   ("curves: vrf", [
    ("vrf verifies valid openings only", (VrfTest.verifies oracle).withTests cases),
    ("vrf secret, output and mix", (VrfTest.hashes oracle).withTests cases)]),
   ("curves: sphincs", [
    ("sphincs signs, verifies and refuses changes",
      (SphincsTest.signsAndVerifies oracle).withTests (max 1 (cases / 50))),
    ("sphincs digest fields", SphincsTest.digestFields.withTests cases)]),
   ("curves: state machines", [
    ("G1 accumulator against a scalar (StateMachine)",
      ((Machines.accumulator oracle).property (.linear 1 30)).withTests (max 1 (cases / 4))),
    ("RFC 6979 nonce generator (StateMachine)",
      ((Machines.nonces oracle).property (.linear 1 40)).withTests cases),
    ("BLS signers (Command, madhouse)",
      (Machines.signers oracle .madhouse).withTests slow),
    ("BLS signers (Command, deterministic)", Machines.signers oracle .deterministic),
    ("KZG blob store (Command, madhouse)",
      (Machines.store ⟨oracle, setup⟩ .madhouse).withTests (max 1 (cases / 50))),
    ("KZG blob store (Command, deterministic)",
      Machines.store ⟨oracle, setup⟩ .deterministic)]),
   ("curves: every parameter", [
    ("every: the two tags of the proof-of-possession scheme", (Every.tags oracle).withTests 1),
    ("every: core BLS operations under any tag", (Every.coreAnyTag oracle).withTests slow),
    ("every: a signature is no proof of possession",
      Every.separation.withTests (max 1 (cases / 50))),
    ("every: any count of field elements", Every.fieldElements.withTests (max 1 (cases / 4))),
    ("every: the sign of a coordinate", Every.signs.withTests cases),
    ("every: powers in any modulus", Every.powers.withTests cases),
    ("every: the cofactor of G2 is h_eff", (Every.cofactor oracle).withTests slow),
    ("every: a child key of any parent", (Every.childKeys oracle).withTests (max 1 (cases / 4))),
    ("every: all 128 cells of a blob", (Every.everyCell setup oracle).withTests
      (max 1 (cases / 250))),
    ("every: the coset of every cell index", Every.everyCoset.withTests 1),
    ("every: the evaluation form over any domain", Every.anyDomain.withTests cases),
    ("every: the FFT of any length", Every.anyFft.withTests (max 1 (cases / 4))),
    ("every: the FFT in G1", (Every.fftInG1 oracle).withTests slow),
    ("every: addresses of leanXMSS", (Every.xmssAddresses oracle).withTests cases),
    ("every: paths of a small subtree of leanXMSS", (Every.xmssPaths oracle).withTests slow),
    ("every: codewords of leanSPHINCS", (Every.sphincsCodewords oracle).withTests cases),
    ("every: addresses of leanSPHINCS", (Every.sphincsAddresses oracle).withTests cases)])]

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  -- A word among the arguments keeps the groups whose name holds it.
  let only := args.filter fun arg => arg.toNat?.isNone
  let select ← Selection.fromEnv
  let oracle ← Oracle.start "curves"
  let .ok setup := EthLib.Cryptography.Kzg.TrustedSetup.ofHex
    | throw (IO.userError "the embedded trusted setup does not decode")
  let xmss ← XmssTest.loadVectors oracle
  let special ← Specials.load oracle
  -- A case of KZG or of leanSPHINCS takes seconds, and each shrink runs one more.
  let slowNames := ["kzg", "KZG", "128 cells", "sphincs signs"]
  let bounded (name : String) (p : Property IO) : Property IO :=
    if slowNames.any fun word => (name.splitOn word).length > 1 then p.withShrinks 40 else p
  let all := (groups oracle setup xmss special cases).map fun (group, properties) =>
    (group, properties.map fun (name, p) => (name, bounded name p))
  -- A minimum for a name that no property has would be asked of nothing.
  let names := all.flatMap fun (_, properties) => properties.map (·.1)
  for (name, _) in minimums do
    unless names.contains name do throw (IO.userError s!"no property is named {name}")
  let mut failed := false
  for (name, properties) in all do
    if only.isEmpty || only.any fun word => (name.splitOn word).length > 1 then
      let properties := properties.map fun (name, p) =>
        (name, withMinimums cases ((minimums.lookup name).getD []) p)
      unless ← checkGroup name properties select do failed := true
  pure (if failed then 1 else 0)

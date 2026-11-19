import Property.Curves.Bls
import EthLib.Cryptography.Kzg

/-!
# KZG against c-kzg-4844

The blob operations of EIP-4844 and the cell operations of EIP-7594, on the trusted setup that
EthLib embeds, which the oracle reads from the same file.
A blob is described by a few numbers, so that a failing case shrinks to a readable one.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.KzgTest

open Kzg Bls12

def r : Nat := Bls.Fr.modulus

/-- A blob, as the rule that fills it and the elements set afterwards. -/
structure BlobSpec where
  /-- `0` fills with zero, `1` with `seed`, and any other with a spread of `seed`. -/
  mode : Nat
  seed : Nat
  /-- Elements set by index; a value of `r` or more makes the blob invalid. -/
  overrides : List (Nat × Nat)
  deriving Repr, BEq, Inhabited

/-- Element `i` of a blob. -/
def BlobSpec.element (spec : BlobSpec) (i : Nat) : Nat :=
  match spec.overrides.find? (·.1 == i) with
  | some (_, value) => value
  | none =>
    match spec.mode with
    | 0 => 0
    | 1 => spec.seed % r
    | _ => (spec.seed + i) *
        (spec.seed + i + 1) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95 % r

/-- The 131072 bytes of a blob. -/
def BlobSpec.blob (spec : BlobSpec) : Blob :=
  let elements := Array.ofFn (n := 4096) fun i => spec.element i.val
  Vector.ofFn fun i => UInt8.ofNat (elements[i.val / 32]! >>> (8 * (31 - i.val % 32)))

/-- A blob: zero, constant or spread, with a few elements at the edges of the field. -/
def genBlob (invalid : Bool := true) : Gen BlobSpec := do
  let mode ← Gen.frequency [(1, pure 0), (1, pure 1), (3, pure 2)]
  let seed ← genNear r
  let index := Gen.frequency [(1, pure 0), (1, pure 1), (1, pure 4095), (2, Gen.nat
      (.constant 0 4095))]
  let value := if invalid then genNear r else (· % r) <$> genNear r
  let overrides ← Gen.frequency [(2, pure []), (3, Gen.list (.linear 0 3) (Gen.zip index value))]
  pure ⟨mode, seed, overrides⟩

def blobHex (spec : BlobSpec) : String := hexVec spec.blob

/-- A point where a polynomial is opened: a root of unity of the domain, an edge of the
field, or any number below `2 ^ 256`. -/
def genZ : Gen Nat :=
  Gen.frequency [
    (3, (fun j => modPow r 7 ((r - 1) / 4096 * j)) <$> Gen.nat (.constant 0 4095)),
    (1, (fun j => modPow r 7 ((r - 1) / 8192 * j)) <$> Gen.nat (.constant 0 8191)),
    (4, genNear r)]

/-- 48 bytes near a commitment or a proof: itself, the point at infinity, a point of the
curve that may lie outside the subgroup, its negative, or one bit changed. -/
def genBad48 (good : Vector UInt8 48) : Gen (Vector UInt8 48) :=
  Gen.frequency [
    (5, pure good),
    (1, pure Bls.G1.infinityBytes),
    (1, Bls.G1.compress <$> genG1),
    (1, flipVec good <$> Gen.nat (.constant 0 383)),
    (1, pure (Bls.G1.compress (Bls.G1.neg ((Bls.G1.uncompress good).toOption.getD Bls.G1.zero))))]

/-- An answer of a verification: `1`, `0`, or `error`. -/
def verdict (result : Except KzgError Bool) : String :=
  match result with
  | .ok true => "1"
  | .ok false => "0"
  | .error _ => "error"

/-- The commitment of a blob is c-kzg's, a blob with an element of `r` or more is refused,
and the versioned hash of the commitment is that of EIP-4844. -/
def commits (setup : TrustedSetup) (oracle : Oracle) : Property IO := propertyM do
  let spec ← forAll genBlob
  pure do
    let got := match blobToKzgCommitment setup spec.blob with
      | .ok c => hexVec c
      | .error _ => "error"
    got === (← oracle.ask ["kzgcommit", blobHex spec])
    match blobToKzgCommitment setup spec.blob with
    | .ok c => hexVec (kzgCommitmentToVersionedHash c) ===
        (← oracle.ask ["versionedhash", hexVec c])
    | .error _ => pure ()

/-- A proof at a point and its value are c-kzg's, and verification agrees on the proof
changed at one place. -/
def proves (setup : TrustedSetup) (oracle : Oracle) : Property IO := propertyM do
  let spec ← forAll (genBlob false)
  let z ← forAll genZ
  let blob := spec.blob
  let (commitment, proof, y) := match blobToKzgCommitment setup blob,
      computeKzgProof setup blob (vec32 (z % r)) with
    | .ok c, .ok (proof, y) => (c, proof, beNat ⟨y.toArray⟩)
    | _, _ => (Bls.G1.infinityBytes, Bls.G1.infinityBytes, 0)
  let commitment' ← forAllWith hexVec (genBad48 commitment)
  let proof' ← forAllWith hexVec (genBad48 proof)
  let y' ← forAll (Gen.frequency [(5, pure y), (1, pure ((y + 1) % r)), (1, genNear r)])
  let z' ← forAll (Gen.frequency [(5, pure (z % r)), (1, pure z), (1, genZ)])
  pure do
    let got := match computeKzgProof setup blob (vec32 z) with
      | .ok (proof, y) => s!"{hexVec proof} {hexVec y}"
      | .error _ => "error"
    got === (← oracle.ask ["kzgproof", blobHex spec, hexVec (vec32 z)])
    verdict (verifyKzgProof setup commitment' (vec32 z') (vec32 y') proof') === (← oracle.ask
      ["kzgverify", hexVec commitment', hexVec (vec32 z'), hexVec (vec32 y'), hexVec proof'])

/-- A blob with its commitment and proof, each possibly changed. -/
structure Triple where
  spec : BlobSpec
  commitment : Vector UInt8 48
  proof : Vector UInt8 48

instance : Repr Triple := ⟨fun t _ => repr (t.spec, hexVec t.commitment, hexVec t.proof)⟩

def genTriple (setup : TrustedSetup) : Gen Triple := do
  let spec ← Gen.frequency [(6, genBlob false), (1, genBlob)]
  let blob := spec.blob
  let commitment := (blobToKzgCommitment setup blob).toOption.getD Bls.G1.infinityBytes
  let proof := (computeBlobKzgProof setup blob commitment).toOption.getD Bls.G1.infinityBytes
  let commitment ← Gen.frequency [(6, pure commitment), (1, genBad48 commitment)]
  let proof ← Gen.frequency [(6, pure proof), (1, genBad48 proof)]
  pure ⟨spec, commitment, proof⟩

/-- The proof of a blob against a commitment is c-kzg's, and so is its verification. -/
def blobProofs (setup : TrustedSetup) (oracle : Oracle) : Property IO := propertyM do
  let t ← forAll (genTriple setup)
  pure do
    let blob := t.spec.blob
    let got := match computeBlobKzgProof setup blob t.commitment with
      | .ok proof => hexVec proof
      | .error _ => "error"
    got === (← oracle.ask ["kzgblobproof", blobHex t.spec, hexVec t.commitment])
    verdict (verifyBlobKzgProof setup blob t.commitment t.proof) === (← oracle.ask
      ["kzgverifyblob", blobHex t.spec, hexVec t.commitment, hexVec t.proof])

/-- The batch verification of blobs is c-kzg's, on lists of any lengths. -/
def batches (setup : TrustedSetup) (oracle : Oracle) : Property IO := propertyM do
  let triples ← forAll (Gen.list (.linear 0 3) (genTriple setup))
  let (dropC, dropP) ← forAll (Gen.zip (Gen.frequency [(6, pure 0), (1, pure 1)])
    (Gen.frequency [(6, pure 0), (1, pure 1)]))
  pure do
    let blobs := triples.map (·.spec.blob)
    let commitments := (triples.map (·.commitment)).drop dropC
    let proofs := (triples.map (·.proof)).drop dropP
    verdict (verifyBlobKzgProofBatch setup blobs.toArray commitments.toArray proofs.toArray)
      === (← oracle.ask ["kzgverifybatch", listWord (blobs.map hexVec),
        listWord (commitments.map hexVec), listWord (proofs.map hexVec)])

/-- The SHA-256 of byte vectors in a row, as the oracle shortens a long answer. -/
def digest {n : Nat} (parts : Array (Vector UInt8 n)) : String :=
  hex (Hash.Sha256.hash (parts.foldl (fun acc part => acc ++ ⟨part.toArray⟩) ByteArray.empty))

/-- The cells of a blob and their proofs are c-kzg's. -/
def cells (setup : TrustedSetup) (oracle : Oracle) : Property IO := propertyM do
  let spec ← forAll genBlob
  pure do
    let expected ← oracle.ask ["kzgcells", blobHex spec]
    match computeCellsAndKzgProofs setup spec.blob, computeCells spec.blob with
    | .ok (cells, proofs), .ok only =>
      s!"{digest cells} {digest proofs}" === expected
      ensure (only == cells) "the cells alone differ from the cells with proofs"
    | .error _, .error _ => expected === "error"
    | _, _ => failWith "the two cell computations disagree on whether the blob is valid"

/-- The indices of the cells handed to recovery: half or more in order, or a near miss. -/
def genIndices : Gen (List Nat) := do
  let all := List.range 128
  let chosen ← Gen.frequency [
    (3, Gen.subsequence all),
    (2, (fun k => all.drop k |>.take 64) <$> Gen.nat (.constant 0 64)),
    (1, pure (all.filter (· % 2 == 1))),
    (1, pure all),
    (1, (fun k => all.take k) <$> Gen.nat (.constant 60 66))]
  Gen.frequency [
    (8, pure chosen),
    (1, Gen.shuffle chosen),
    (1, pure (chosen ++ chosen.take 1)),
    (1, pure (chosen.dropLast ++ [128])),
    (1, pure (chosen.take 1 ++ chosen))]

/-- Recovery from half of the cells gives the cells and proofs of c-kzg, and refuses what
c-kzg refuses: too few cells, an index out of range or out of order, an invalid cell. -/
def recovers (setup : TrustedSetup) (oracle : Oracle) : Property IO := propertyM do
  let spec ← forAll (genBlob false)
  let indices ← forAll genIndices
  let (spoil, value) ← forAll (Gen.zip (Gen.frequency [(6, pure none),
    (1, some <$> Gen.nat (.constant 0 63))]) (genNear r))
  let fewer ← forAll (Gen.frequency [(8, pure 0), (1, pure 1)])
  pure do
    let .ok (all, _) := computeCellsAndKzgProofs setup spec.blob | failWith "no cells"
    let chosen := indices.map fun i => all[i % 128]!
    -- One element of the first cell is replaced, by a number that may not be canonical.
    let chosen := match spoil, chosen with
      | some at_, first :: rest =>
        (Vector.ofFn fun i : Fin Constants.BYTES_PER_CELL =>
          if i.val / 32 == at_ then (vec32 value)[i.val % 32]! else first[i.val]!) :: rest
      | _, cs => cs
    let chosen := chosen.drop fewer
    let got := match recoverCellsAndKzgProofs setup indices.toArray chosen.toArray with
      | .ok (cells, proofs) => s!"{digest cells} {digest proofs}"
      | .error _ => "error"
    let expected ← oracle.ask ["kzgrecover", listWord (indices.map toString),
      listWord (chosen.map hexVec)]
    -- Given all 128 cells, c-kzg copies them, where the specification interpolates them again.
    -- The two differ on cells that are not the values of one polynomial, so only the proofs
    -- are compared there.
    if spoil.isSome && indices.length == 128 && got != "error" && expected != "error" then
      (words got).drop 1 === (words expected).drop 1
    else got === expected

/-- The batch verification of cell proofs is c-kzg's, on cells of up to two blobs with an
index, a cell, a proof or a commitment changed. -/
def verifiesCells (setup : TrustedSetup) (oracle : Oracle) : Property IO := propertyM do
  let (specA, specB) ← forAll (Gen.zip (genBlob false) (genBlob false))
  let picks ← forAll (Gen.list (.linear 0 5) (Gen.zip Gen.bool (Gen.frequency [
    (1, pure 0), (1, pure 127), (3, Gen.nat (.constant 0 127))])))
  let change ← forAll (Gen.frequency [(5, pure 0), (1, pure 1), (1, pure 2), (1, pure 3),
    (1, pure 4), (1, pure 5), (1, pure 6), (1, pure 7)])
  let value ← forAll (genNear r)
  let bad ← forAllWith hexVec (genBad48 Bls.G1.infinityBytes)
  pure do
    let side (spec : BlobSpec) := do
      let .ok c := blobToKzgCommitment setup spec.blob | failWith "no commitment"
      let .ok (cells, proofs) := computeCellsAndKzgProofs setup spec.blob | failWith "no cells"
      pure (c, cells, proofs)
    let a ← side specA
    let b ← side specB
    let rows := picks.map fun (second, i) =>
      let (c, cells, proofs) := if second then b else a
      (c, i, cells[i]!, proofs[i]!)
    let commitments := rows.map (·.1)
    let indices := rows.map (·.2.1)
    let cellList := rows.map (·.2.2.1)
    let proofs := rows.map (·.2.2.2)
    -- One change, at the first row.
    let indices := match change, indices with
      | 1, i :: rest => (i + 1) % 128 :: rest
      | 2, _ :: rest => 128 :: rest
      | _, is => is
    let cellList := match change, cellList with
      | 3, first :: rest =>
        (Vector.ofFn fun i : Fin Constants.BYTES_PER_CELL =>
          if i.val / 32 == 5 then (vec32 value)[i.val % 32]! else first[i.val]!) :: rest
      | _, cs => cs
    let proofs := match change, proofs with
      | 4, _ :: rest => bad :: rest
      | 5, ps => ps.drop 1
      | _, ps => ps
    let commitments := match change, commitments with
      | 6, _ :: rest => bad :: rest
      | 7, cs => cs.reverse
      | _, cs => cs
    verdict (verifyCellKzgProofBatch setup commitments.toArray indices.toArray cellList.toArray
      proofs.toArray) === (← oracle.ask ["kzgverifycells", listWord (commitments.map hexVec),
        listWord (indices.map toString), listWord (cellList.map hexVec),
        listWord (proofs.map hexVec)])

end CurvesProperty.KzgTest

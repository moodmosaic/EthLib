import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Classes
import Property.Serialization.Near
import Property.Serialization.Merkle
import Property.Serialization.Rooted
import Property.Serialization.Streams
import Property.Serialization.Misc
import Property.Serialization.Extra
import Property.Serialization.Params
import Property.Serialization.Shapes
import Property.Serialization.Formats
import Property.Serialization.Minimums

/-!
# The serialization layer, on generated inputs

    lake exe serialization-property            # 100 cases of each
    lake exe serialization-property 1000
    HEDGEHOG_ONLY="RLP,DER" lake exe serialization-property 1000

Every property names the classes of its cases, and a report lists their shares.

From 1,000 cases on, each class must reach the minimum that `Minimums.lean` gives it.

The properties of the last group state what EthLib does not do: each must fail.
-/

open Hedgehog Support EthLib.Serialization

namespace SerializationProperty

/-! ## RLP -/

/-- The encoder writes the bytes of the reference. -/
def rlpEncode (oracle : Oracle) : Property IO := propertyM do
  let item ← forAllWith itemText genItem
  pure do
    labelItem item
    let expected ← oracle.ask ["rlpenc", itemText item]
    match Rlp.encode item with
    | .ok bytes => hex bytes === expected
    | .error _ => failWith "no encoding"

/-- The decoder accepts what the strict references accept, and reads the same item. -/
def rlpDecode (oracle : Oracle) : Property IO := propertyM do
  let item ← forAllWith itemText genItem
  let valid := (Rlp.encode item).toOption.getD .empty
  let input ← forAllWith hex
    (Gen.frequency [(3, genMutation valid), (3, genRlpNear valid), (5, genHeaded),
      (1, genBytes (.linear 0 12))])
  pure do
    classifyOne "input" inputForms (inputForm input)
    classifyOne "verdict" rlpVerdicts (rlpVerdict (Rlp.decode input))
    classify "the encoding of an item, unchanged" (input == valid)
    let expected ← oracle.ask ["rlpdec", hex input]
    match Rlp.decode input with
    | .ok got => itemText got === expected
    | .error _ => expected === "error"

/-- The scalar decoder accepts the canonical scalars only. -/
def rlpScalar (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll (Gen.frequency [(3, genNatBits 72), (1, Gen.nat (.constant 0 200))])
  let valid := (Rlp.encode (.scalar n)).toOption.getD .empty
  let encoded (item : Rlp.Item) : ByteArray := (Rlp.encode item).toOption.getD .empty
  let input ← forAllWith hex (Gen.frequency [(2, pure valid), (3, genMutation valid),
    (1, (fun b => encoded (.bytes b)) <$> genBytes (.linear 0 4)),
    -- A scalar behind a zero byte, a list, and the forms the encoder never writes.
    (2, (fun zeros => encoded (.bytes (⟨Array.replicate zeros 0⟩ ++ Rlp.bigEndian n))) <$>
      Gen.nat (.constant 1 2)),
    (2, encoded <$> genItemOf 1),
    (2, genRlpNear valid)])
  pure do
    classifyOne "verdict" (rlpVerdicts ++ ["leading zero in a scalar", "a list as a scalar"])
      (rlpVerdict (Rlp.decodeScalar input))
    classifyOne "scalar" ["none", "0", "1 to 127", "128 to 2^64 - 1", "2^64 or more"]
      (match Rlp.decodeScalar input with
        | .error _ => "none"
        | .ok n => if n == 0 then "0" else if n < 128 then "1 to 127"
          else if n < 2 ^ 64 then "128 to 2^64 - 1" else "2^64 or more")
    let expected ← oracle.ask ["rlpint", hex input]
    match Rlp.decodeScalar input with
    | .ok got => toString got === expected
    | .error _ => expected === "error"

/-! ## SSZ -/

/-- A generated type is legal, and its value has the bytes and the root of the reference. -/
def sszEncode (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  pure do
    labelType shape
    labelValue shape value
    ensure (shape.wellFormed.toOption.isSome) "the type is not well formed"
    encodedText shape value === (← oracle.ask ["sszenc", typeText shape, valueText value])

/-- The decoder accepts what the reference accepts, and reads the same value. -/
def sszDecode (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let valid := (Ssz.serialize shape value).toOption.getD #[]
  let input ← forAllWith hex (genNearEncoding shape ⟨valid⟩)
  pure do
    -- The generator cuts a valid encoding in parts by itself: they must join to it again.
    let kinds := partKinds shape ⟨valid⟩
    ensure (kinds.isEmpty || hex (joinParts kinds (splitParts kinds ⟨valid⟩)) == hex ⟨valid⟩)
      "the parts of the valid encoding do not join to it"
    labelOutcome decodeReasons (Ssz.deserialize shape input.data)
    classify "the encoding of a value, unchanged" (input.data == valid)
    classifyOne "root" constructors (constructorOf shape)
    ensure (match Ssz.deserialize shape input.data with
      | .error e => (rootReasons shape).contains e.reason
      | .ok _ => true) "a refusal that the parts of the type cannot give"
    let expected ← oracle.ask ["sszdec", typeText shape, hex input]
    match Ssz.deserialize shape input.data with
    | .ok got =>
      annotate s!"EthLib read {valueText got}"
      encodedText shape got === expected
    | .error e =>
      annotate s!"the specification: {expected}"
      refusal e === faultOf expected

/-- The properties of a group, with the minimums of the table when the run is long enough. -/
def withMinimums (cases : Nat) (properties : List (String × Property IO)) :
    List (String × Property IO) :=
  if cases < 1000 then properties
  else properties.map fun (name, property) =>
    (name, covering ((minimums.lookup name).getD []) property)

end SerializationProperty

open SerializationProperty in
def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "serialization"
  let select ← Selection.fromEnv
  let ok ← checkGroup "serialization" (withMinimums cases [
    ("RLP encodes as the reference", (rlpEncode oracle).withTests cases),
    ("RLP decodes the canonical encodings only", (rlpDecode oracle).withTests cases),
    ("RLP scalars are canonical", (rlpScalar oracle).withTests cases),
    ("SSZ serializes and roots as the reference", (sszEncode oracle).withTests cases),
    ("SSZ deserializes what the reference does", (sszDecode oracle).withTests cases),
    ("SSZ sizes are within the bounds of the type", (sizeBounds oracle).withTests cases),
    ("SSZ defaults are the reference's", (defaults oracle).withTests cases),
    ("SSZ compatibility is the reference's", (compatible oracle).withTests cases),
    ("SSZ paths have the index of the specification", (gindexOfPath oracle).withTests cases),
    ("SSZ nodes are those of the reference tree", (nodeAtGindex oracle).withTests cases),
    ("SSZ proofs verify, and only for their leaf", proofVerifies.withTests cases),
    ("SSZ helper indices are the specification's", (helperIndices oracle).withTests cases),
    ("SSZ multiproofs rebuild the specification's root", (multiproofRoot oracle).withTests cases),
    ("SSZ branches by depth and index", (branchByDepth oracle).withTests cases),
    ("SSZ documents read back under every spelling", sszJsonTrip.withTests cases),
    ("SSZ documents are those of the mapping", sszJsonModel.withTests cases),
    ("SSZ documents hold integers as digits", sszJsonUint.withTests cases),
    ("typed SSZ: a container of every kind of field", (typedCodec oracle Record).withTests cases),
    ("typed SSZ: a progressive container with fork lists",
        (typedCodec oracle Sparse).withTests cases),
    ("typed SSZ: a container of fixed size", (typedCodec oracle Fixed).withTests cases),
    ("typed RLP reads back within its range", rlpCodec.withTests cases),
    ("DER reads one tag, length and value", (derRead oracle).withTests cases),
    ("DER integers are minimal", (derInteger oracle).withTests cases),
    ("DER signatures read as the reference reads them", (derSignature oracle).withTests cases),
    ("DER values are valid as X.690 says", (derValidate oracle).withTests cases),
    ("JSON-RPC readers accept the patterns of the schema", (rpcRead oracle).withTests cases),
    ("JSON-RPC writers write the patterns", (rpcWrite oracle).withTests cases),
    ("JSON-RPC integers are the integral numbers", (rpcInteger oracle).withTests cases),
    ("JSON-RPC error objects read back", rpcError.withTests cases),
    ("RLP decodes inputs at the edge of each form", (rlpPrefixed oracle).withTests cases),
    ("SSZ refuses a declaration that breaks a rule", illegalDeclarations.withTests cases),
    ("SSZ layouts are at most 256 positions wide", widestLayout.withTests (min cases 255)),
    ("SSZ limits of progressive shapes bound the count only", progressiveLimit.withTests cases),
    ("SSZ lists far below their limit", (tallLists oracle).withTests cases),
    ("SSZ multiproofs of a value rebuild its root", (multiproofOfValue oracle).withTests cases),
    ("SSZ documents near a valid one read as the specification reads them",
        (sszJsonNear oracle).withTests cases),
    ("SSZ documents are those the specification writes", (sszJsonCited oracle).withTests cases),
    ("SSZ documents under the byte alias", (sszJsonAlias oracle).withTests cases),
    ("SSZ declarations are legal as the specification says", (declarations oracle).withTests cases),
    ("SSZ proof requests are answered as the specification does",
        (proofRequests oracle).withTests cases),
    ("typed SSZ: a field before its fork", (typedCodec oracle (Staged .fusaka)).withTests cases),
    ("typed SSZ: a field from its fork on",
        (typedCodec oracle (Staged .glamsterdam)).withTests cases)]) select
  -- A sequence is many cases: the state machines run a fifth as many sequences.
  let runs := max 20 (cases / 5)
  let word := "[\"uint\",8]"
  let pair := "[\"cont\",[\"f0\",\"f1\"],[[\"uint\",8],[\"uint\",2]]]"
  let machines ← checkGroup "serialization: state machines" (withMinimums cases [
    ("StateMachine: List[uint64, 40] keeps its tree",
      (listProperty oracle true UInt64 40 word 50).withTests runs),
    ("StateMachine: ProgressiveList[uint64] keeps its tree",
      (listProperty oracle false UInt64 0 word 50).withTests runs),
    ("StateMachine: List[uint16, 100] keeps its tree",
      (listProperty oracle true UInt16 100 "[\"uint\",2]" 50).withTests runs),
    ("StateMachine: ProgressiveList[boolean] keeps its tree",
      (listProperty oracle false Bool 0 "[\"bool\"]" 50).withTests runs),
    ("StateMachine: List[uint256, 20] keeps its tree",
      (listProperty oracle true EthLib.Base.U256 20 "[\"uint\",32]" 40).withTests runs),
    ("StateMachine: ProgressiveList[uint256] keeps its tree",
      (listProperty oracle false EthLib.Base.U256 0 "[\"uint\",32]" 40).withTests runs),
    ("StateMachine: List[Bytes32, 9] keeps its tree",
      (listProperty oracle true (Vector UInt8 32) 9 "[\"bvec\",32]" 40).withTests runs),
    ("StateMachine: ProgressiveList[Bytes32] keeps its tree",
      (listProperty oracle false (Vector UInt8 32) 0 "[\"bvec\",32]" 40).withTests runs),
    ("StateMachine: List[Pair, 6] keeps its tree",
      (listProperty oracle true Pair 6 pair 40).withTests runs),
    ("StateMachine: ProgressiveList[Pair] keeps its tree",
      (listProperty oracle false Pair 0 pair 40).withTests runs),
    ("StateMachine: an RLP stream is read in the order written",
      (streamMachine.property (.linear 1 40)).withTests cases),
    ("Command, madhouse: rooted vectors keep their trees", (vectorScenario oracle).withTests cases),
    ("Command, madhouse: an e2store file grows by records", (fileScenario oracle).withTests cases),
    ("Command, in order: an e2store file as a writer makes it", fileScript oracle)]) select
  let params ← checkGroup "serialization: every parameter" (withMinimums cases [
    ("RLP prefixes of every length", (rlpLengthPrefix oracle).withTests cases),
    ("RLP reads a length on every count of bytes", (rlpReadPrefix oracle).withTests cases),
    ("RLP reads an item between every two positions", (rlpDecodeAt oracle).withTests cases),
    ("RLP numbers of every size in base 256", (rlpBigEndian oracle).withTests cases),
    ("RLP scalars below every power of two", rlpScalarBelow.lift.withTests cases),
    ("typed RLP: byte strings of every length, fields of every fork",
        rlpCodecShapes.lift.withTests cases),
    ("SSZ merkleizes under every capacity and hasher",
        (merkleizeLimits oracle).withTests cases),
    ("SSZ progressive spines from every level",
        (merkleizeProgressiveLevels oracle).withTests cases),
    ("SSZ zero subtrees of every depth", (zeroSubtrees oracle).withTests cases),
    ("SSZ integers of every width", (sszUintWidths oracle).withTests cases),
    ("SSZ slots and spans of every layout", sszSlots.lift.withTests cases),
    ("SSZ values of every near count fit or do not", (sszFits oracle).withTests cases),
    ("SSZ values of every type are zero or are not", (sszIsZero oracle).withTests cases),
    ("SSZ roots under every hasher", (sszHasher oracle).withTests cases),
    ("SSZ roots with every budget of nesting", sszBudget.lift.withTests cases),
    -- Twelve element types by ten collections by twelve lengths: three times the cases.
    ("typed SSZ: collections of every element and length",
        (typedCollections oracle).withTests (3 * cases)),
    ("typed SSZ: texts of every limit", (typedString oracle).withTests cases),
    ("typed SSZ: every pair of forks", (typedForks oracle).withTests (3 * cases)),
    ("SSZ generalized indices of every spine, path and join",
        (gindexArithmetic oracle).withTests cases),
    ("SSZ chunk positions of every element", (chunkPositions oracle).withTests cases),
    ("SSZ branches under every hash and depth", (branchEveryHash oracle).withTests cases),
    ("DER reads a value of every tag", (derEveryTag oracle).withTests cases),
    ("DER validates a value of every tag", (derValidateEveryTag oracle).withTests cases),
    ("e2store headers of every type and length", (e2sHeaders oracle).withTests cases),
    ("e2store index records of every count", (e2sIndex oracle).withTests cases),
    ("JSON-RPC readers at every width", (rpcWidths oracle).withTests cases),
    ("JSON-RPC readers of every structure", (rpcStructure oracle).withTests cases)]) select
  let bytes32 := "[\"bvec\",32]"
  let short := "[\"list\",[\"uint\",2],3]"
  let rooted ← checkGroup "serialization: rooted values at every length and fork"
    (withMinimums cases [
    ("rooted vectors of every length: boolean",
      (vectorEveryLength oracle Bool "[\"bool\"]").withTests cases),
    ("rooted vectors of every length: uint8",
      (vectorEveryLength oracle UInt8 "[\"uint\",1]").withTests cases),
    ("rooted vectors of every length: uint16",
      (vectorEveryLength oracle UInt16 "[\"uint\",2]").withTests cases),
    ("rooted vectors of every length: uint32",
      (vectorEveryLength oracle UInt32 "[\"uint\",4]").withTests cases),
    ("rooted vectors of every length: uint64",
      (vectorEveryLength oracle UInt64 word).withTests cases),
    ("rooted vectors of every length: uint128",
      (vectorEveryLength oracle (BitVec 128) "[\"uint\",16]").withTests cases),
    ("rooted vectors of every length: uint256",
      (vectorEveryLength oracle EthLib.Base.U256 "[\"uint\",32]" 65).withTests cases),
    ("rooted vectors of every length: Bytes32",
      (vectorEveryLength oracle (Vector UInt8 32) bytes32 65).withTests cases),
    ("rooted vectors of every length: a container",
      (vectorEveryLength oracle Pair pair 65).withTests cases),
    ("rooted vectors of every length: a list",
      (vectorEveryLength oracle (Ssz.SszList UInt16 3) short 65).withTests cases),
    ("rooted lists at every pair of forks: boolean",
      (listEveryFork oracle Bool "[\"bool\"]").withTests runs),
    ("rooted lists at every pair of forks: uint8",
      (listEveryFork oracle UInt8 "[\"uint\",1]").withTests runs),
    ("rooted lists at every pair of forks: uint64",
      (listEveryFork oracle UInt64 word).withTests runs),
    ("rooted lists at every pair of forks: uint256",
      (listEveryFork oracle EthLib.Base.U256 "[\"uint\",32]").withTests runs),
    ("rooted lists at every pair of forks: Bytes32",
      (listEveryFork oracle (Vector UInt8 32) bytes32).withTests runs),
    ("rooted lists at every pair of forks: a container",
      (listEveryFork oracle Pair pair).withTests runs),
    ("rooted lists at every pair of forks: a list",
      (listEveryFork oracle (Ssz.SszList UInt16 3) short).withTests runs)]) select
  -- What follows states what EthLib does not do: each must fail with a counterexample.
  let findings ← checkGroup "serialization: findings" [
    ("OPEN: a branch longer than its depth is valid as phase0 says",
      branchLongerThanDepth oracle)] select (mustFail := true)
  pure (if ok && machines && params && rooted && findings then 0 else 1)

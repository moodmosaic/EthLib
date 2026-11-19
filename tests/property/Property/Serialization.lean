import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Merkle
import Property.Serialization.Rooted
import Property.Serialization.Streams
import Property.Serialization.Misc
import Property.Serialization.Extra

/-!
# The serialization layer, on generated inputs

    lake exe serialization-property            # 100 cases of each
    lake exe serialization-property 1000
-/

open Hedgehog Support EthLib.Serialization

namespace SerializationProperty

/-! ## RLP -/

/-- The encoder writes the bytes of the reference. -/
def rlpEncode (oracle : Oracle) : Property IO := propertyM do
  let item ← forAllWith itemText genItem
  pure do
    let expected ← oracle.ask ["rlpenc", itemText item]
    match Rlp.encode item with
    | .ok bytes => hex bytes === expected
    | .error _ => failWith "no encoding"

/-- The decoder accepts what the strict references accept, and reads the same item. -/
def rlpDecode (oracle : Oracle) : Property IO := propertyM do
  let item ← forAllWith itemText genItem
  let valid := (Rlp.encode item).toOption.getD .empty
  let input ← forAllWith hex
    (Gen.frequency [(4, genMutation valid), (1, genBytes (.linear 0 12))])
  pure do
    let expected ← oracle.ask ["rlpdec", hex input]
    match Rlp.decode input with
    | .ok got => itemText got === expected
    | .error _ => expected === "error"

/-- The scalar decoder accepts the canonical scalars only. -/
def rlpScalar (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll (genNatBits 72)
  let valid := (Rlp.encode (.scalar n)).toOption.getD .empty
  let input ← forAllWith hex (Gen.frequency [(1, pure valid), (3, genMutation valid),
    (1, (fun b => (Rlp.encode (.bytes b)).toOption.getD .empty) <$> genBytes (.linear 0 4))])
  pure do
    let expected ← oracle.ask ["rlpint", hex input]
    match Rlp.decodeScalar input with
    | .ok got => toString got === expected
    | .error _ => expected === "error"

/-! ## SSZ -/

/-- A generated type is legal, and its value has the bytes and the root of the reference. -/
def sszEncode (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  pure do
    ensure (shape.wellFormed.toOption.isSome) "the type is not well formed"
    encodedText shape value === (← oracle.ask ["sszenc", typeText shape, valueText value])

/-- The decoder accepts what the reference accepts, and reads the same value. -/
def sszDecode (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let valid := (Ssz.serialize shape value).toOption.getD #[]
  let input ← forAllWith hex (genMutation ⟨valid⟩)
  pure do
    let expected ← oracle.ask ["sszdec", typeText shape, hex input]
    match Ssz.deserialize shape input.data with
    | .ok got =>
      annotate s!"EthLib read {valueText got}"
      encodedText shape got === expected
    | .error e =>
      annotate s!"the specification: {expected}"
      refusal e === faultOf expected

end SerializationProperty

open SerializationProperty in
def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "serialization"
  let ok ← checkGroup "serialization" [
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
        (typedCodec oracle (Staged .glamsterdam)).withTests cases)]
  -- A sequence is many cases: the state machines run a fifth as many sequences.
  let runs := max 20 (cases / 5)
  let word := "[\"uint\",8]"
  let pair := "[\"cont\",[\"f0\",\"f1\"],[[\"uint\",8],[\"uint\",2]]]"
  let machines ← checkGroup "serialization: state machines" [
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
    ("Command, in order: an e2store file as a writer makes it", fileScript oracle)]
  pure (if ok && machines then 0 else 1)

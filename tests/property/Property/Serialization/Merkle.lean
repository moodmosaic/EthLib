import Hedgehog
import Support
import Property.Serialization.Common

/-!
# SSZ trees: nodes, generalized indices, proofs, and the rules of a declaration
-/

open Hedgehog Support EthLib.Serialization

namespace SerializationProperty

open Ssz in
/-- A path as JSON: a number for a position, a word for a mixed-in word. -/
def pathText (path : List PathStep) : String :=
  jsonArray (path.map fun
    | .position index => toString index
    | .length => "\"len\""
    | .activeFields => "\"active\""
    | .selector => "\"selector\"")

instance : Inhabited (Gen (List Ssz.PathStep)) := ⟨pure []⟩

open Ssz in
/-- A path through a type: mostly steps the type has, now and then one it lacks. -/
partial def genPath (shape : Desc) : Gen (List PathStep) :=
  let next (child : Desc) (step : PathStep) : Gen (List PathStep) := (step :: ·) <$> genPath child
  let word (step : PathStep) : Gen (List PathStep) :=
    Gen.frequency [(9, pure [step]), (1, pure [step, .position 0])]
  let stray : Gen (List PathStep) :=
    (fun step => [step]) <$> Gen.element [.length, .activeFields, .selector, .position 0]
  let element (child : Desc) (count : Option Nat) : Gen (List PathStep) := do
    let top := count.getD 700
    let index ← Gen.frequency [(3, Gen.nat (.linear 0 (top - 1))), (1, pure (top - 1)), (1,
        pure top),
      (1, Gen.element [0, 31, 32, 255, 256, 257])]
    next child (.position index)
  let fields (children : List Desc) : Gen (List PathStep) := do
    let index ← Gen.frequency [(9, Gen.nat (.constant 0 (children.length - 1))),
      (1, pure children.length)]
    next (children.getD index .bool) (.position index)
  let steps : List (Nat × Gen (List PathStep)) :=
    match shape with
    | .bool | .uint _ => [(1, stray)]
    | .byteVector length => [(6, element (.uint 1) (some length))]
    | .byteList limit => [(4, element (.uint 1) (some limit)), (2, word .length)]
    | .bitVector length => [(6, element .bool (some length))]
    | .bitList limit => [(4, element .bool (some limit)), (2, word .length)]
    | .progressiveBitList _ => [(4, element .bool none), (2, word .length)]
    | .vector child length => [(6, element child (some length))]
    | .list child limit => [(4, element child (some limit)), (2, word .length)]
    | .progressiveList child _ => [(4, element child none), (2, word .length)]
    | .container _ children => [(6, fields children)]
    | .progressiveContainer _ _ children => [(4, fields children), (2, word .activeFields)]
    | .compatibleUnion selectors options => [
        (4, do
          let slot ← Gen.nat (.constant 0 (options.length - 1))
          next (options.getD slot .bool) (.position (selectors.getD slot 0))),
        (1, pure [.position 0]),
        (2, word .selector)]
  Gen.frequency ((2, pure []) :: (1, stray) :: steps)

/-- The generalized index of a path is the one of the specification. -/
def gindexOfPath (oracle : Oracle) : Property IO := propertyM do
  let shape ← forAllWith typeText genDesc
  let path ← forAllWith pathText (genPath shape)
  pure do
    let expected ← oracle.ask ["sszgindex", typeText shape, pathText path]
    match Ssz.getGeneralizedIndex shape path with
    | .ok index => toString index === expected
    | .error e =>
      annotate s!"the specification: {expected}"
      refusal e === faultOf expected

/-- A generalized index: of a path of the type, a neighbour of one, or any small one. -/
def genGindex (shape : Ssz.Desc) : Gen Nat := do
  let path ← genPath shape
  let base := (Ssz.getGeneralizedIndex shape path).toOption.getD 1
  Gen.frequency [
    (4, pure base),
    (1, pure (base / 2)),
    (1, pure (base ^^^ 1)),
    (1, pure (2 * base)),
    (1, pure (2 * base + 1)),
    (2, Gen.nat (.exponential 1 4096))]

/-- The node at a generalized index of the tree of a value is the node of the reference. -/
def nodeAtGindex (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let index ← forAll (genGindex shape)
  pure do
    let expected ← oracle.ask ["ssznode", typeText shape, valueText value, toString index]
    match Ssz.nodeRoot shape value index with
    | .ok node => hex ⟨node⟩ === expected
    | .error e =>
      annotate s!"the specification: {expected}"
      refusal e === faultOf expected

/-- A proof built for an index of a value verifies against the root, and no other leaf does. -/
def proofVerifies : Property IO := pureIO do
  let (shape, value) ← forAllWith typedText genTyped
  let index ← forAll (genGindex shape)
  match Ssz.nodeRoot shape value index, Ssz.buildProof shape value index,
    Ssz.hashTreeRoot shape value with
  | .ok leaf, .ok proof, .ok root =>
    (Ssz.verifyMerkleProof leaf proof index root).toOption === some true
    let other := leaf.modify 0 (· + 1)
    (Ssz.verifyMerkleProof other proof index root).toOption === some false
  | _, _, _ => pure ()

/-- Indices of a multiproof: unrelated ones, and now and then a repeat or an ancestor. -/
def genIndices : Gen (List Nat) :=
  Gen.list (.linear 0 6) (Gen.frequency [(3, Gen.nat (.constant 1 63)), (1,
      Gen.nat (.exponential 1 5000))])

/-- Whether the request is one the specification's multiproof rebuilds a root from soundly. -/
def unrelated (indices : List Nat) : Bool :=
  !indices.isEmpty && indices.eraseDups.length == indices.length &&
    indices.all fun a => indices.all fun b =>
      a == b || !(List.range 64).any fun k => k > 0 && a >>> k == b

/-- The helper indices are those of the cited specification, which refuses the same requests.

Where a request has no relatives, they are also those of `consensus-specs`. -/
def helperIndices (oracle : Oracle) : Property IO := propertyM do
  let indices ← forAll genIndices
  pure do
    let cited ← oracle.ask ["spechelpers", toString indices]
    match Ssz.getHelperIndices indices with
    | .ok helpers =>
      ensure (unrelated indices) "a request with relatives was accepted"
      let text := " ".intercalate (helpers.map toString)
      let text := if text.isEmpty then "-" else text
      text === cited
      text === (← oracle.ask ["helpers", toString indices])
    | .error e =>
      annotate s!"the specification: {cited}"
      refusal e === faultOf cited

/-- Nodes of 32 bytes, as one run of bytes. -/
def genNodes (count : Nat) : Gen (List (Array UInt8)) :=
  Gen.list (.singleton count) ((·.data) <$> genBytesN 32)

/-- Nodes as the oracle reads them. -/
def nodesText (nodes : List (Array UInt8)) : String :=
  hex ⟨nodes.foldl (· ++ ·) #[]⟩

/-- The root of a multiproof is the one that both specifications rebuild. -/
def multiproofRoot (oracle : Oracle) : Property IO := propertyM do
  let indices ← forAll (Gen.filter (fun xs => unrelated xs && !xs.contains 1) genIndices)
  let count := (Ssz.getHelperIndices indices).toOption.getD [] |>.length
  let leaves ← forAllWith nodesText (genNodes indices.length)
  let proof ← forAllWith nodesText (genNodes count)
  pure do
    let expected ← oracle.ask ["multiroot", nodesText leaves, nodesText proof, toString indices]
    expected === (← oracle.ask ["specroot", nodesText leaves, nodesText proof, toString indices])
    match Ssz.calculateMultiMerkleRoot leaves proof indices with
    | .ok root => hex ⟨root⟩ === expected
    | .error e => failWith s!"EthLib refused: {repr e}"

/-- A request for a root, well formed or not, is answered or refused as the specification does. -/
def proofRequests (oracle : Oracle) : Property IO := propertyM do
  let index ← forAll (Gen.frequency [(1, Gen.element [0, 1]), (4, Gen.nat (.exponential 1 5000))])
  let off ← forAll (Gen.frequency [(6, pure 0), (1, pure 1), (1, pure 2)])
  let leaves ← forAllWith nodesText (genNodes 1)
  let proof ← forAllWith nodesText (genNodes (index.log2 + off - 1))
  let indices ← forAll genIndices
  let many ← forAllWith nodesText (genNodes indices.length)
  let helpers := (Ssz.getHelperIndices indices).toOption.getD [] |>.length
  let shared ← forAllWith nodesText (genNodes (helpers + off - 1))
  pure do
    let text (result : Except Ssz.Err (Array UInt8)) : String :=
      match result with
      | .ok root => hex ⟨root⟩
      | .error e => refusal e
    let cited ← oracle.ask ["specroot", nodesText leaves, nodesText proof, toString index]
    let got := text (Ssz.calculateMerkleRoot (leaves.headD #[]) proof index)
    got === (if cited.startsWith "error" then faultOf cited else cited)
    let cited ← oracle.ask ["specroot", nodesText many, nodesText shared, toString indices]
    let got := text (Ssz.calculateMultiMerkleRoot many shared indices)
    got === (if cited.startsWith "error" then faultOf cited else cited)

/-- A node as a vector of 32 bytes. -/
def chunkOf (node : Array UInt8) : Vector UInt8 32 :=
  Vector.ofFn fun i => node.getD i.val 0

/-- A branch by depth and index climbs to the root of `is_valid_merkle_branch`. -/
def branchByDepth (oracle : Oracle) : Property IO := propertyM do
  let depth ← forAll (Gen.nat (.linear 0 12))
  let index ← forAll (Gen.frequency [(3, Gen.nat (.constant 0 (2 ^ depth - 1))),
    (1, Gen.nat (.exponential 0 (2 ^ 70)))])
  let leaf ← forAllWith nodesText (genNodes 1)
  let branch ← forAllWith nodesText (genNodes depth)
  let wrong ← forAll Gen.bool
  pure do
    let leaf := chunkOf (leaf.headD #[])
    let nodes := branch.map chunkOf
    let rootText ← oracle.ask ["branchroot", nodesText [leaf.toArray], nodesText branch,
      toString depth, toString index]
    let root := chunkOf ((unhex? rootText).getD .empty).data
    let root := if wrong then root.set 31 (root[31] + 1) else root
    let expected ← oracle.ask ["branch", nodesText [leaf.toArray], nodesText branch,
      toString depth, toString index, hex ⟨root.toArray⟩]
    toString (Ssz.isValidMerkleBranch leaf nodes depth index root) === expected
    -- The normalized form of the light client: the same branch behind zero nodes.
    if index < 2 ^ depth then
      let zeros ← pure (List.replicate (index % 3) (Vector.replicate 32 (0 : UInt8)))
      let normal := Ssz.isValidNormalizedMerkleBranch leaf (zeros ++ nodes) (2 ^ depth + index) root
      normal.toOption === some (!wrong)

instance : Inhabited (Gen Ssz.Desc) := ⟨pure .bool⟩

open Ssz in
/-- A type near another: one name, limit, length, width, layout or spelling changed. -/
partial def genNear (shape : Desc) : Gen Desc :=
  let bump (n : Nat) : Gen Nat := Gen.element [n, n, n + 1, max 1 (n - 1)]
  let inside : Gen Desc :=
    match shape with
    | .vector element length => (Desc.vector · length) <$> genNear element
    | .list element limit => (Desc.list · limit) <$> genNear element
    | .progressiveList element limit => (Desc.progressiveList · limit) <$> genNear element
    | .container names fields => do
      let slot ← Gen.nat (.constant 0 (fields.length - 1))
      let field ← genNear (fields.getD slot .bool)
      pure (.container names (fields.set slot field))
    | .progressiveContainer active names fields => do
      let slot ← Gen.nat (.constant 0 (fields.length - 1))
      let field ← genNear (fields.getD slot .bool)
      pure (.progressiveContainer active names (fields.set slot field))
    | .compatibleUnion selectors options =>
      Gen.element [.compatibleUnion selectors options,
        .compatibleUnion (selectors.take 1) (options.take 1),
        .compatibleUnion (selectors.map fun s => s % 127 + 1) options]
    | other => pure other
  let outside : Gen Desc :=
    match shape with
    | .uint width => Desc.uint <$> Gen.element [width, 1, 8]
    | .bool => Gen.element [.bool, .uint 1]
    | .byteVector length => Gen.choice [Desc.byteVector <$> bump length,
        Desc.vector (.uint 1) <$> bump length, Desc.byteList <$> bump length]
    | .byteList limit => Gen.choice [Desc.byteList <$> bump limit,
        Desc.list (.uint 1) <$> bump limit, pure (.progressiveList (.uint 1) none)]
    | .bitVector length => Gen.choice [Desc.bitVector <$> bump length, Desc.bitList <$> bump length,
        Desc.vector .bool <$> bump length]
    | .bitList limit => Gen.choice [Desc.bitList <$> bump limit, pure (.progressiveBitList none),
        Desc.list .bool <$> bump limit]
    | .progressiveBitList _ => Gen.element [.progressiveBitList (some 5),
        .progressiveList .bool none]
    | .vector element length => Gen.choice [Desc.vector element <$> bump length,
        Desc.list element <$> bump length, pure (variant shape)]
    | .list element limit => Gen.choice [Desc.list element <$> bump limit,
        pure (.progressiveList element none), pure (variant shape)]
    | .progressiveList element _ => Gen.element [.progressiveList element (some 3), .list element 4]
    | .container names fields => Gen.element [
        .container (names.map (· ++ "x")) fields,
        .container (names.take 1 |>.map (· ++ "x") |>.append (names.drop 1)) fields,
        .container names.reverse fields.reverse,
        .container (names ++ ["more"]) (fields ++ [.bool]),
        .progressiveContainer (names.map fun _ => true) names fields]
    | .progressiveContainer active names fields => Gen.element [
        -- One more field at the end, or in front: every position moves in the second.
        .progressiveContainer (active ++ [true]) (names ++ ["more"]) (fields ++ [.bool]),
        .progressiveContainer (active ++ [false, true]) (names ++ ["more"]) (fields ++ [.uint 8]),
        .progressiveContainer (true :: active) ("more" :: names) (.bool :: fields),
        .progressiveContainer (false :: active) names fields,
        .progressiveContainer active (names.map (· ++ "x")) fields,
        .progressiveContainer active names.reverse fields,
        -- The first field alone, at its place, and the last field moved to the front.
        .progressiveContainer (active.take ((active.idxOf true) + 1)) (names.take 1)
          (fields.take 1),
        .progressiveContainer [true] (names.drop (names.length - 1))
          (fields.drop (fields.length - 1)),
        .container names fields]
    | .compatibleUnion selectors options => Gen.element [
        .compatibleUnion (selectors.take 1) (options.take 1), options.headD .bool]
  Gen.frequency [(2, pure shape), (3, inside), (3, outside)]

/-- Two types merkleize alike exactly when the reference lets one union hold both. -/
def compatible (oracle : Oracle) : Property IO := propertyM do
  let left ← forAllWith typeText genDesc
  let right ← forAllWith typeText (genNear left)
  pure do
    let expected ← oracle.ask ["sszcompat", typeText left, typeText right]
    ensure (right.wellFormed.toOption.isSome) "the near type is not well formed"
    (if Ssz.isCompatible left right then "ok" else "error") === expected
    -- Compatibility is symmetric, and a union of the two is legal exactly then.
    Ssz.isCompatible right left === Ssz.isCompatible left right
    (Ssz.Desc.compatibleUnion [1, 2] [left, right]).wellFormed.toOption.isSome ===
      Ssz.isCompatible left right

/-- The sizes an encoding can have are those of the reference, and an encoding lies within. -/
def sizeBounds (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  pure do
    let expected ← oracle.ask ["sszbounds", typeText shape]
    -- The reference gives a progressive shape the bound `2 ^ 32`; EthLib gives it none.
    match shape.maxSize with
    | some most =>
      s!"{shape.minSize} {most}" === expected
      let size := (Ssz.serialize shape value).toOption.getD #[] |>.size
      ensure (shape.minSize ≤ size && size ≤ most)
        s!"an encoding of {size} bytes is out of bounds"
    | none => (expected.splitOn " ").headD "" === toString shape.minSize
    -- A fixed size is both bounds; a list of limit zero has equal bounds and is not fixed.
    if let some size := shape.fixedSize then
      (shape.minSize, shape.maxSize) === (size, some size)

/-- The default value has the bytes and the root of the reference's, and reads as zeroed. -/
def defaults (oracle : Oracle) : Property IO := propertyM do
  let shape ← forAllWith typeText genDesc
  pure do
    match shape.default with
    | .ok value =>
      ensure (value.fits shape) "the default does not fit"
      (shape.isZero value).toOption === some true
      encodedText shape value === (← oracle.ask ["sszdef", typeText shape])
    | .error _ =>
      -- Only a union has no default.
      ensure ((typeText shape).splitOn "union" |>.length |> (· > 1))
        "a type without a union has no default"

end SerializationProperty

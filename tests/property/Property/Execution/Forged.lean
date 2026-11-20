import Property.Execution.Trie

/-!
# Hex-prefix, and proofs of tries that are built node by node

`trieSet` and `root` build only canonical tries.

A changed node of a real proof no longer has its hash.

So a proof from a real trie never shows the verifier a node that is not canonical.

Here the nodes are generated one by one along the path of a key, and hashed from the leaves up.

A model of twenty lines says what such a proof shows, and py-trie reads the same proof.

The hex-prefix encoding has its own two properties, at every length of path and both flags.
-/

open Hedgehog Support EthLib EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace ExecutionProperty

/-! ## Hex-prefix -/

/-- Any nibble. -/
def genNibble : Gen Nibble := (fun n => ⟨n % 16, by omega⟩) <$> Gen.nat (.constant 0 15)

/-- A path: every length from 0 to 9, the lengths around 64, and longer ones up to 130. -/
def genNibbles : Gen (List Nibble) :=
  Gen.frequency [(4, Gen.list (.constant 0 9) genNibble), (2, Gen.list (.constant 62 66) genNibble),
    (2, Gen.list (.constant 67 130) genNibble)]

/-- A path as text: one hexadecimal digit for each nibble, `-` for none. -/
def nibblesText (path : List Nibble) : String :=
  if path.isEmpty then "-"
  else String.ofList (path.map fun n => (Nat.toDigits 16 n.val).headD '0')

/-- The bytes of pairs of nibbles, the high one first. -/
def packPairs : List Nat → List UInt8
  | high :: low :: rest => UInt8.ofNat (16 * high + low) :: packPairs rest
  | _ => []

/-- Hex-prefix as Appendix C of the Yellow Paper writes it, apart from EthLib's.

The first nibble is `2 t + (length mod 2)`, and a zero nibble follows it when the length is even.
-/
def hpOf (path : List Nibble) (isLeaf : Bool) : ByteArray :=
  let flag := (if isLeaf then 2 else 0) + path.length % 2
  let nibbles := path.map (·.val)
  bytesOf (packPairs (if path.length % 2 = 1 then flag :: nibbles else flag :: 0 :: nibbles))

/-- The class of the length of a path. -/
def lengthClass (length : Nat) : String :=
  if length = 0 then "length: 0" else if length = 1 then "length: 1"
  else if length = 2 then "length: 2" else if length < 62 then
    (if length % 2 = 1 then "length: odd, 3 to 61" else "length: even, 4 to 60")
  else if length ≤ 66 then (if length % 2 = 1 then "length: 63 or 65" else "length: 62, 64 or 66")
  else "length: above 66"

/-- The hex-prefix encoding of a path is the one of execution-specs, and it decodes back.

The paths have every length from 0 to 9 and the lengths around 64, with both flags.

A second writer here, from the text of the Yellow Paper, must give the same bytes. -/
def hexPrefixEncode (oracle : Oracle) : Property IO := propertyM do
  let path ← forAllWith nibblesText genNibbles
  let isLeaf ← forAll Gen.bool
  pure do
    coverMin 2 "length: 0" (path.length = 0)
    coverMin 1 "length: 1" (path.length = 1)
    coverMin 2 "length: 2" (path.length = 2)
    coverMin 6 "length: odd, 3 to 61" (2 < path.length && path.length < 62 && path.length % 2 = 1)
    coverMin 5 "length: even, 4 to 60" (2 < path.length && path.length < 62 && path.length % 2 = 0)
    coverMin 3 "length: 63 or 65" (path.length = 63 || path.length = 65)
    coverMin 4 "length: 62, 64 or 66" (path.length = 62 || path.length = 64 || path.length = 66)
    coverMin 8 "length: above 66" (66 < path.length)
    coverMin 8 "flag: a leaf, odd" (isLeaf && path.length % 2 = 1)
    coverMin 8 "flag: a leaf, even" (isLeaf && path.length % 2 = 0)
    coverMin 7 "flag: an extension, odd" (!isLeaf && path.length % 2 = 1)
    coverMin 9 "flag: an extension, even" (!isLeaf && path.length % 2 = 0)
    coverMin 29 "a nibble of 8 or more" (path.any (8 ≤ ·.val))
    let compact := nibbleListToCompact path isLeaf
    hex compact === (← oracle.ask ["hp", nibblesText path, if isLeaf then "1" else "0"])
    hex compact === hex (hpOf path isLeaf)
    match compactToNibbleList compact with
    | .ok (back, flag) =>
      nibblesText back === nibblesText path
      flag === isLeaf
    | .error error => failWith s!"the encoding does not decode: {repr error}"

/-- Bytes that may be a hex-prefix encoding: every first byte, and encodings changed in a byte. -/
def genCompact : Gen ByteArray :=
  let anyFirst := (fun (first : UInt8) (rest : ByteArray) => ⟨#[first]⟩ ++ rest) <$> genByte <*>
    genBytes (.constant 0 4)
  let near := do
    let valid ← hpOf <$> genNibbles <*> Gen.bool
    let position ← Gen.frequency [(3, pure 0), (1, Gen.nat (.constant 0 (valid.size - 1)))]
    let byte ← genByte
    pure (valid.set! position byte)
  Gen.frequency [(1, pure .empty), (4, anyFirst), (2, near), (2, hpOf <$> genNibbles <*> Gen.bool),
    (2, hpOf <$> Gen.list (.constant 0 1) genNibble <*> Gen.bool)]

/-- The decoder reads exactly the encodings, as the Yellow Paper defines them.

The first nibble is at most 3, and when it is even the second nibble is zero.

What the decoder reads, execution-specs encodes to the same bytes.

What it refuses breaks one of the two rules, and the error names which. -/
def hexPrefixDecode (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAllWith hex genCompact
  pure do
    let first := (bytes.data.getD 0 0).toNat
    let (high, low) := (first / 16, first % 16)
    let expected := if bytes.isEmpty then "empty"
      else if 3 < high then s!"invalidFirstNibble {high}"
      else if high % 2 = 0 ∧ low ≠ 0 then s!"nonZeroPadding {low}" else "an encoding"
    coverMin 2 "verdict: empty" bytes.isEmpty
    coverMin 11 "verdict: the first nibble is above 3" (!bytes.isEmpty && 3 < high)
    coverMin 2 "verdict: the padding is not zero" (!bytes.isEmpty && high ≤ 3 && high % 2 = 0 &&
      low ≠ 0)
    for flag in [0, 1, 2, 3] do
      coverMin 4 s!"verdict: an encoding with the first nibble {flag}"
        (expected == "an encoding" && high = flag)
    coverMin 3 "an encoding of the empty path" (expected == "an encoding" && bytes.size = 1 &&
      high % 2 = 0)
    coverMin 4 "an encoding of one nibble" (expected == "an encoding" && bytes.size = 1 &&
      high % 2 = 1)
    match compactToNibbleList bytes with
    | .ok (path, isLeaf) =>
      expected === "an encoding"
      hex bytes === (← oracle.ask ["hp", nibblesText path, if isLeaf then "1" else "0"])
      isLeaf === decide (2 ≤ high)
      path.length === 2 * bytes.size - (if high % 2 = 1 then 1 else 2)
    | .error .empty => expected === "empty"
    | .error (.invalidFirstNibble nibble) => expected === s!"invalidFirstNibble {nibble}"
    | .error (.nonZeroPadding nibble) => expected === s!"nonZeroPadding {nibble}"

/-! ## Tries built node by node -/

/-- How a parent holds a child. -/
inductive Hold where
  /-- Inside its own encoding when the child has fewer than 32 bytes, else by hash. -/
  | canonical
  /-- Inside its own encoding, whatever the size. -/
  | inside
  /-- By hash, whatever the size. -/
  | byHash
  deriving Repr, BEq

/-- A node of a trie that no rule keeps canonical. -/
inductive Forged where
  /-- A leaf: the rest of a path, and a value that may be empty. -/
  | leaf (path : List Nibble) (value : ByteArray)
  /-- An extension: a run of nibbles that may be empty, and how it holds its child. -/
  | extension (path : List Nibble) (hold : Hold) (child : Forged)
  /-- A branch: some children, each at a nibble, and a value that may be empty. -/
  | branch (children : List (Nibble × Hold × Forged)) (value : ByteArray)
  /-- An item that is no node, or a reference that is neither empty nor a hash. -/
  | broken (name : String) (item : Item)

instance : Inhabited Forged := ⟨.leaf [] .empty⟩

instance : Inhabited Item := ⟨.bytes .empty⟩

/-- A node as a report shows it. -/
partial def Forged.text : Forged → String
  | .leaf path value => s!"leaf({nibblesText path}, {hex value})"
  | .extension path hold child => s!"ext({nibblesText path}, {reprStr hold}, {child.text})"
  | .branch children value =>
    let parts := children.map fun (nibble, hold, child) =>
      s!"{nibble.val}: {reprStr hold} {child.text}"
    s!"branch([{", ".intercalate parts}], {hex value})"
  | .broken name _ => s!"broken({name})"

mutual

/-- The RLP structure of a node. -/
partial def Forged.item : Forged → Item
  | .leaf path value => .list [.bytes (hpOf path true), .bytes value]
  | .extension path hold child => .list [.bytes (hpOf path false), child.held hold]
  | .branch children value =>
    .list ((List.finRange 16).map (fun (nibble : Nibble) =>
      match children.find? (·.1 == nibble) with
      | some (_, hold, child) => child.held hold
      | none => .bytes .empty) ++ [.bytes value])
  | .broken _ item => item

/-- What a parent writes for a child: its structure, or the hash of its encoding. -/
partial def Forged.held (node : Forged) (hold : Hold) : Item :=
  let item := node.item
  let digest : Item := .bytes ⟨(keccak256 (enc item)).toArray⟩
  match node, hold with
  | .broken _ _, _ => item
  | _, .inside => item
  | _, .byHash => digest
  | _, .canonical => if (enc item).size < 32 then item else digest

end

/-- Whether a parent holds a child by hash, so that a proof lists the child. -/
def Forged.isHashed (node : Forged) (hold : Hold) : Bool :=
  match node, hold with
  | .broken _ _, _ => false
  | _, .inside => false
  | _, .byHash => true
  | _, .canonical => 32 ≤ (enc node.item).size

/-- What a trie says of a path. -/
inductive Verdict where
  /-- The path has this value. -/
  | value (bytes : ByteArray)
  /-- The path has no value. -/
  | absent
  /-- The path reaches an item that is no node. -/
  | broken (name : String)
  /-- The path ends at a leaf whose value is empty, which no trie of the Yellow Paper holds. -/
  | emptyLeaf
  deriving Inhabited

/-- The model: what a node says of the rest of a path, and the nodes below it held by hash.

It reads the generated nodes, not their bytes. -/
partial def Forged.walk (node : Forged) (path : List Nibble) (proof : List ByteArray) :
    Verdict × List ByteArray :=
  let enter (hold : Hold) (child : Forged) (rest : List Nibble) : Verdict × List ByteArray :=
    child.walk rest (if child.isHashed hold then proof ++ [enc child.item] else proof)
  match node with
  | .leaf rest value =>
    (if rest != path then .absent else if value.isEmpty then .emptyLeaf else .value value, proof)
  | .extension segment hold child =>
    if segment.isEmpty then (.broken "an extension of no nibble", proof)
    else if segment == path.take segment.length then enter hold child (path.drop segment.length)
    else (.absent, proof)
  | .branch children value =>
    match path with
    | [] => (if value.isEmpty then .absent else .value value, proof)
    | nibble :: rest =>
      match children.find? (·.1 == nibble) with
      | some (_, hold, child) => enter hold child rest
      | none => (.absent, proof)
  | .broken name _ => (.broken name, proof)

/-- How a parent holds a child: mostly as the Yellow Paper says. -/
def genHold : Gen Hold :=
  Gen.frequency [(4, pure .canonical), (3, pure .inside), (2, pure .byHash)]

/-- An item that is no node, with its name. -/
def genBroken : Gen Forged :=
  let value : Item := .bytes ⟨#[7]⟩
  let leafPath : Item := .bytes ⟨#[0x20]⟩
  (fun (name, item) => Forged.broken name item) <$> Gen.element [
    ("a reference of 1 byte", .bytes ⟨#[1]⟩),
    ("a reference of 31 bytes", .bytes (bytesOf (List.replicate 31 1))),
    ("a reference of 33 bytes", .bytes (bytesOf (List.replicate 33 1))),
    ("a hash of no node", .bytes (bytesOf (List.replicate 32 1))),
    ("a list of no item", .list []),
    ("a list of one item", .list [leafPath]),
    ("a list of three items", .list [leafPath, value, value]),
    ("a list of 16 items", .list (List.replicate 16 (.bytes .empty))),
    ("a list of 18 items", .list (List.replicate 18 (.bytes .empty))),
    ("a path that is a list", .list [.list [], value]),
    ("a leaf whose value is a list", .list [leafPath, .list []]),
    ("a branch whose value is a list", .list (List.replicate 16 (.bytes .empty) ++ [.list []])),
    ("a path of no byte", .list [.bytes .empty, value]),
    ("a first nibble of 4", .list [.bytes ⟨#[0x40]⟩, value]),
    ("a first nibble of 15", .list [.bytes ⟨#[0xf1]⟩, value]),
    ("a padding that is not zero", .list [.bytes ⟨#[0x21, 0x23]⟩, value])]

/-- A path beside another: its last nibble changed, one nibble shorter, or one longer. -/
def genBeside (path : List Nibble) : Gen (List Nibble) := do
  let nibble ← genNibble
  Gen.element [path.dropLast ++ [nibble], path.dropLast, path ++ [nibble]]

/-- The end of a spine: a leaf of the path, a leaf beside it, a leaf with no value, or no node. -/
def genLeafFor (path : List Nibble) : Gen Forged :=
  Gen.frequency [(5, Forged.leaf path <$> genValue),
    (2, Forged.leaf <$> genBeside path <*> genValue),
    (1, pure (.leaf path .empty)), (1, genBroken)]

/-- A trie along the rest of a path, of at most the depth: the nodes that the path meets.

A branch also holds a few leaves off the path. -/
def genForgedAt : Nat → List Nibble → Gen Forged
  | 0, path => genLeafFor path
  | depth + 1, path =>
    let extension : Gen Forged := do
      let length ← Gen.frequency [(3, Gen.nat (.constant 1 (min 3 path.length))),
        (1, pure path.length)]
      let segment ← Gen.frequency [(7, pure (path.take length)),
        (1, (path.take (length - 1) ++ [·]) <$> genNibble), (1, pure [])]
      Forged.extension segment <$> genHold <*> genForgedAt depth (path.drop segment.length)
    let branch : Gen Forged := do
      let others ← Gen.list (.constant 0 3)
        (Gen.zip genNibble (Gen.zip genHold (Forged.leaf <$> Gen.list (.constant 0 2) genNibble <*>
          genValue)))
      let value ← Gen.frequency [(if path.isEmpty then 2 else 3, pure .empty), (2, genValue)]
      match path with
      | [] => pure (.branch others value)
      | nibble :: rest =>
        let others := others.filter (·.1 != nibble)
        let onPath ← Gen.frequency [(6, (fun hold child => [(nibble, hold, child)]) <$> genHold <*>
          genForgedAt depth rest), (1, pure [])]
        pure (.branch (onPath ++ others) value)
    Gen.frequency [(2, genLeafFor path), (if path.isEmpty then 0 else 3, extension), (4, branch),
      (1, genBroken)]

/-- The nibbles of bytes, the high one first, apart from EthLib's. -/
def nibblesOf (bytes : ByteArray) : List Nibble :=
  bytes.data.toList.flatMap fun byte =>
    [⟨byte.toNat / 16 % 16, by omega⟩, ⟨byte.toNat % 16, by omega⟩]

/-- The path of a key: its nibbles, or those of its hash in a secured trie. -/
def pathOf (secured : Bool) (key : ByteArray) : List Nibble :=
  nibblesOf (if secured then ⟨(keccak256 key).toArray⟩ else key)

/-- What the path of a key meets in a trie built node by node. -/
structure PathMet where
  oddExtension : Bool := false
  evenExtension : Bool := false
  oddLeaf : Bool := false
  evenLeaf : Bool := false
  emptyLeafPath : Bool := false
  branchValue : Bool := false
  branchNoValue : Bool := false
  emptySlot : Bool := false
  leftExtension : Bool := false
  inside : Bool := false
  hashed : Bool := false
  longInside : Bool := false
  shortHashed : Bool := false
  nestedInside : Bool := false
  deriving Inhabited

/-- What the rest of a path meets from a node on; `within` says the node is inside its parent. -/
partial def metBy (node : Forged) (path : List Nibble) (within : Bool) (met : PathMet) : PathMet :=
  let enter (hold : Hold) (child : Forged) (rest : List Nibble) (met : PathMet) : PathMet :=
    let hashed := child.isHashed hold
    let size := (enc child.item).size
    let isNode := match child with
      | .broken _ _ => false
      | _ => true
    let met := { met with
      inside := met.inside || (isNode && !hashed)
      hashed := met.hashed || hashed
      longInside := met.longInside || (isNode && !hashed && 32 ≤ size)
      shortHashed := met.shortHashed || (hashed && size < 32)
      nestedInside := met.nestedInside || (isNode && !hashed && within) }
    metBy child rest (isNode && !hashed) met
  match node with
  | .leaf rest _ =>
    if rest != path then met
    else { met with
      oddLeaf := rest.length % 2 = 1
      evenLeaf := rest.length % 2 = 0 && !rest.isEmpty
      emptyLeafPath := rest.isEmpty }
  | .extension segment hold child =>
    if segment.isEmpty then met
    else if segment == path.take segment.length then
      enter hold child (path.drop segment.length) { met with
        oddExtension := met.oddExtension || segment.length % 2 = 1
        evenExtension := met.evenExtension || segment.length % 2 = 0 }
    else { met with leftExtension := true }
  | .branch children value =>
    match path with
    | [] => { met with branchValue := !value.isEmpty, branchNoValue := value.isEmpty }
    | nibble :: rest =>
      match children.find? (·.1 == nibble) with
      | some (_, hold, child) => enter hold child rest met
      | none => { met with emptySlot := true }
  | .broken _ _ => met

/-- A proof of a trie built node by node shows what the model reads from the nodes.

The nodes lie along the path of a key: leaves, extensions, branches, and items that are no node.

A parent holds a child by the rule of the Yellow Paper, or the other way.

- A path that ends at a value: the verifier gives the value.
- A path that leaves the trie: the verifier shows the absence.
- A path that reaches an item that is no node: the verifier refuses the proof.
- A node after the last one of the path: the verifier refuses the proof.

py-trie reads the same proof, and where it answers it gives the answer of the model.

A leaf with an empty value is in no trie of the Yellow Paper, and only labelled. -/
def forgedProof (oracle : Oracle) : Property IO := propertyM do
  let secured ← forAll Gen.bool
  let key ← forAllWith hex (genBytes (.constant 0 4))
  let node ← forAllWith Forged.text
    (Gen.sized fun size => genForgedAt (min 5 (size / 12 + 1)) (pathOf secured key))
  let asked ← forAllWith hex (Gen.frequency [(6, pure key), (1, genBytes (.constant 0 4))])
  let extra ← forAll (Gen.frequency [(9, pure false), (1, pure true)])
  pure do
    let rootBytes := enc node.item
    let rootHash := keccak256 rootBytes
    let (verdict, below) := node.walk (pathOf secured asked) []
    let proof := rootBytes :: below ++ (if extra then [⟨#[0x80]⟩] else [])
    annotate s!"proof {" ".intercalate (proof.map hex)}"
    let result := verifyProof keccak256 rootHash secured asked proof
    annotate s!"EthLib: {repr result}"
    let got := proofAnswer result
    coverMin 16 "secured" secured
    coverMin 8 "model: a value" (!extra && verdict matches .value _)
    coverMin 11 "model: absent" (!extra && verdict matches .absent)
    coverMin 8 "model: an item that is no node" (!extra && verdict matches .broken _)
    coverMin 1 "model: a leaf with no value" (!extra && verdict matches .emptyLeaf)
    coverMin 3 "a node after the last one of the path" extra
    coverMin 5 "proof: 2 nodes" (below.length = 1)
    coverMin 2 "proof: 3 nodes or more" (2 ≤ below.length)
    if let .broken name := verdict then label s!"broken: {name}"
    match result with
    | .error error => label s!"EthLib: refuses, {errorName error}"
    | .ok _ => label "EthLib: accepts"
    let shape := metBy node (pathOf secured asked) false {}
    coverMin 5 "path: an extension of an odd length" shape.oddExtension
    coverMin 4 "path: an extension of an even length" shape.evenExtension
    coverMin 2 "path: a leaf of an odd length" shape.oddLeaf
    coverMin 5 "path: a leaf of an even length" shape.evenLeaf
    coverMin 1 "path: a leaf of no nibble" shape.emptyLeafPath
    coverMin 1 "path: ends at the value of a branch" shape.branchValue
    coverMin 1 "path: ends at a branch with no value" shape.branchNoValue
    coverMin 3 "path: an empty slot of a branch" shape.emptySlot
    coverMin 2 "path: an extension that the key leaves" shape.leftExtension
    coverMin 8 "path: a child inside its parent" shape.inside
    coverMin 8 "path: a child by hash" shape.hashed
    coverMin 4 "path: a long child inside its parent" shape.longInside
    classify "path: a short child by hash" shape.shortHashed
    coverMin 1 "path: a child inside a child inside its parent" shape.nestedInside
    if extra then got === "error"
    else match verdict with
      | .value bytes => got === hex bytes
      | .absent => got === "absent"
      | .broken _ => got === "error"
      | .emptyLeaf => label s!"a leaf with no value: EthLib answers {got}"
    -- The reference hashes no key, so it reads the hashed key of a secured trie as a key.
    let wireKey := if secured then ⟨(keccak256 asked).toArray⟩ else asked
    let reference ← oracle.ask (["trieverify", hexV rootHash, hex wireKey] ++ proof.map hex)
    if !extra then
      match verdict with
      | .value bytes =>
        coverMin 8 "py-trie answers, a value" (reference != "error")
        if reference ≠ "error" then reference === hex bytes
      | .absent =>
        coverMin 10 "py-trie answers, absent" (reference != "error")
        if reference ≠ "error" then reference === "absent"
      | .broken _ => classify "py-trie accepts an item that is no node" (reference != "error")
      | .emptyLeaf => label s!"a leaf with no value: py-trie answers {reference}"

/-- The names of the items that are no node. -/
def brokenNames : List String := [
  "a reference of 1 byte", "a reference of 31 bytes", "a reference of 33 bytes",
  "a hash of no node", "a list of no item", "a list of one item", "a list of three items",
  "a list of 16 items", "a list of 18 items", "a path that is a list",
  "a leaf whose value is a list", "a branch whose value is a list", "a path of no byte",
  "a first nibble of 4", "a first nibble of 15", "a padding that is not zero"]

/-- A proof whose path meets an item that is no node is refused, wherever the item lies.

The item is the root, the child of an extension, or the child of a branch on the path.

Each of the sixteen items comes as often as another. -/
def brokenNode : Property IO := propertyM do
  let broken ← forAllWith Forged.text genBroken
  let place ← forAll (Gen.nat (.constant 0 2))
  let hold ← forAll genHold
  let key ← forAllWith hex (genBytes (.constant 1 2))
  pure do
    let path := pathOf false key
    let node : Forged := match place, path with
      | 1, first :: _ => .extension [first] hold broken
      | 2, first :: _ => .branch [(first, hold, broken)] .empty
      | _, _ => broken
    let name := match broken with
      | .broken name _ => name
      | _ => "a node"
    coverOne 3 brokenNames name
    coverMin 11 "place: the root" (place = 0)
    coverMin 11 "place: under an extension" (place = 1)
    coverMin 10 "place: under a branch" (place = 2)
    let rootBytes := enc node.item
    let (_, below) := node.walk path []
    let result := verifyProof keccak256 (keccak256 rootBytes) false key (rootBytes :: below)
    match result with
    | .error error => label s!"EthLib: refuses, {errorName error}"
    | .ok value => failWith s!"EthLib accepts the proof: {hex (value.getD .empty)}"

end ExecutionProperty

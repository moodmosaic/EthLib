import Property.Execution.Common

/-!
# The Merkle Patricia Trie, against execution-specs and py-trie

The keys are short and over few bytes, so that they share prefixes and one is a prefix of another.

The values lie on both sides of the 32 bytes at which a parent holds a child by its hash.
-/

open Hedgehog Support EthLib EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace ExecutionProperty

/-- A key: a few bytes from a small alphabet, or 32 bytes that differ only at the end.

The keys of the alphabet share prefixes, and one is often a prefix of another. -/
def genKeyBytes : Gen ByteArray :=
  let short := bytesOf <$> Gen.list (.constant 0 4) (Gen.element [0x00, 0x01, 0x10, 0x11, 0xff])
  let long := (fun (tail : List UInt8) => bytesOf (List.replicate 30 0x11 ++ tail)) <$>
    Gen.list (.singleton 2) (Gen.element [0x00, 0x01, 0x10, 0xf0])
  Gen.frequency [(4, short), (1, long)]

/-- How the keys of one trie are drawn. -/
inductive KeyStyle where
  /-- From the small alphabet, so that keys share prefixes and nest. -/
  | nested
  /-- A stem that every key starts with, then at most two bytes: the root is an extension. -/
  | stem (bytes : ByteArray)
  /-- Any one or two bytes, so that a branch has a child at every nibble. -/
  | wide
  /-- 32 bytes that differ in the last one or two nibbles: leaves that their branch holds inside.
  -/
  | deep (bytes : ByteArray)

/-- A style of keys. -/
def genKeyStyle : Gen KeyStyle :=
  Gen.frequency [(4, pure .nested), (2, KeyStyle.stem <$> genBytes (.constant 1 3)),
    (2, pure .wide), (1, KeyStyle.deep <$> genBytesN 31)]

/-- A key of a style, and now and then one of the alphabet or a long one whatever the style. -/
def genKeyIn (style : KeyStyle) : Gen ByteArray :=
  let own := match style with
    | .nested => genKeyBytes
    | .stem bytes => (bytes ++ ·) <$> genBytes (.constant 0 2)
    | .wide => genBytes (.constant 1 2)
    | .deep bytes => (fun (b : UInt8) => bytes ++ ⟨#[b]⟩) <$>
        Gen.frequency [(3, Gen.element [0x00, 0x01, 0x02, 0x10, 0x11, 0xf0]), (1, genByte)]
  Gen.frequency [(18, own), (2, genKeyBytes), (1, genBytes (.constant 33 70))]

/-- A value that is not empty, of a length around the 32 bytes of a hash, or of 250 to 300. -/
def genValue : Gen ByteArray := do
  let length ← Gen.frequency [(6, Gen.nat (.constant 1 4)), (6, Gen.nat (.constant 25 34)),
    (2, Gen.nat (.linear 1 80)), (1, Gen.nat (.constant 250 300))]
  genBytesN length

/-- A value, or now and then the empty one, which deletes its key. -/
def genValueOrNone : Gen ByteArray := Gen.frequency [(4, genValue), (1, pure .empty)]

/-- Writes to a trie, in order: none, one or two, some, or many. -/
def genWritesIn (style : KeyStyle) : Gen (List (ByteArray × ByteArray)) :=
  let write := Gen.zip (genKeyIn style) genValueOrNone
  Gen.frequency [(1, pure []), (2, Gen.list (.constant 1 3) write),
    (8, Gen.list (.linear 2 24) write), (1, Gen.list (.constant 40 90) write)]

/-- A style of keys, and writes to a trie in that style. -/
def genTrieCase : Gen (KeyStyle × List (ByteArray × ByteArray)) := do
  let style ← genKeyStyle
  pure (style, ← genWritesIn style)

/-- A key to ask a trie for: one that is set, one beside a key that is set, or any of the style.

A key beside another has one byte changed, is cut by a byte or two, or goes on by a byte.

So the path leaves the trie at a leaf, inside an extension, and at a branch. -/
def genAskedKey (style : KeyStyle) (writes : List (ByteArray × ByteArray)) : Gen ByteArray :=
  if writes.isEmpty then genKeyIn style
  else
    let set := Gen.element (writes.map Prod.fst)
    let beside := do
      let key ← set
      let byte ← Gen.frequency [(2, Gen.element [0x00, 0x01, 0x10, 0x11, 0xff]), (1, genByte)]
      Gen.element [key.extract 0 (key.size - 1), key ++ ⟨#[byte]⟩,
        key.extract 0 (key.size - 1) ++ ⟨#[byte]⟩, key.extract 0 (key.size - 2),
        ⟨#[byte]⟩ ++ key.extract 1 key.size, key.extract 0 1 ++ ⟨#[byte]⟩ ++ key.extract 2 key.size]
    Gen.frequency [(3, set), (5, beside), (1, genKeyIn style)]

/-- A write as a word of a command of the oracle. -/
def pairWord (entry : ByteArray × ByteArray) : String := s!"{hex entry.1}={hex entry.2}"

/-- The trie after the writes. -/
def trieOf (secured : Bool) (writes : List (ByteArray × ByteArray)) : Trie :=
  writes.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured, []⟩

/-- The value of a key after the writes: the last one written, by a plain search. -/
def lastWrite (writes : List (ByteArray × ByteArray)) (key : ByteArray) : ByteArray :=
  ((writes.reverse.find? fun (k, _) => k.data == key.data).map Prod.snd).getD .empty

/-- How the writes show in a report. -/
def showWrites (writes : List (ByteArray × ByteArray)) : String :=
  " ".intercalate (writes.map pairWord)

/-! ## The shape of a trie, for the labels of a case -/

/-- The entries of a trie as paths, or none where a value is empty. -/
def pathsOf (trie : Trie) : List (List Nibble × ByteArray) :=
  (prepareData keccak256 trie.data trie.secured).toOption.getD []

/-- The node of the entries at a level, or none where the trie has none. -/
def nodeAt (obj : List (List Nibble × ByteArray)) (level : Nat) : Option InternalNode :=
  (patricialize keccak256 obj level).toOption.join

/-- Whether a parent holds the node of the entries at a level inside its own encoding. -/
def heldInside (obj : List (List Nibble × ByteArray)) (level : Nat) : Bool :=
  match encode (unencoded (nodeAt obj level)) with
  | .ok encoded => encoded.size < 32
  | .error _ => false

/-- The children of a branch at a level that hold a node, each with its entries. -/
def childrenAt (obj : List (List Nibble × ByteArray)) (level : Nat) :
    List (List (List Nibble × ByteArray)) :=
  ((List.finRange 16).map fun (nibble : Nibble) =>
    obj.filter fun (key, _) => key[level]? = some nibble).filter (!·.isEmpty)

/-- How many nodes of each kind a trie has, and how their parents hold them. -/
structure Census where
  /-- The leaves. -/
  leaves : Nat := 0
  /-- The extensions. -/
  extensions : Nat := 0
  /-- The branches with no value. -/
  branches : Nat := 0
  /-- The branches with a value. -/
  valued : Nat := 0
  /-- The nodes below the root that their parent holds inside its encoding. -/
  inside : Nat := 0
  /-- The nodes below the root that their parent holds by hash. -/
  hashed : Nat := 0

/-- The census of the node of the entries at a level, added to a census. -/
def censusAt : Nat → List (List Nibble × ByteArray) → Nat → Bool → Census → Census
  | 0, _, _, _, census => census
  | fuel + 1, obj, level, isRoot, census =>
    let census := if isRoot then census
      else if heldInside obj level then { census with inside := census.inside + 1 }
      else { census with hashed := census.hashed + 1 }
    match nodeAt obj level with
    | none => census
    | some (.leaf _ _) => { census with leaves := census.leaves + 1 }
    | some (.extension segment _) =>
      censusAt fuel obj (level + segment.length) false
        { census with extensions := census.extensions + 1 }
    | some (.branch _ value) =>
      let census := if value.size = 0 then { census with branches := census.branches + 1 }
        else { census with valued := census.valued + 1 }
      (childrenAt obj level).foldl (fun census sub => censusAt fuel sub (level + 1) false census)
        census

/-- The census of a trie. -/
def censusOf (trie : Trie) : Census :=
  let obj := pathsOf trie
  censusAt (longestPath obj + 2) obj 0 true {}

/-- Whether the path of a key of the trie is a proper prefix of the path of another. -/
def hasPrefixKeys (trie : Trie) : Bool :=
  let paths := (pathsOf trie).map Prod.fst
  paths.any fun a => paths.any fun b => a.length < b.length && a.isPrefixOf b

/-- The labels of a trie: its count of keys, its kinds of node, and how they are held. -/
def labelTrie (trie : Trie) : TestT IO Unit := do
  let count := trie.data.length
  label (if count = 0 then "keys: 0" else if count = 1 then "keys: 1"
    else if count = 2 then "keys: 2" else if count ≤ 8 then "keys: 3 to 8" else "keys: 9 or more")
  let census := censusOf trie
  let obj := pathsOf trie
  label (match nodeAt obj 0 with
    | none => "root: no node"
    | some (.leaf _ _) => "root: a leaf"
    | some (.extension _ _) => "root: an extension"
    | some (.branch _ _) => "root: a branch")
  coverMin 6 "trie: a key is a prefix of another" (hasPrefixKeys trie)
  coverMin 8 "trie: an extension" (0 < census.extensions)
  coverMin 6 "trie: a branch with a value" (0 < census.valued)
  coverMin 11 "trie: a node held inside its parent" (0 < census.inside)
  coverMin 23 "trie: a node held by hash" (0 < census.hashed)
  coverMin 10 "trie: nodes held both ways" (0 < census.inside && 0 < census.hashed)
  coverMin 7 "trie: a key of 33 bytes or more" (trie.data.any (32 < ·.1.size))
  coverMin 9 "trie: a value of 250 bytes or more" (trie.data.any (250 ≤ ·.2.size))

/-- The labels of the writes that made a trie: overwrites, and deletes of a key that is set. -/
def labelWrites (secured : Bool)
    (writes : List (ByteArray × ByteArray)) : TestT IO Unit := do
  let step (acc : Trie × Bool × Bool) (write : ByteArray × ByteArray) : Trie × Bool × Bool :=
    let (trie, overwrote, deleted) := acc
    let isSet := !(trieGet trie write.1).isEmpty
    (trieSet trie write.1 write.2, overwrote || (isSet && !write.2.isEmpty),
      deleted || (isSet && write.2.isEmpty))
  let (_, overwrote, deleted) := writes.foldl step (⟨secured, []⟩, false, false)
  coverMin 9 "writes: a key written twice" overwrote
  coverMin 4 "writes: a delete of a key that is set" deleted

/-- The nodes on the path of a key, and where the path ends. -/
structure PathShape where
  /-- The kind of each node on the path, from the root. -/
  kinds : List String := []
  /-- Whether the path enters a node that its parent holds inside its encoding. -/
  inside : Bool := false
  /-- Whether the path enters a node that its parent holds by hash. -/
  hashed : Bool := false
  /-- Where the path ends. -/
  ending : String := "nowhere"

/-- The shape of the path of the rest of a key, from the node of the entries at a level. -/
def pathShapeAt : Nat → List (List Nibble × ByteArray) → Nat → List Nibble → PathShape → PathShape
  | 0, _, _, _, shape => shape
  | fuel + 1, obj, level, path, shape =>
    let enter (sub : List (List Nibble × ByteArray)) (deeper : Nat) (rest : List Nibble)
        (shape : PathShape) : PathShape :=
      let shape := if (nodeAt sub deeper).isNone then shape
        else if heldInside sub deeper then { shape with inside := true }
        else { shape with hashed := true }
      pathShapeAt fuel sub deeper rest shape
    match nodeAt obj level with
    | none => { shape with
        ending := if shape.kinds.isEmpty then "the empty trie" else "an empty slot of a branch" }
    | some (.leaf rest _) => { shape with
        kinds := shape.kinds ++ ["leaf"]
        ending := if rest = path then "the leaf of the key" else "the leaf of another key" }
    | some (.extension segment _) =>
      let shape := { shape with kinds := shape.kinds ++ ["extension"] }
      if segment = path.take segment.length then
        enter obj (level + segment.length) (path.drop segment.length) shape
      else { shape with ending := "an extension that the key leaves" }
    | some (.branch _ value) =>
      let kind := if value.size = 0 then "branch" else "branch with a value"
      let shape := { shape with kinds := shape.kinds ++ [kind] }
      match path with
      | [] => { shape with
          ending := if value.size = 0 then "a branch with no value" else "the value of a branch" }
      | nibble :: rest =>
        enter (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1) rest shape

/-- The shape of the path of a key in a trie. -/
def pathShape (trie : Trie) (key : ByteArray) : PathShape :=
  let obj := pathsOf trie
  let path := keyPath keccak256 trie.secured key
  pathShapeAt (path.length + 2) obj 0 path {}

/-- The labels of the path of a key in a trie. -/
def labelPath (trie : Trie) (key : ByteArray) : TestT IO Unit := do
  let shape := pathShape trie key
  label s!"path ends at: {shape.ending}"
  coverMin 5 "path: through an extension" (shape.kinds.contains "extension")
  coverMin 5 "path: through a branch with a value" (shape.kinds.contains "branch with a value")
  coverMin 3 "path: into a node held inside its parent" shape.inside
  coverMin 14 "path: into a node held by hash" shape.hashed
  label (if key.isEmpty then "key: empty" else if key.size ≤ 4 then "key: 1 to 4 bytes"
    else if key.size < 32 then "key: 5 to 31 bytes" else if key.size = 32 then "key: 32 bytes"
    else "key: 33 bytes or more")

/-- What the deletion of a key that is set does to the branch above it, if it removes that branch.

A branch with two occupants loses one, and the other takes its place: a leaf, or an extension. -/
def collapseAt : Nat → List (List Nibble × ByteArray) → Nat → List Nibble → Option String
  | 0, _, _, _ => none
  | fuel + 1, obj, level, path =>
    let kindOf (sub : List (List Nibble × ByteArray)) : String :=
      match nodeAt sub (level + 1) with
      | some (.leaf _ _) => "a leaf"
      | _ => "an extension"
    match nodeAt obj level with
    | some (.extension segment _) =>
      collapseAt fuel obj (level + segment.length) (path.drop segment.length)
    | some (.branch _ value) =>
      let children := childrenAt obj level
      match path with
      | [] => if h : children.length = 1 then some (kindOf children[0]) else none
      | nibble :: rest =>
        let sub := obj.filter fun (key, _) => key[level]? = some nibble
        if sub.length = 1 then
          let others := children.filter fun other =>
            other.any fun (key, _) => key[level]? != some nibble
          if value.size ≠ 0 ∧ others.isEmpty then some "a leaf"
          else if h : value.size = 0 ∧ others.length = 1 then some (kindOf others[0])
          else none
        else collapseAt fuel sub (level + 1) rest
    | _ => none

/-- What the deletion of a key does to the branch above it, in a trie that holds the key. -/
def collapseOf (trie : Trie) (key : ByteArray) : Option String :=
  let path := keyPath keccak256 trie.secured key
  collapseAt (path.length + 2) (pathsOf trie) 0 path

/-- The root of a trie is the root of execution-specs, plain or secured. -/
def trieRoot (oracle : Oracle) : Property IO := propertyM do
  let secured ← forAll Gen.bool
  let writes ← forAllWith showWrites (Prod.snd <$> genTrieCase)
  pure do
    let trie := trieOf secured writes
    coverMin 16 "secured" secured
    labelTrie trie
    labelWrites secured writes
    let expected ← oracle.ask (["trieroot", if secured then "1" else "0"] ++ writes.map pairWord)
    orError (hexV <$> root keccak256 trie) === expected
    -- A trie holds no empty value: one that is put in its entries by hand has no root.
    let broken : Trie := ⟨secured, trie.data ++ [(⟨#[0xee, 0xee, 0xee]⟩, .empty)]⟩
    (root keccak256 broken).toOption.isNone === true
    (getProof keccak256 broken .empty).toOption.isNone === true

/-- The value that a proof gives, in the words of the oracle. -/
def proofAnswer (result : Except ProofError (Option ByteArray)) : String :=
  match result with
  | .ok (some value) => hex value
  | .ok none => "absent"
  | .error _ => "error"

/-- A hash for the trie that is not Keccak-256, with its name in the oracle. -/
def otherHashes : List (String × (ByteArray → Hash32)) := [
  ("sha256", fun bytes =>
    (exactBytes? 32 (EthLib.Cryptography.Hash.Sha256.hash bytes)).getD (Vector.replicate 32 0)),
  ("prefixed", fun bytes => keccak256 (⟨#[1]⟩ ++ bytes))]

/-- The trie takes its hash as an argument: with another hash, the root is still the reference's.

The reference is the trie of execution-specs with its hash replaced by the same one.

The hash also makes the path of a key in a secured trie.

The proof of a key under that hash shows the value of the key, or its absence. -/
def trieOtherHash (oracle : Oracle) : Property IO := propertyM do
  let (name, hash) ← forAllWith Prod.fst (Gen.element otherHashes)
  let secured ← forAll Gen.bool
  let (style, writes) ← forAllWith (fun c => showWrites c.2) genTrieCase
  let key ← forAllWith hex (genAskedKey style writes)
  pure do
    let trie := trieOf secured writes
    label s!"hash: {name}"
    coverMin 16 "secured" secured
    labelTrie trie
    let expected ← oracle.ask (["trieroothash", name, if secured then "1" else "0"] ++
      writes.map pairWord)
    let rootHash := root hash trie
    orError (hexV <$> rootHash) === expected
    let truth := lastWrite writes key
    label (if truth.isEmpty then "the key is absent" else "the key is set")
    match rootHash, getProof hash trie key with
    | .ok r, .ok proof =>
      label (if proof.length ≤ 1 then "proof: 1 node" else "proof: 2 nodes or more")
      proofAnswer (verifyProof hash r secured key proof) ===
        (if truth.isEmpty then "absent" else hex truth)
      -- The proof under one hash is no proof under another.
      if 2 ≤ proof.length then
        proofAnswer (verifyProof keccak256 r secured key proof) === "error"
    | _, _ => failWith "no root or no proof"

/-- The proof of a key is the proof of py-trie, and it shows the value of the key or its absence.

py-trie lists every node on the path, and EthLib the ones that their parent holds by hash.

So the oracle keeps those of py-trie.

Half the tries are secured: their keys are hashed, so every path has 64 nibbles. -/
def trieProof (oracle : Oracle) : Property IO := propertyM do
  let secured ← forAll Gen.bool
  let (style, writes) ← forAllWith (fun c => showWrites c.2) genTrieCase
  let key ← forAllWith hex (genAskedKey style writes)
  pure do
    let trie := trieOf secured writes
    coverMin 16 "secured" secured
    labelTrie trie
    labelPath trie key
    -- The reference hashes no key, so a secured trie is sent with its keys already hashed.
    let wire (k : ByteArray) : ByteArray := if secured then ⟨(keccak256 k).toArray⟩ else k
    let answer ← oracle.ask (["trieproof", hex (wire key)] ++
      writes.map fun (k, v) => pairWord (wire k, v))
    let proof := (getProof keccak256 trie key).toOption.getD []
    label (if proof.length ≤ 1 then "proof: 1 node" else if proof.length = 2 then "proof: 2 nodes"
      else "proof: 3 nodes or more")
    label (if (lastWrite writes key).isEmpty then "the key is absent" else "the key is set")
    let rootHash := orError (hexV <$> root keccak256 trie)
    " ".intercalate (rootHash :: proof.map hex) === answer
    let truth := lastWrite writes key
    match root keccak256 trie with
    | .ok r => proofAnswer (verifyProof keccak256 r secured key proof) ===
        (if truth.isEmpty then "absent" else hex truth)
    | .error _ => failWith "no root"

/-- A change of a proof. -/
inductive ProofChange where
  /-- A node removed. -/
  | drop (index : Nat)
  /-- A node written twice. -/
  | repeated (index : Nat)
  /-- A node changed as an item and encoded again. -/
  | node (index : Nat) (mutation : Mutation)
  /-- A byte of a node changed. -/
  | byte (index position : Nat) (value : UInt8)
  /-- The nodes of the proof of another key, in place of the tail. -/
  | graft (keep : Nat)
  deriving Repr

/-- A change of a proof, at an index that is reduced modulo the length. -/
def genProofChange : Gen ProofChange :=
  let index := Gen.nat (.constant 0 5)
  Gen.choice [ProofChange.drop <$> index, ProofChange.repeated <$> index,
    ProofChange.node <$> index <*> genMutation,
    ProofChange.byte <$> index <*> Gen.nat (.constant 0 600) <*> genByte,
    ProofChange.graft <$> index]

/-- The proof after a change; `other` is the proof of another key. -/
def ProofChange.apply (proof other : List ByteArray) : ProofChange → List ByteArray
  | .drop i => proof.eraseIdx (i % (proof.length + 1))
  | .repeated i =>
    let i := i % (proof.length + 1)
    proof.take (i + 1) ++ proof.drop i
  | .node i mutation => proof.mapIdx fun j encoded =>
    if j = i % proof.length then
      match decode encoded with
      | .ok item => enc (mutate mutation.path mutation.kind item)
      | .error _ => encoded
    else encoded
  | .byte i position value => proof.mapIdx fun j encoded =>
    if j = i % proof.length ∧ 0 < encoded.size then encoded.set! (position % encoded.size) value
    else encoded
  | .graft keep => proof.take (keep % (proof.length + 1)) ++ other.drop (keep % (other.length + 1))

/-- A proof that EthLib accepts gives the value of the key in the trie, whatever was done to it.

The proofs are those of a key, changed:

- A node dropped, repeated or rewritten.
- A byte changed.
- The tail of the proof of another key.

A proof that still reads the trie's nodes may be accepted, and then it must not lie.

py-trie reads the same proof, and where both accept, they give the same value. -/
def trieProofSound (oracle : Oracle) : Property IO := propertyM do
  let (style, writes) ← forAllWith (fun c => showWrites c.2) genTrieCase
  let keys := genAskedKey style writes
  let key ← forAllWith hex keys
  let otherKey ← forAllWith hex keys
  let asked ← forAllWith hex (Gen.frequency [(3, pure key), (1, pure otherKey),
    (1, genKeyIn style)])
  let changes ← forAll (Gen.list (.constant 0 2) genProofChange)
  pure do
    let trie := trieOf false writes
    let proof := (getProof keccak256 trie key).toOption.getD []
    let other := (getProof keccak256 trie otherKey).toOption.getD []
    let changed := changes.foldl (fun proof change => change.apply proof other) proof
    annotate s!"proof {" ".intercalate (changed.map hex)}"
    let .ok r := root keccak256 trie | failWith "no root"
    let truth := lastWrite writes asked
    let result := verifyProof keccak256 r false asked changed
    let got := proofAnswer result
    labelTrie trie
    labelPath trie asked
    label s!"changes: {changes.length}"
    coverMin 14 "the proof is the proof of the key asked"
      (changed.map hex == ((getProof keccak256 trie asked).toOption.getD []).map hex)
    coverMin 19 "the proof is changed, and not the proof of the key asked"
      (changed.map hex != ((getProof keccak256 trie asked).toOption.getD []).map hex)
    for change in changes do
      label (match change with
        | .drop _ => "change: a node dropped"
        | .repeated _ => "change: a node repeated"
        | .node _ _ => "change: a node rewritten"
        | .byte _ _ _ => "change: a byte"
        | .graft _ => "change: the tail of another proof")
    label (match result with
      | .ok (some _) => "EthLib: accepts, the key is set"
      | .ok none => "EthLib: accepts, the key is absent"
      | .error error => s!"EthLib: refuses, {errorName error}")
    if got ≠ "error" then
      got === (if truth.isEmpty then "absent" else hex truth)
      -- The reference raises on a key that ends inside an extension: its refusal says nothing.
      let reference ← oracle.ask (["trieverify", hexV r, hex asked] ++ changed.map hex)
      classify "accepted by both, a changed proof" (reference ≠ "error" &&
        changed.map hex != ((getProof keccak256 trie asked).toOption.getD []).map hex)
      classify "accepted by EthLib alone" (reference == "error")
      if reference ≠ "error" then got === reference

/-! ## The trie as a state machine -/

/-- A write to the trie: an empty value deletes the key. -/
structure TrieWrite where
  /-- The key. -/
  key : ByteArray
  /-- The value, or the empty byte string to delete the key. -/
  value : ByteArray

instance : Repr TrieWrite where
  reprPrec w _ := s!"{hex w.key}={hex w.value}"

/-- The model of a trie: the keys that are set, each with its value, in no order. -/
structure TrieModel where
  /-- How the keys of this trie are drawn. -/
  style : KeyStyle
  /-- The entries. -/
  entries : List (ByteArray × ByteArray)

instance : Repr TrieModel where
  reprPrec m _ := showWrites m.entries

/-- The model: a list of entries, where a write replaces its key and an empty value removes it.

A small trie mostly gains a key, and a larger one loses and changes keys as often as it gains. -/
def trieModel : Model TrieModel TrieWrite where
  initState := (fun style => ⟨style, []⟩) <$> genKeyStyle
  transitions s :=
    let fresh := Gen.zipWith TrieWrite.mk (genKeyIn s.style) genValue
    if s.entries.isEmpty then fresh
    else
      let set := Gen.element (s.entries.map Prod.fst)
      let grow := if s.entries.length < 6 then 6 else 3
      Gen.frequency [(grow, fresh), (2, Gen.zipWith TrieWrite.mk set genValue),
        (2, (TrieWrite.mk · .empty) <$> set), (1, (TrieWrite.mk · .empty) <$> genKeyIn s.style)]
  apply s w :=
    let rest := s.entries.filter fun (k, _) => k.data != w.key.data
    { s with entries := if w.value.isEmpty then rest else (w.key, w.value) :: rest }

/-- EthLib's trie under writes, beside py-trie under the same writes.

py-trie changes its nodes in place at each write, and EthLib builds the root from the entries.

After each write the two roots are equal, and EthLib holds the entries of the model.

EthLib's root does not depend on the order in which the entries were set. -/
def trieMachine (oracle : Oracle) : StateMachine TrieModel TrieWrite Trie IO where
  toModel := trieModel
  initSut _ := do
    oracle.stdin.putStrLn "sm_trie\tnew"
    oracle.stdin.flush
    let _ ← oracle.stdout.getLine
    pure ⟨false, []⟩
  applySut before _ after w := do
    let isSet := !(trieGet before w.key).isEmpty
    label (if w.value.isEmpty then
        (if isSet then "write: a delete of a key that is set" else "write: a delete of no key")
      else if isSet then "write: a new value of a key that is set" else "write: a new key")
    if isSet ∧ w.value.isEmpty then
      match collapseOf before w.key with
      | some kind => label s!"a delete turns a branch into {kind}"
      | none => label "a delete leaves its branch, or the trie had none"
    let trie := trieSet before w.key w.value
    let count := after.entries.length
    coverMin 2 "reaches 9 keys or more" (9 ≤ count)
    coverMin 14 "a write to a trie where a key is a prefix of another" (hasPrefixKeys trie)
    coverMin 14 "a write to a trie with a branch with a value" (0 < (censusOf trie).valued)
    coverMin 24 "a write to a trie with nodes held both ways"
      (0 < (censusOf trie).inside && 0 < (censusOf trie).hashed)
    let expected ← oracle.ask ["sm_trie", "set", hex w.key, hex w.value]
    orError (hexV <$> root keccak256 trie) === expected
    pure trie
  invariants trie s := do
    trie.data.length === s.entries.length
    for (key, value) in s.entries do
      hex (trieGet trie key) === hex value
    -- The root is a function of the entries, not of their order.
    orError (hexV <$> root keccak256 ⟨false, s.entries⟩) ===
      orError (hexV <$> root keccak256 trie)

end ExecutionProperty

namespace ExecutionProperty

/-- The empty proof shows that a key is absent from the empty trie, as it does for py-trie.

The empty trie has no node, so a proof by "the nodes on the path" (EIP-1186) lists none.

py-trie builds the empty proof, and reads it as the absence of the key.

EthLib refused the empty proof when the campaign began, and takes it since pull request #3405.

See the findings. -/
def emptyTrieProof (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith hex genKeyBytes
  let secured ← forAll Gen.bool
  pure do
    let .ok emptyRoot := root keccak256 ⟨secured, []⟩ | failWith "no root"
    let reference ← oracle.ask ["trieverify", hexV emptyRoot, hex key]
    reference === "absent"
    annotate s!"EthLib: {repr (verifyProof keccak256 emptyRoot secured key [])}"
    proofAnswer (verifyProof keccak256 emptyRoot secured key []) === reference

end ExecutionProperty

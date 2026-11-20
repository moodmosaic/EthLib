import Hedgehog
import Support
import Property.Serialization.Common

/-!
# The classes of a case

A property that passes may test little, so each one names the branches its cases reach.

The classes here are read from the code under test.

There is one per form of a prefix, constructor of a type, size of a tree and reason of a refusal.

A report lists each class with its share of the cases.
-/

open Hedgehog Support EthLib.Serialization

namespace SerializationProperty

variable {m : Type → Type} [Monad m]

/-- Count the case under the one name it has, among the names it could have. -/
def classifyOne (kind : String) (known : List String) (name : String) : TestT m Unit :=
  (if known.contains name then known else known ++ [name]).forM fun each =>
    classify s!"{kind}: {each}" (each == name)

/-- Count the case under each of the names it has, among the names it could have. -/
def classifyAny (kind : String) (known names : List String) : TestT m Unit :=
  (known ++ (names.filter (!known.contains ·)).eraseDups).forM fun each =>
    classify s!"{kind}: {each}" (names.contains each)

/-- The property with a least share, in percent, asked of the classes that a table names.

A class is named where it is counted, with `classify`; its minimum is set here, in one place.

So the minimums of a driver are one table, made from the shares of a long run. -/
def covering (table : List (String × Nat)) (property : Property IO) : Property IO :=
  let ask (journal : Journal) : Journal := journal.map fun
    | .label name least hit => .label name (max least ((table.lookup name).getD 0)) hit
    | entry => entry
  { property with test := do
      let test ← property.test
      modify ask
      pure do
        test
        modify ask }

/-! ## RLP -/

/-- A length by the form of the prefix that writes it. -/
def lengthClass (length : Nat) : String :=
  if length == 0 then "0"
  else if length < 56 then "1 to 55"
  else if length < 256 then "56 to 255"
  else if length < 65536 then "256 to 65535"
  else "65536 or more"

/-- The classes of a length. -/
def lengthClasses : List String := ["0", "1 to 55", "56 to 255", "256 to 65535", "65536 or more"]

/-- A byte string by the form of its encoding. -/
def stringClass (data : ByteArray) : String :=
  if data.size == 1 then
    if data.data[0]! < 0x80 then "a byte below 0x80" else "string of 1, 0x80 or more"
  else if data.size == 0 then "string of 0"
  else if data.size < 56 then "string of 2 to 55"
  else if data.size < 256 then "string of 56 to 255"
  else if data.size < 65536 then "string of 256 to 65535"
  else "string of 65536 or more"

/-- The classes of an RLP node. -/
def itemUniverse : List String :=
  ["a byte below 0x80", "string of 0", "string of 1, 0x80 or more", "string of 2 to 55",
    "string of 56 to 255", "string of 256 to 65535", "string of 65536 or more"] ++
  lengthClasses.map ("list payload of " ++ ·)

/-- The bytes that write a length in base 256. -/
def byteLength (n : Nat) : Nat := if n == 0 then 0 else n.log2 / 8 + 1

/-- The size of an encoding with a payload of a length, counted apart from the encoder. -/
def prefixedSize (length : Nat) : Nat :=
  if length < 56 then 1 + length else 1 + byteLength length + length

/-- The class of every node of an item, the size of its encoding, and its depth. -/
partial def itemClasses : Rlp.Item → List String × Nat × Nat
  | .bytes data =>
    let size := if data.size == 1 && data.data[0]! < 0x80 then 1 else prefixedSize data.size
    ([stringClass data], size, 0)
  | .list items =>
    let below := items.map itemClasses
    let payload := below.foldl (fun total part => total + part.2.1) 0
    let depth := below.foldl (fun deepest part => max deepest part.2.2) 0
    (s!"list payload of {lengthClass payload}" :: below.flatMap (·.1), prefixedSize payload,
      depth + 1)

/-- Label an item: the class of its root, the classes it holds, and its depth. -/
def labelItem (item : Rlp.Item) : TestT m Unit := do
  let (classes, _, depth) := itemClasses item
  classifyOne "root" itemUniverse (classes.headD "")
  classifyAny "holds" itemUniverse classes
  classifyOne "depth" ["0", "1", "2", "3", "4 or more"]
    (if depth < 4 then toString depth else "4 or more")

/-- An input by what its first byte announces. -/
def inputForm (input : ByteArray) : String :=
  if input.size == 0 then "no byte"
  else
    let first := input.data[0]!.toNat
    if first < 0x80 then "a byte below 0x80"
    else if first < 0xb8 then "short string"
    else if first < 0xc0 then s!"long string, length on {first - 0xb7}"
    else if first < 0xf8 then "short list"
    else s!"long list, length on {first - 0xf7}"

/-- The forms of an input. -/
def inputForms : List String :=
  ["no byte", "a byte below 0x80", "short string", "short list"] ++
  (List.range 8).map (fun k => s!"long string, length on {k + 1}") ++
  (List.range 8).map (fun k => s!"long list, length on {k + 1}")

/-- The verdict of the decoder, by the constructor of its error. -/
def rlpVerdict {α : Type} : Except Rlp.RlpError α → String
  | .ok _ => "accepted"
  | .error (.inputTooShort ..) => "input too short"
  | .error (.singleByteWithPrefix _) => "a byte below 0x80 with a prefix"
  | .error (.longFormForShortLength _) => "long form for a short length"
  | .error .leadingZeroInLength => "leading zero in a length"
  | .error (.trailingBytes _) => "trailing bytes"
  | .error .leadingZeroInScalar => "leading zero in a scalar"
  | .error .listAsScalar => "a list as a scalar"
  | .error _ => "another error"

/-- The verdicts of the decoder of an item. -/
def rlpVerdicts : List String :=
  ["accepted", "input too short", "a byte below 0x80 with a prefix",
    "long form for a short length", "leading zero in a length", "trailing bytes"]

/-! ## SSZ types -/

open Ssz in
/-- A type by its constructor and the kind of what it holds. -/
def kindOf : Desc → String
  | .bool => "boolean"
  | .uint width => s!"uint{8 * width}"
  | .byteVector _ => "ByteVector"
  | .byteList _ => "ByteList"
  | .bitVector _ => "Bitvector"
  | .bitList _ => "Bitlist"
  | .progressiveBitList _ => "ProgressiveBitlist"
  | .vector element _ =>
    if element.isBasic then "Vector of basic"
    else if element.isFixed then "Vector of fixed composite" else "Vector of variable"
  | .list element _ =>
    if element.isBasic then "List of basic"
    else if element.isFixed then "List of fixed composite" else "List of variable"
  | .progressiveList element _ =>
    if element.isBasic then "ProgressiveList of basic"
    else if element.isFixed then "ProgressiveList of fixed composite"
    else "ProgressiveList of variable"
  | .container _ fields =>
    if fields.all Desc.isFixed then "Container, fixed" else "Container, variable"
  | .progressiveContainer active _ fields =>
    if active.contains false then "ProgressiveContainer with a gap"
    else if fields.all Desc.isFixed then "ProgressiveContainer, fixed"
    else "ProgressiveContainer, variable"
  | .compatibleUnion _ _ => "CompatibleUnion"

/-- The kinds of a type. -/
def kindUniverse : List String :=
  ["boolean", "uint8", "uint16", "uint32", "uint64", "uint128", "uint256", "ByteVector",
    "ByteList", "Bitvector", "Bitlist", "ProgressiveBitlist", "Vector of basic",
    "Vector of fixed composite", "Vector of variable", "List of basic",
    "List of fixed composite", "List of variable", "ProgressiveList of basic",
    "ProgressiveList of fixed composite", "ProgressiveList of variable", "Container, fixed",
    "Container, variable", "ProgressiveContainer, fixed", "ProgressiveContainer, variable",
    "ProgressiveContainer with a gap", "CompatibleUnion"]

open Ssz in
/-- The kind of every type that a type holds, itself first. -/
partial def kindsOf (shape : Desc) : List String :=
  kindOf shape :: match shape with
    | .vector element _ | .list element _ | .progressiveList element _ => kindsOf element
    | .container _ fields | .progressiveContainer _ _ fields => fields.flatMap kindsOf
    | .compatibleUnion _ options => options.flatMap kindsOf
    | _ => []

/-- Label a type: the kind of its root, the kinds it holds, and its nesting. -/
def labelType (shape : Ssz.Desc) : TestT m Unit := do
  let kinds := kindsOf shape
  classifyOne "root" kindUniverse (kinds.headD "")
  classifyAny "holds" kindUniverse kinds
  classifyOne "nesting" ["1", "2", "3", "4 or more"]
    (if shape.nesting < 4 then toString shape.nesting else "4 or more")
  classify "size: fixed" shape.isFixed
  classify "size: variable" (!shape.isFixed)

/-! ## SSZ values -/

/-- Whether a count is a power of two. -/
def isPow2 (n : Nat) : Bool := n > 0 && 2 ^ n.log2 == n

/-- The classes of the tree of one value: its leaves, its capacity, its zero subtrees. -/
def treeClasses (shape : Ssz.Desc) (value : Ssz.Value) : List String :=
  match Ssz.merkleLayout shape value with
  | .error _ => []
  | .ok layout =>
    let count := layout.leaves.count
    let leaves :=
      if count == 0 then ["leaves: none"]
      else if count == 1 then ["leaves: one"]
      else if isPow2 count then ["leaves: a power of two"]
      else if isPow2 (count - 1) then ["leaves: one over a power of two"]
      else ["leaves: another count"]
    let room := match layout.limit with
      | none =>
        -- The runs of a spine hold 1, 4, 16 and 64 leaves.
        [if count == 0 then "spine: no run" else if count ≤ 1 then "spine: one run"
          else if count ≤ 5 then "spine: two runs" else if count ≤ 21 then "spine: three runs"
          else if count ≤ 85 then "spine: four runs" else if count ≤ 341 then "spine: five runs"
          else "spine: six runs or more"] ++
        (if [1, 5, 21, 85, 341, 1365].contains count then ["spine: its last run is full"]
          else [])
      | some capacity =>
        let zeros := Ssz.depthFor capacity - Ssz.depthFor (max count 1)
        [if capacity == 0 then "capacity: 0" else if capacity == count then "capacity: full"
          else if isPow2 capacity then "capacity: a power of two, not full"
          else "capacity: not a power of two, not full",
          if zeros == 0 then "zero subtree: none" else if zeros < 8 then "zero subtree: 1 to 7"
          else if zeros < 32 then "zero subtree: 8 to 31"
          else if zeros < 64 then "zero subtree: 32 to 63"
          else if zeros == 64 then "zero subtree: 64" else "zero subtree: 65 or more"]
    -- The deepest zero subtree beside the data is one level under the top of the tree.
    let deepest := match layout.limit with
      | some capacity =>
        if Ssz.depthFor capacity > Ssz.depthFor (max count 1) then some (Ssz.depthFor capacity - 1)
        else none
      | none => none
    let asked := match deepest with
      | some depth =>
        if depth == 64 then ["asks the zero root of depth 64, the last of the table"]
        else if depth > 64 then ["asks a zero root of depth 65 or more, which is folded"] else []
      | none => []
    leaves ++ room ++ asked ++ (if layout.mixin.isSome then ["mixes a word in"] else [])

/-- The classes of the tree of a value. -/
def treeUniverse : List String :=
  ["leaves: none", "leaves: one", "leaves: a power of two", "leaves: one over a power of two",
    "leaves: another count", "capacity: 0", "capacity: full",
    "capacity: a power of two, not full", "capacity: not a power of two, not full",
    "zero subtree: none", "zero subtree: 1 to 7", "zero subtree: 8 to 31",
    "zero subtree: 32 to 63", "zero subtree: 64", "zero subtree: 65 or more", "spine: no run",
    "spine: one run", "spine: two runs", "spine: three runs", "spine: four runs",
    "spine: five runs", "spine: six runs or more", "spine: its last run is full",
    "asks the zero root of depth 64, the last of the table",
    "asks a zero root of depth 65 or more, which is folded", "mixes a word in"]

/-- The classes of a tree under a capacity, without those of a spine. -/
def boundedUniverse : List String := treeUniverse.filter (!·.startsWith "spine")

/-- The classes of a tree on a spine, without those of a capacity. -/
def spineUniverse : List String :=
  treeUniverse.filter fun name => name.startsWith "leaves" || name.startsWith "spine"

/-- The counts of bits at the edges of a byte and of a node. -/
def bitEdges : List Nat := [0, 1, 7, 8, 9, 255, 256, 257]

open Ssz in
/-- The classes of every value that a value holds: bitfields and lists by their counts. -/
partial def valueClasses : Desc → Value → List String
  | .bitVector _, .bits data | .bitList _, .bits data | .progressiveBitList _, .bits data =>
    if bitEdges.contains data.size then [s!"bits: {data.size}"] else ["bits: another count"]
  | .byteList limit, .bytes data =>
    (if data.size == limit then ["a list at its limit"] else []) ++
    (if data.size == 0 then ["a list of none"] else [])
  | .vector element _, .seq values => values.flatMap (valueClasses element)
  | .list element limit, .seq values =>
    (if values.length == limit then ["a list at its limit"] else []) ++
    (if values.isEmpty then ["a list of none"] else []) ++ values.flatMap (valueClasses element)
  | .progressiveList element _, .seq values =>
    (if values.isEmpty then ["a list of none"] else []) ++ values.flatMap (valueClasses element)
  | .container _ fields, .seq values | .progressiveContainer _ _ fields, .seq values =>
    (fields.zip values).flatMap fun (field, value) => valueClasses field value
  | .compatibleUnion selectors options, .union selector data =>
    match (selectors.zip options).lookup selector with
    | some option => "a union" :: valueClasses option data
    | none => []
  | _, _ => []

/-- The classes of the values inside a value. -/
def valueUniverse : List String :=
  bitEdges.map (fun n => s!"bits: {n}") ++
  ["bits: another count", "a list at its limit", "a list of none", "a union"]

/-- The size of an encoding by the nodes it fills, and by the bytes that an offset in it takes. -/
def bytesClass (size : Nat) : String :=
  if size == 0 then "no byte"
  else if size < 32 then "1 to 31"
  else if size == 32 then "32"
  else if size ≥ 65536 then "65536 or more"
  else if size % 32 == 0 then "a multiple of 32 above it"
  else "another size above 32"

/-- The classes of the size of an encoding. -/
def bytesClasses : List String :=
  ["no byte", "1 to 31", "32", "a multiple of 32 above it", "another size above 32",
    "65536 or more"]

/-- Label a value of a type: the tree of its root, and the values it holds. -/
def labelValue (shape : Ssz.Desc) (value : Ssz.Value) : TestT m Unit := do
  classifyAny "root" treeUniverse (treeClasses shape value)
  classifyAny "holds" valueUniverse (valueClasses shape value)
  classifyOne "bytes" bytesClasses
    (bytesClass ((Ssz.serialize shape value).toOption.getD #[]).size)

/-- The reasons for which the decoder refuses bytes.

`TRUNCATED` is not among them.

`deserialize` checks the size of a struct before it reads its fixed part, so it never gives it.

The readers that give it are tested by a call of their own. -/
def decodeReasons : List String :=
  ["SCOPE", "SCOPE_TOO_SMALL", "SCOPE_UNDIVIDED", "FIRST_OFFSET", "OFFSET_UNORDERED",
    "OFFSET_PAST_SCOPE", "OFFSET_UNALIGNED", "OFFSET_BELOW_TABLE", "NOT_A_BIT",
    "PADDING_BITS", "EMPTY_ENCODING", "NO_DELIMITER", "TRAILING_ZEROS", "NO_SELECTOR",
    "UNKNOWN_SELECTOR", "LIMIT"]

/-- Label an outcome: accepted, or refused for a reason among those known. -/
def labelOutcome {α : Type} (reasons : List String) (result : Except Ssz.Err α)
    (kind : String := "verdict") : TestT m Unit :=
  classifyOne kind ("accepted" :: reasons)
    (match result with
      | .ok _ => "accepted"
      | .error e => e.reason)

open Ssz in
/-- The constructor of a type. -/
def constructorOf : Desc → String
  | .bool => "boolean"
  | .uint _ => "uint"
  | .byteVector _ => "ByteVector"
  | .byteList _ => "ByteList"
  | .bitVector _ => "Bitvector"
  | .bitList _ => "Bitlist"
  | .progressiveBitList _ => "ProgressiveBitlist"
  | .vector _ _ => "Vector"
  | .list _ _ => "List"
  | .progressiveList _ _ => "ProgressiveList"
  | .container _ _ => "Container"
  | .progressiveContainer _ _ _ => "ProgressiveContainer"
  | .compatibleUnion _ _ => "CompatibleUnion"

/-- The constructors of a type. -/
def constructors : List String :=
  ["boolean", "uint", "ByteVector", "ByteList", "Bitvector", "Bitlist", "ProgressiveBitlist",
    "Vector", "List", "ProgressiveList", "Container", "ProgressiveContainer", "CompatibleUnion"]

/-- A count by how many there are, up to a few. -/
def countClass (most count : Nat) : String :=
  if count < most then toString count else s!"{most} or more"

/-- The classes of a count. -/
def countClasses (most : Nat) : List String :=
  (List.range most).map toString ++ [s!"{most} or more"]

/-- The depth of a generalized index, by the turns below the root. -/
def depthClass (index : Nat) : String :=
  if index == 0 then "no index"
  else if index == 1 then "the root"
  else if index.log2 == 1 then "1"
  else if index.log2 ≤ 4 then "2 to 4"
  else if index.log2 ≤ 8 then "5 to 8"
  else if index.log2 ≤ 16 then "9 to 16"
  else if index.log2 ≤ 63 then "17 to 63"
  else "64 or more"

/-- The classes of the depth of a generalized index. -/
def depthClasses : List String :=
  ["no index", "the root", "1", "2 to 4", "5 to 8", "9 to 16", "17 to 63", "64 or more"]

/-- Where the walk to a generalized index ends, by the branch of `nodeRootAt` that answers. -/
def walkClass (shape : Ssz.Desc) (value : Ssz.Value) (index : Nat) : String :=
  match Ssz.merkleLayout shape value with
  | .error _ => "no layout"
  | .ok layout =>
    if index ≤ 1 then "the root"
    else
      let depth := if layout.mixin.isSome then index.log2 - 1 else index.log2
      if layout.mixin.isSome && index.testBit depth then
        if depth == 0 then "the mixed-in word" else "under the mixed-in word"
      else match layout.limit with
        | none => "on or under a spine"
        | some capacity =>
          if depth ≤ (Ssz.nextPow2 capacity).log2 then "inside the tree of the root"
          else "under a leaf of the tree of the root"

/-- The classes of the end of a walk. -/
def walkClasses : List String :=
  ["the root", "the mixed-in word", "under the mixed-in word", "on or under a spine",
    "inside the tree of the root", "under a leaf of the tree of the root"]

/-- The reasons for which a value has no node at an index. -/
def nodeReasons : List String :=
  ["NOT_A_GINDEX", "PATH_INTO_MIXIN", "PATH_INTO_PACKED", "PATH_INTO_GAP", "PATH_PAST_SPINE"]

/-- Label a request for a node: the verdict, the depth, the branch, and a zero node. -/
def labelNode (shape : Ssz.Desc) (value : Ssz.Value) (index : Nat)
    (reasons : List String := nodeReasons) (walks : List String := walkClasses) :
    TestT m Unit := do
  let result := Ssz.nodeRoot shape value index
  labelOutcome reasons result
  classifyOne "depth" depthClasses (depthClass index)
  classifyOne "walk" walks (walkClass shape value index)
  classify "the node is the root of a zero subtree"
    (match result with
      | .ok node => Ssz.zeroRoots.contains node
      | .error _ => false)

end SerializationProperty

import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Classes
import Property.Serialization.Merkle
import Property.Serialization.Misc
import Property.Serialization.Params
import Property.Serialization.Near

/-!
# Declarations that name no type, limits of progressive shapes, documents near a valid one
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Serialization

namespace SerializationProperty

/-! ## Illegal declarations -/

open Ssz in
/-- A declaration that names no type, by one rule of the specification or of an EIP. -/
def genIllegal : Gen (String × Desc) := do
  let field ← genDescOf 1
  let layout ← genActive 3
  let fields := [field, .bool, .uint 8]
  let names := fieldNames 3
  Gen.element [
    ("a uint of three bytes", .uint 3),
    ("a uint of no bytes", .uint 0),
    ("a uint of 64 bytes", .uint 64),
    ("an empty vector", .vector field 0),
    ("an empty bit vector", .bitVector 0),
    ("an empty byte vector", .byteVector 0),
    ("a container of no fields", .container [] []),
    ("a container with a name too few", .container (names.take 2) fields),
    ("a container with a name twice", .container ["a", "b", "a"] fields),
    ("a progressive container of no fields", .progressiveContainer [] [] []),
    ("a layout of no positions", .progressiveContainer [] names fields),
    ("a layout that ends on a gap", .progressiveContainer (layout ++ [false]) names fields),
    ("a layout with a field too many", .progressiveContainer (layout ++ [true]) names fields),
    ("a layout with a field too few", .progressiveContainer [true, true] names fields),
    ("a layout of only gaps", .progressiveContainer [false, false, false] names fields),
    ("a layout of 257 positions",
      .progressiveContainer (List.replicate 254 false ++ [true, true, true]) names fields),
    ("a progressive container with a name twice",
      .progressiveContainer layout ["a", "a", "b"] fields),
    ("a union of no options", .compatibleUnion [] []),
    ("a union with the selector 0", .compatibleUnion [0, 1] [field, field]),
    ("a union with the selector 128", .compatibleUnion [1, 128] [field, field]),
    ("a union with the selector 255", .compatibleUnion [255] [field]),
    ("a union with a selector twice", .compatibleUnion [5, 5] [field, field]),
    ("a union with a selector too many", .compatibleUnion [1, 2] [field]),
    ("a union with an option too many", .compatibleUnion [1] [field, field]),
    ("a union of options that merkleize apart", .compatibleUnion [1, 2] [.uint 8, .uint 4]),
    ("a union of a list and a vector", .compatibleUnion [1, 2] [.list field 2, .vector field 2])]

open Ssz in
/-- A legal type that holds the given one, at some depth. -/
def genAround (inner : Desc) : Gen Desc :=
  Gen.element [inner, .list inner 3, .vector inner 2, .progressiveList inner none,
    .container ["a", "b"] [.bool, inner], .progressiveContainer [true, false, true] ["a",
        "b"] [inner, .bool],
    .compatibleUnion [1, 2] [inner, inner], .list (.container ["a"] [inner]) 1]

/-- The reasons for which a declaration names no type. -/
def declarationReasons : List String :=
  ["UINT_WIDTH", "VECTOR_EMPTY", "CONTAINER_EMPTY", "LAYOUT_WIDTH", "LAYOUT_TRAILING_GAP",
    "LAYOUT_TOO_WIDE", "LAYOUT_FIELD_COUNT", "BAD_DECLARATION", "UNION_EMPTY",
    "UNION_SELECTOR_RANGE", "UNION_SELECTOR_REPEATED", "UNION_INCOMPATIBLE"]

/-- A declaration that breaks a rule is refused, wherever in a type it sits. -/
def illegalDeclarations : Property IO := pureIO do
  let (rule, inner) ← forAllWith (fun (rule, shape) => s!"{rule}: {typeText shape}") genIllegal
  let shape ← forAllWith typeText (genAround inner)
  classifyOne "refused as" declarationReasons
    (match shape.wellFormed with
      | .ok _ => "accepted"
      | .error e => e.reason)
  classifyOne "around it" ("nothing: it is the root" :: constructors.drop 7)
    (if shape == inner then "nothing: it is the root" else constructorOf shape)
  ensure shape.wellFormed.toOption.isNone s!"{rule} was accepted"

/-- A declaration names a type exactly when the cited specification lets it. -/
def declarations (oracle : Oracle) : Property IO := propertyM do
  let base ← forAllWith typeText genDesc
  let illegal ← forAllWith (fun (rule, shape) => s!"{rule}: {typeText shape}") genIllegal
  let near ← forAllWith typeText (genNear base)
  let shape ← forAllWith typeText (Gen.frequency [(1, pure near), (2, genAround illegal.2)])
  pure do
    labelOutcome declarationReasons shape.wellFormed
    let cited ← oracle.ask ["ssztype", typeText shape]
    annotate cited
    classify "refused, and the oracle answers with a name of its own"
      (shape.wellFormed.toOption.isNone && faultOf cited == "error NOT_AN_INTEGER")
    match shape.wellFormed with
    | .ok _ => cited === "ok"
    | .error e =>
      annotate s!"EthLib refused: {repr e}"
      -- The oracle refuses a count of names or selectors by itself, under a name of its own.
      if faultOf cited != "error NOT_AN_INTEGER" then refusal e === faultOf cited

/-- A layout of 256 positions is the widest legal one. -/
def widestLayout : Property IO := pureIO do
  let gaps ← forAll (Gen.frequency [(1, Gen.element [0, 1, 254]), (4, Gen.nat (.constant 0 254))])
  let wide (count : Nat) : Ssz.Desc :=
    .progressiveContainer
      (List.replicate gaps true ++ List.replicate (count - gaps - 1) false ++ [true])
      (fieldNames (gaps + 1)) (List.replicate (gaps + 1) .bool)
  classifyOne "fields" ["1", "2 to 128", "129 to 255"]
    (if gaps == 0 then "1" else if gaps < 128 then "2 to 128" else "129 to 255")
  ensure (wide 256).wellFormed.toOption.isSome "a layout of 256 positions was refused"
  ensure (wide 257).wellFormed.toOption.isNone "a layout of 257 positions was accepted"

/-! ## The limit of a progressive shape -/

open Ssz in
/-- A limit on a progressive shape bounds the count and changes neither the bytes nor the tree. -/
def progressiveLimit : Property IO := pureIO do
  let element ← forAllWith typeText (genDescOf 1)
  let bits ← forAll Gen.bool
  let free : Desc := if bits then .progressiveBitList none else .progressiveList element none
  let value ← forAllWith valueText (genValueOf true free)
  let count := match value with
    | .bits data => data.size
    | .seq elements => elements.length
    | _ => 0
  let limit ← forAll (Gen.element [count, count + 1, count - 1, 0, 2 ^ 64])
  let bound : Desc :=
    if bits then .progressiveBitList (some limit) else .progressiveList element (some limit)
  ensure bound.wellFormed.toOption.isSome "the type is not well formed"
  let within := count ≤ limit
  classifyOne "shape" ["ProgressiveBitlist", "ProgressiveList of basic",
      "ProgressiveList of composite"]
    (if bits then "ProgressiveBitlist" else if element.isBasic then "ProgressiveList of basic"
      else "ProgressiveList of composite")
  classifyOne "count" ["below the limit", "at the limit", "over the limit"]
    (if count < limit then "below the limit" else if count == limit then "at the limit"
      else "over the limit")
  classify "count: 0" (count == 0)
  classifyAny "root" spineUniverse (treeClasses free value)
  value.fits bound === within
  if within then
    encodedText bound value === encodedText free value
    let bytes := (serialize free value).toOption.getD #[]
    (deserialize bound bytes).toOption.map valueText === some (valueText value)
  else
    ensure (serialize bound value).toOption.isNone "a value over the limit was written"
    ensure (hashTreeRoot bound value).toOption.isNone "a value over the limit has a root"
    let bytes := (serialize free value).toOption.getD #[]
    ensure (deserialize bound bytes).toOption.isNone "bytes over the limit were read"

/-! ## Limits far above the data -/

open Ssz in
/-- A list with a limit far above its count: a tree of zero subtrees beside a few nodes. -/
def genTall : Gen (Desc × Value) := do
  let element ← Gen.frequency [(1, genBasic), (1, genDescOf 1)]
  -- Above 64 levels of zero subtrees the root of one is folded, not read from the table.
  --
  -- The first reference has no tree deeper than 256 levels, so no limit here is above `2 ^ 250`.
  let power ← Gen.frequency [(2, Gen.element [10, 31, 32, 40, 62]),
    (2, Gen.element [63, 64, 65, 66, 69, 70, 72, 73]), (1, Gen.element [100, 200, 250])]
  let near ← Gen.element [0, 1]
  let limit := 2 ^ power + near
  let kind ← Gen.element [0, 1, 2]
  let shape : Desc := match kind with
    | 0 => .list element limit
    | 1 => .byteList limit
    | _ => .bitList limit
  let small : Desc := match kind with
    | 0 => .list element 40
    | 1 => .byteList 70
    | _ => .bitList 520
  let value ← genValueOf true small
  pure (shape, value)

/-- A list far below its limit has the bytes and the root of the reference. -/
def tallLists (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTall
  -- Now and then a step into an element past the count, where the tree has a zero node.
  let count := match value with
    | .seq values => values.length
    | _ => 0
  let past := (Ssz.getGeneralizedIndex shape [.position (count + 1), .position 0]).toOption
  let index ← forAll (Gen.frequency [(5, genGindex shape),
    (if past.isSome then 1 else 0, pure (past.getD 1))])
  pure do
    classifyOne "root" ["List of basic", "List of fixed composite", "List of variable",
      "ByteList", "Bitlist"] (kindOf shape)
    -- A list under a limit far above its count: never full, and no spine.
    classifyAny "root" (boundedUniverse.filter (!["capacity: 0", "capacity: full"].contains ·))
      (treeClasses shape value)
    labelNode shape value index nodeReasons.dropLast
      (walkClasses.filter (· != "on or under a spine"))
    encodedText shape value === (← oracle.ask ["sszenc", typeText shape, valueText value])
    let expected ← oracle.ask ["ssznode", typeText shape, valueText value, toString index]
    match Ssz.nodeRoot shape value index with
    | .ok node => hex ⟨node⟩ === expected
    | .error e =>
      annotate s!"the specification: {expected}"
      refusal e === faultOf expected

/-! ## Multiproofs of a value -/

/-- Indices at which a value has nodes, none of them a relative of another.

Many indices are drawn, and those that have a node and no relative so far are kept, up to five. -/
def genNodeIndices (shape : Ssz.Desc) (value : Ssz.Value) : Gen (List Nat) := do
  let candidates ← Gen.list (.singleton 16) (genGindex shape)
  let most ← Gen.nat (.constant 2 5)
  let kept := candidates.foldl (fun kept index =>
    if kept.length < most && index > 1 && unrelated (index :: kept) &&
        (Ssz.nodeRoot shape value index).toOption.isSome then index :: kept
    else kept) []
  pure (if kept.isEmpty then candidates.take 1 else kept.reverse)

/-- A multiproof built for indices of a value rebuilds its root.

This holds by EthLib and by the specification. -/
def multiproofOfValue (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let indices ← forAll (Gen.frequency [(5, genNodeIndices shape value),
    (1, Gen.list (.constant 1 4) (genGindex shape))])
  pure do
    let leaves := indices.mapM (Ssz.nodeRoot shape value)
    match leaves, Ssz.buildMultiproof shape value indices, Ssz.hashTreeRoot shape value with
    | .ok leaves, .ok proof, .ok root =>
      label "a multiproof was built and checked"
      classifyOne "indices" ((countClasses 4).drop 1) (countClass 4 indices.length)
      classifyOne "nodes of the proof" ["0", "1 to 4", "5 to 12", "13 or more"]
        (if proof.length == 0 then "0" else if proof.length ≤ 4 then "1 to 4"
          else if proof.length ≤ 12 then "5 to 12" else "13 or more")
      (Ssz.verifyMerkleMultiproof leaves proof indices root).toOption === some true
      hex ⟨root⟩ === (← oracle.ask ["multiroot", nodesText leaves, nodesText proof,
          toString indices])
      -- Another leaf at the first index does not verify.
      let other := leaves.set 0 ((leaves.headD #[]).modify 0 (· + 1))
      (Ssz.verifyMerkleMultiproof other proof indices root).toOption === some false
    | .ok _, .error e, .ok _ =>
      -- Every node exists, so only a request with relatives, or of the root, is refused.
      annotate s!"EthLib refused: {repr e}"
      classifyOne "refused" ["REPEATED_INDEX", "NESTED_INDEX", "ROOT_HAS_NO_BRANCH"] e.reason
      ensure (!unrelated indices || indices.contains 1) "a multiproof of existing nodes was refused"
    | _, _, _ => label "no node at an index: nothing checked"

/-! ## Documents near a valid one -/

instance : Inhabited (Gen Lean.Json) := ⟨pure .null⟩

/-- A document with one node changed a little. -/
partial def genJsonNear (document : Lean.Json) : Gen Lean.Json :=
  let here : Gen Lean.Json :=
    match document with
    | .str text => Gen.frequency [
        (2, Lean.Json.str <$> Gen.element [text ++ "0", "0" ++ text, text.toUpper,
          (text.drop 1).toString, (text.dropEnd 1).toString, " " ++ text, "0x" ++ text,
          text ++ "g", ""]),
        -- A byte more, a byte fewer, no byte, a zero byte, every bit set, and an array.
        (3, Lean.Json.str <$> Gen.element [text ++ "00", text ++ "01", "0x", "0x00", "0x01",
          (text.dropEnd 2).toString, (text.dropEnd 2).toString ++ "ff",
          (text.dropEnd 2).toString ++ "00", (text.dropEnd 1).toString ++ "f", text ++ "ff"]),
        (1, Gen.element [.arr #[], .arr #[.str "1"], .num 1, .null])]
    | .bool b => Gen.element [.bool (!b), .str (toString b), .num (if b then 1 else 0), .null]
    | .arr items => Gen.element [.arr (items.push (items.getD 0 (.str "0"))), .arr items.pop,
        .arr items.reverse, .arr (items.push .null), .str "0x"]
    | .obj fields => Gen.element [document.setObjVal! "extra" (.str "1"),
        document.setObjVal! "f0" .null,
        document.setObjVal! "selector" (.str "0"), document.setObjVal! "selector" (.str "128"),
        document.setObjVal! "selector" (.str "2"), document.setObjVal! "selector" (.str "3"),
        document.setObjVal! "selector" (.num 1), .arr #[document], .obj {}, .obj {},
        -- One member fewer.
        Lean.Json.mkObj (fields.toList.drop 1), Lean.Json.mkObj fields.toList.dropLast]
    | other => pure other
  let below : Gen Lean.Json :=
    match document with
    | .arr items =>
      if items.isEmpty then here else do
        let slot ← Gen.nat (.constant 0 (items.size - 1))
        let item ← genJsonNear (items.getD slot .null)
        pure (.arr (items.set! slot item))
    | .obj fields =>
      let names := fields.toList.map (·.1)
      if names.isEmpty then here else do
        let name ← Gen.element names
        let item ← genJsonNear ((document.getObjVal? name).toOption.getD .null)
        pure (document.setObjVal! name item)
    | _ => here
  Gen.frequency [(1, here), (2, below)]

/-- A document with its hexadecimal in lower case and its bare numbers as digits. -/
partial def normalized : Lean.Json → Lean.Json
  | .str text => .str (if text.startsWith "0x" then text.toLower else text)
  | .num n => if n.exponent == 0 && n.mantissa ≥ 0 then .str (toString n.mantissa) else .num n
  | .arr items => .arr (items.map normalized)
  | .obj fields => Lean.Json.mkObj (fields.toList.map fun (name, value) => (name, normalized value))
  | other => other

open Ssz in
/-- A document near the one of a value, with a fault made for the type, at any depth.

- An integer of one more than its width holds.
- A byte vector of a byte more, a byte list of a byte over its limit.
- A bitfield with a padding bit, without its delimiter, with a zero byte after it.
- A list of an element over its limit, a vector of an element fewer.
- A union with a selector it lacks, with no data, or with no member at all. -/
partial def genDocumentFault (depth : Nat) (shape : Desc) (value : Value) : Gen Lean.Json :=
  let valid := (jsonOf shape .opaque value).toOption.getD .null
  let bytes : ByteArray := ⟨(serialize shape value).toOption.getD #[]⟩
  let hexDocument (data : ByteArray) : Lean.Json := .str ("0x" ++ hexOf data.data)
  let here : Gen Lean.Json :=
    match shape, value with
    | .bool, _ => Gen.element [.str "true", .num 1, .null]
    | .uint width, _ => Gen.element [.str (toString (2 ^ (8 * width))),
        .str (toString (2 ^ (8 * width) + 1)), .str "-1", .str "01"]
    | .byteVector _, _ => Gen.element [hexDocument (bytes.push 0),
        hexDocument (bytes.extract 0 (bytes.size - 1)), .arr #[]]
    | .byteList limit, _ =>
      if limit ≤ 600 then
        Gen.element [hexDocument (bytes ++ ⟨Array.replicate (limit + 1 - bytes.size) 0⟩),
          .str "0x0", .arr #[]]
      else Gen.element [.str "0x0", .arr #[]]
    | .bitVector _, _ | .bitList _, _ | .progressiveBitList _, _ =>
      Gen.frequency [(5, hexDocument <$> genTargeted shape bytes), (1, pure (.arr #[]))]
    | .vector _ _, .seq _ =>
      match valid with
      | .arr items => Gen.element [.arr items.pop, .arr (items.push (items.getD 0 .null))]
      | other => pure other
    | .list _ limit, .seq _ =>
      match valid with
      | .arr items =>
        if limit ≤ 600 && limit > 0 then
          pure (.arr (Array.replicate (limit + 1) (items.getD 0 (.str "0"))))
        else pure (.str "0x")
      | other => pure other
    | .compatibleUnion selectors _, _ => do
      let other ← Gen.element (([0, 1, 2, 3, 126, 127, 128] : List Nat).filter
        (!selectors.contains ·))
      Gen.element [valid.setObjVal! "selector" (.str (toString other)), .obj {},
        Lean.Json.mkObj [("selector", .str (toString (selectors.headD 1)))],
        valid.setObjVal! "more" .null]
    | _, _ => pure (.obj {})
  match depth, shape, value with
  | depth + 1, .vector element _, .seq values | depth + 1, .list element _, .seq values
  | depth + 1, .progressiveList element _, .seq values =>
    match valid, values with
    | .arr items, _ :: _ => Gen.frequency [(1, here), (2, do
        let slot ← Gen.nat (.constant 0 (values.length - 1))
        let bad ← genDocumentFault depth element (values.getD slot (.bool false))
        pure (.arr (items.set! slot bad)))]
    | _, _ => here
  | depth + 1, .container names fields, .seq values
  | depth + 1, .progressiveContainer _ names fields, .seq values =>
    Gen.frequency [(1, here), (3, do
      let slot ← Gen.nat (.constant 0 (fields.length - 1))
      let bad ← genDocumentFault depth (fields.getD slot .bool) (values.getD slot (.bool false))
      pure (valid.setObjVal! (names.getD slot "") bad))]
  | depth + 1, .compatibleUnion selectors options, .union selector data =>
    match (selectors.zip options).lookup selector with
    | some option => Gen.frequency [(1, here),
        (1, (valid.setObjVal! "data" ·) <$> genDocumentFault depth option data)]
    | none => here
  | _, _, _ => here

/-- The reasons for which a document holds no value. -/
def jsonReasons : List String :=
  ["WRONG_TYPE", "HEX_PREFIX", "HEX_DIGITS", "HEX_LENGTH", "BITFIELD_PADDING",
    "BITFIELD_DELIMITER", "BITFIELD_TRAILING_ZEROS", "UINT_RANGE", "OVER_LIMIT", "ELEMENT_KIND",
    "NO_DEFAULT", "UNDECLARED_FIELD", "MISSING_FIELD", "STRUCT_NOT_AN_OBJECT",
    "UNDECLARED_SELECTOR", "COUNT", "SCOPE", "EMPTY_ENCODING"]

/-- A document near a valid one, where EthLib reads it, holds the value the specification reads.

So none of these documents is read as a value that the specification does not also read from it:

- A document with a leading zero.
- A document with a padded bitfield.
- A document with a count out of the type.
- A document with an element of another kind. -/
def sszJsonNear (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let valid := (Ssz.jsonOf shape .opaque value).toOption.getD .null
  let document ← forAllWith (·.compress) (Gen.frequency [(3, genJsonNear valid),
    (4, genDocumentFault 3 shape value)])
  pure do
    let cited ← oracle.ask ["sszjsonread", typeText shape, document.compress]
    annotate s!"the specification: {cited}"
    let mine := Ssz.valueOf shape .opaque document
    labelOutcome jsonReasons mine
    classify "the document of the value, unchanged" (document.compress == valid.compress)
    classifyOne "against the specification" ["both read", "both refuse",
        "EthLib refuses what the specification reads"]
      (match mine.toOption.isSome, cited.startsWith "error" with
        | true, _ => "both read"
        | false, true => "both refuse"
        | false, false => "EthLib refuses what the specification reads")
    match Ssz.valueOf shape .opaque document with
    | .error e =>
      -- The specification's reader also takes hex without its marker and other loose spellings.
      --
      -- The vectors of the same repository ask a reader to refuse them.
      --
      -- So a refusal is checked on the one document that must be read: the valid one.
      annotate s!"EthLib refused: {repr e}"
      ensure (document.compress != valid.compress) "the valid document was refused"
    | .ok read =>
      annotate s!"EthLib read {valueText read}"
      ensure (read.fits shape) "a value that does not fit was read"
      (Ssz.serialize shape read).toOption.map (hex ⟨·⟩) === some cited

/-- The document of a value is the one the cited specification writes. -/
def sszJsonCited (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  pure do
    match Ssz.jsonOf shape .opaque value with
    | .ok document =>
      (← oracle.ask ["sszjson", typeText shape, valueText value, document.compress]) === "ok"
    | .error e => failWith s!"no document: {repr e}"

open Ssz in
/-- A type that holds the byte alias, its spelling, and its declaration for the oracle. -/
def genAliased : Gen (Desc × Spelling × String) := do
  let n ← Gen.nat (.constant 1 5)
  Gen.element [
    (.uint 1, .byte, "[\"byte\"]"),
    (.vector (.uint 1) n, .plain [.byte], s!"[\"vec\",[\"byte\"],{n}]"),
    (.list (.uint 1) n, .plain [.byte], s!"[\"list\",[\"byte\"],{n}]"),
    (.progressiveList (.uint 1) none, .plain [.byte], "[\"plist\",[\"byte\"]]"),
    (.container ["a", "b", "c"] [.uint 1, .vector (.uint 1) 2, .uint 1],
      .plain [.byte, .plain [.byte], .opaque],
      "[\"cont\",[\"a\",\"b\",\"c\"],[[\"byte\"],[\"vec\",[\"byte\"],2],[\"uint\",1]]]"),
    (.list (.vector (.uint 1) 2) 3, .plain [.plain [.byte]],
      "[\"list\",[\"vec\",[\"byte\"],2],3]"),
    (.vector (.list (.uint 1) n) 2, .plain [.plain [.byte]],
      s!"[\"vec\",[\"list\",[\"byte\"],{n}],2]"),
    (.compatibleUnion [1, 2] [.uint 1, .uint 1], .plain [.byte, .byte],
      "[\"union\",[1,2],[[\"byte\"],[\"byte\"]]]")]

/-- A value under the byte alias is written as the specification writes it, and reads back. -/
def sszJsonAlias (oracle : Oracle) : Property IO := propertyM do
  let (shape, spelling, declared) ← forAllWith (·.2.2) genAliased
  let value ← forAllWith valueText (genValueOf false shape)
  pure do
    classifyOne "root" ["uint", "Vector", "List", "ProgressiveList", "Container",
      "CompatibleUnion"] (constructorOf shape)
    match Ssz.jsonOf shape spelling value with
    | .ok document =>
      annotate document.compress
      (← oracle.ask ["sszjson", declared, valueText value, document.compress]) === "ok"
      (Ssz.valueOf shape spelling document).toOption.map valueText === some (valueText value)
    | .error e => failWith s!"no document: {repr e}"

/-! ## RLP inputs by their first byte -/

/-- Bytes behind a first byte at the edge of each form of the prefix. -/
def genPrefixed : Gen ByteArray := do
  let first ← Gen.frequency [
    (1, Gen.element [0x7f, 0x80, 0x81, 0x82, 0xb7, 0xb8, 0xb9, 0xba, 0xbf, 0xc0, 0xc1, 0xc2, 0xf7,
      0xf8, 0xf9, 0xff]),
    (1, Gen.integral (.constant 0xb8 0xbf)), (1, Gen.integral (.constant 0xf8 0xff))]
  let rest ← Gen.list (.linear 0 60) (Gen.frequency [(3, Gen.element [0, 1, 55, 56, 0x7f, 0x80,
      0x81, 0xc0]),
    (1, genByte)])
  pure ⟨(first :: rest).toArray⟩

/-- The decoder agrees with the strict references on inputs that start at the edge of a form. -/
def rlpPrefixed (oracle : Oracle) : Property IO := propertyM do
  let input ← forAllWith hex (Gen.frequency [(2, genPrefixed), (1, genHeaded),
    (1, genRlpNear .empty)])
  pure do
    classifyOne "input" inputForms (inputForm input)
    classifyOne "verdict" rlpVerdicts (rlpVerdict (Rlp.decode input))
    let expected ← oracle.ask ["rlpdec", hex input]
    match Rlp.decode input with
    | .ok got => itemText got === expected
    | .error _ => expected === "error"

/-! ## Fields that a fork adds or removes -/

/-- A container with a field from Glamsterdam on and a field until then. -/
structure Staged (fork : Fork) where
  a : UInt16
  b : Since .glamsterdam fork (Ssz.SszList UInt8 4)
  c : Until .glamsterdam fork UInt32
  d : Ssz.SszList UInt16 2

open Ssz in
instance {fork : Fork} : SszType (Staged fork) :=
  SszType.container
    (["a"] ++ sinceNames .glamsterdam fork ["b"] ++ untilNames .glamsterdam fork ["c"] ++ ["d"])
    (fun r => (r.a, r.b, r.c, r.d)) (fun (a, b, c, d) => ⟨a, b, c, d⟩)

end SerializationProperty

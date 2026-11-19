import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Merkle
import Property.Serialization.Misc

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

/-- A declaration that breaks a rule is refused, wherever in a type it sits. -/
def illegalDeclarations : Property IO := pureIO do
  let (rule, inner) ← forAllWith (fun (rule, shape) => s!"{rule}: {typeText shape}") genIllegal
  let shape ← forAllWith typeText (genAround inner)
  ensure shape.wellFormed.toOption.isNone s!"{rule} was accepted"

/-- A declaration names a type exactly when the cited specification lets it. -/
def declarations (oracle : Oracle) : Property IO := propertyM do
  let base ← forAllWith typeText genDesc
  let illegal ← forAllWith (fun (rule, shape) => s!"{rule}: {typeText shape}") genIllegal
  let near ← forAllWith typeText (genNear base)
  let shape ← forAllWith typeText (Gen.frequency [(2, pure near), (1, genAround illegal.2)])
  pure do
    let cited ← oracle.ask ["ssztype", typeText shape]
    annotate cited
    match shape.wellFormed with
    | .ok _ => cited === "ok"
    | .error e =>
      annotate s!"EthLib refused: {repr e}"
      -- The oracle refuses a count of names or selectors by itself, under a name of its own.
      if faultOf cited != "error NOT_AN_INTEGER" then refusal e === faultOf cited

/-- A layout of 256 positions is the widest legal one. -/
def widestLayout : Property IO := pureIO do
  let gaps ← forAll (Gen.nat (.constant 0 254))
  let wide (count : Nat) : Ssz.Desc :=
    .progressiveContainer
      (List.replicate gaps true ++ List.replicate (count - gaps - 1) false ++ [true])
      (fieldNames (gaps + 1)) (List.replicate (gaps + 1) .bool)
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
  let element ← Gen.frequency [(2, genBasic), (1, genDescOf 1)]
  let power ← Gen.element [10, 31, 32, 40, 62]
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
  let index ← forAll (genGindex shape)
  pure do
    encodedText shape value === (← oracle.ask ["sszenc", typeText shape, valueText value])
    let expected ← oracle.ask ["ssznode", typeText shape, valueText value, toString index]
    match Ssz.nodeRoot shape value index with
    | .ok node => hex ⟨node⟩ === expected
    | .error e =>
      annotate s!"the specification: {expected}"
      refusal e === faultOf expected

/-! ## Multiproofs of a value -/

/-- A multiproof built for indices of a value rebuilds its root, by EthLib and by the
specification. -/
def multiproofOfValue (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let indices ← forAll (Gen.list (.linear 1 4) (genGindex shape))
  pure do
    let leaves := indices.mapM (Ssz.nodeRoot shape value)
    match leaves, Ssz.buildMultiproof shape value indices, Ssz.hashTreeRoot shape value with
    | .ok leaves, .ok proof, .ok root =>
      (Ssz.verifyMerkleMultiproof leaves proof indices root).toOption === some true
      hex ⟨root⟩ === (← oracle.ask ["multiroot", nodesText leaves, nodesText proof,
          toString indices])
      -- Another leaf at the first index does not verify.
      let other := leaves.set 0 ((leaves.headD #[]).modify 0 (· + 1))
      (Ssz.verifyMerkleMultiproof other proof indices root).toOption === some false
    | .ok _, .error e, .ok _ =>
      -- Every node exists, so only a request with relatives, or of the root, is refused.
      annotate s!"EthLib refused: {repr e}"
      ensure (!unrelated indices || indices.contains 1) "a multiproof of existing nodes was refused"
    | _, _, _ => pure ()

/-! ## Documents near a valid one -/

instance : Inhabited (Gen Lean.Json) := ⟨pure .null⟩

/-- A document with one node changed a little. -/
partial def genJsonNear (document : Lean.Json) : Gen Lean.Json :=
  let here : Gen Lean.Json :=
    match document with
    | .str text => Lean.Json.str <$> Gen.element [text ++ "0", "0" ++ text, text.toUpper,
        (text.drop 1).toString,
        (text.dropEnd 1).toString, text ++ "00", " " ++ text, "0x" ++ text, text ++ "g", ""]
    | .bool b => Gen.element [.bool (!b), .str (toString b), .num (if b then 1 else 0), .null]
    | .arr items => Gen.element [.arr (items.push (items.getD 0 (.str "0"))), .arr items.pop,
        .arr items.reverse, .arr (items.push .null), .str "0x"]
    | .obj _ => Gen.element [document.setObjVal! "extra" (.str "1"), document.setObjVal! "f0" .null,
        document.setObjVal! "selector" (.str "0"), document.setObjVal! "selector" (.str "128"),
        document.setObjVal! "selector" (.num 1), .arr #[document], .obj {}]
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

/-- A document near a valid one, where EthLib reads it, holds the value the specification reads.

So no document with a leading zero, a padded bitfield, a count out of the type or an element
of another kind is read as a value that the specification does not also read from it. -/
def sszJsonNear (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let valid := (Ssz.jsonOf shape .opaque value).toOption.getD .null
  let document ← forAllWith (·.compress) (genJsonNear valid)
  pure do
    let cited ← oracle.ask ["sszjsonread", typeText shape, document.compress]
    annotate s!"the specification: {cited}"
    match Ssz.valueOf shape .opaque document with
    | .error e =>
      -- The reader of the specification also takes hex without its marker and other loose
      -- spellings, which the vectors of the same repository ask a reader to refuse.
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
    match Ssz.jsonOf shape spelling value with
    | .ok document =>
      annotate document.compress
      (← oracle.ask ["sszjson", declared, valueText value, document.compress]) === "ok"
      (Ssz.valueOf shape spelling document).toOption.map valueText === some (valueText value)
    | .error e => failWith s!"no document: {repr e}"

/-! ## RLP inputs by their first byte -/

/-- Bytes behind a first byte at the edge of each form of the prefix. -/
def genPrefixed : Gen ByteArray := do
  let first ← Gen.element [0x7f, 0x80, 0x81, 0x82, 0xb7, 0xb8, 0xb9, 0xba, 0xbf, 0xc0, 0xc1, 0xc2,
      0xf7,
    0xf8, 0xf9, 0xff]
  let rest ← Gen.list (.linear 0 60) (Gen.frequency [(3, Gen.element [0, 1, 55, 56, 0x7f, 0x80,
      0x81, 0xc0]),
    (1, genByte)])
  pure ⟨(first :: rest).toArray⟩

/-- The decoder agrees with the strict references on inputs that start at the edge of a form. -/
def rlpPrefixed (oracle : Oracle) : Property IO := propertyM do
  let input ← forAllWith hex genPrefixed
  pure do
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

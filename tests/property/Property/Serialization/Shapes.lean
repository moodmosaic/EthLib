import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Classes
import Property.Serialization.Merkle
import Property.Serialization.Rooted
import Property.Serialization.Params
import Property.Serialization.Near
import EthLib.Serialization.Ssz

/-!
# SSZ at every width, length, limit, fork and hasher

- An integer of every width in bytes, not only the six that name a type.
- The root of a value under another hasher, and with a budget of nesting.
- A typed collection of every element type, at lengths around a byte and a node.
- A fork-chosen list, bitlist and container at every pair of forks.
- A rooted vector of every length, and a rooted list at every pair of forks.
- Generalized indices: a spine from any node, a branch under any hash.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Serialization EthLib.Serialization.Ssz

namespace SerializationProperty

/-! ## Integers of every width -/

/-- An integer of any width in bytes has the bytes and the root of the model.

The specification names six widths, and the code takes any: each is tested.

The typed writer and reader of an integer agree with the untyped ones. -/
def sszUintWidths (oracle : Oracle) : Property IO := propertyM do
  let width ← forAll (Gen.frequency [(2, Gen.element [1, 2, 4, 8, 16, 32]),
    (2, Gen.element [0, 3, 5, 6, 7, 9, 12, 20, 24, 31, 33, 40, 48, 64, 65]),
    (1, Gen.nat (.linear 0 70))])
  let n ← forAll (Gen.frequency [(4, genNatBits (8 * width)),
    (1, (2 ^ (8 * width) + ·) <$> Gen.nat (.linear 0 3))])
  let front ← forAllWith hex (genBytes (.linear 0 3))
  pure do
    let fits := n < 2 ^ (8 * width)
    classifyOne "width" ["one of the six", "0", "another up to 32", "more than 32"]
      (if [1, 2, 4, 8, 16, 32].contains width then "one of the six" else if width == 0 then "0"
        else if width ≤ 32 then "another up to 32" else "more than 32")
    classify "the value fits" fits
    classify "the value does not fit" (!fits)
    classify "the value: the greatest of the width" (n + 1 == 2 ^ (8 * width))
    let expected ← oracle.ask ["uintmodel", toString width, toString n]
    let shape := Desc.uint width
    uintFits width n === fits
    match serialize shape (.uint n), hashTreeRoot shape (.uint n) with
    | .ok bytes, .ok root =>
      s!"{hex ⟨bytes⟩} {hex ⟨root⟩}" === expected
      hex ⟨uintBytes width n⟩ === hex ⟨bytes⟩
      (deserialize shape bytes).toOption.map valueText === some (valueText (.uint n))
      ensure (deserialize shape (bytes.push 0)).toOption.isNone "a byte too many was read"
      ensure (width == 0 || (deserialize shape bytes.pop).toOption.isNone) "a byte too few"
      -- The reader of an integer inside other bytes.
      readUint (front.data ++ bytes) front.size width === n
      readUintBytes (front ++ ⟨bytes⟩) front.size width === n
      -- The typed writer and reader.
      (SszType.encodeUint width n).toOption.map hex === some (hex ⟨bytes⟩)
      (SszType.decodeUint width id ⟨bytes⟩).toOption === some n
      ensure (SszType.decodeUint width id ⟨bytes.push 0⟩).toOption.isNone "the typed reader"
      (SszType.ofUint width id (.uint n)).toOption === some n
    | .error e, _ =>
      expected === "error"
      e.reason === "WRONG_TYPE"
      ensure (hashTreeRoot shape (.uint n)).toOption.isNone "a root of a value that does not fit"
      ensure (SszType.ofUint width id (.uint n)).toOption.isNone "the typed value"
    | .ok _, .error e => failWith s!"bytes and no root: {repr e}"

/-! ## The fixed part of a struct, read from any position -/

/-- The fixed part of a struct reads from any position of any bytes, or says what is missing.

`deserialize` checks the size of a struct first, so it never meets bytes that end inside it.

The readers are called here directly, where they do.

The spans between offsets are the differences, and an offset that goes back is refused. -/
def sszSlots : Property Id := property do
  let fields ← forAllWith (fun fields => jsonArray (fields.map typeText))
    (Gen.list (.linear 0 5) (Gen.frequency [(2, genBasic), (1, genDescOf 1)]))
  let leading := Desc.leadingWidth fields
  let position ← forAll (Gen.frequency [(2, pure 0), (1, Gen.nat (.constant 1 5))])
  let size ← forAll (Gen.frequency [(3, pure (position + leading)),
    (2, Gen.nat (.constant 0 (position + leading))), (1, pure (position + leading + 3))])
  let data ← forAllWith hex (genBytesN size)
  let offsets ← forAll (Gen.frequency [(1, pure []),
    (6, Gen.list (.constant 1 5) (Gen.nat (.linear 0 40)))])
  let scope ← forAll (Gen.nat (.linear 0 45))
  -- The model: walk the fields, each at the end of the one before.
  let walk := fields.foldl (fun (state : Nat × Option (Nat × Nat) × List String) field =>
    let width := field.fixedSize.getD bytesPerOffset
    let (at', fault, slots) := state
    if fault.isSome then state
    else if at' + width > size then (at', some (at' + width, size), slots)
    else (at' + width, none, slots ++ [
      if field.isFixed then s!"inline {hex (data.extract at' (at' + width))}"
      else s!"body {readOffset data at'}"])) (position, none, [])
  let shown (slot : Slot) : String :=
    match slot with
    | .inline bytes => s!"inline {hex ⟨bytes⟩}"
    | .body start => s!"body {start}"
  let showTyped (slot : ByteSlot) : String :=
    match slot with
    | .inline bytes => s!"inline {hex bytes}"
    | .body start => s!"body {start}"
  classify "the bytes hold the fixed part" walk.2.1.isNone
  classify "the bytes end inside the fixed part: TRUNCATED" walk.2.1.isSome
  classify "from a position past the start" (position > 0)
  classify "a field of variable size" (fields.any (!·.isFixed))
  match readSlots fields data.data position with
  | .ok (slots, ending) => (slots.map shown, ending, none) === (walk.2.2, walk.1, walk.2.1)
  | .error (.truncated needed available) => some (needed, available) === walk.2.1
  | .error e => failWith s!"another error: {repr e}"
  match readByteSlots fields data position with
  | .ok (slots, ending) => (slots.map showTyped, ending, none) === (walk.2.2, walk.1, walk.2.1)
  | .error (.truncated needed available) => some (needed, available) === walk.2.1
  | .error e => failWith s!"another error: {repr e}"
  -- The budget of a struct: its width exactly when fixed, else at least its fixed part.
  (structBudget fields scope).toOption.isSome ===
    (match Desc.fieldsFixedSize fields with
      | some width => scope == width
      | none => scope ≥ leading)
  -- The spans of bodies: each to the next offset, the last to the end of the bytes.
  let pairs := offsets.zip (offsets.drop 1 ++ [scope])
  let back := pairs.find? fun (start, next) => next < start
  classifyOne "offsets" ["none", "in order within the bytes", "one goes back",
      "the last is past the end"]
    (if offsets.isEmpty then "none" else match back with
      | none => "in order within the bytes"
      | some (start, _) =>
        if pairs.getLast? == back && start > scope then "the last is past the end"
        else "one goes back")
  match offsetSpans offsets scope with
  | .ok spans =>
    ensure back.isNone "spans of offsets that go back"
    spans === pairs.map fun (start, next) => next - start
  | .error (.offsetUnordered start next) => some (start, next) === back
  | .error (.offsetPastScope start limit) =>
    (some (start, limit), limit) === (back, scope)
  | .error e => failWith s!"another error: {repr e}"

/-! ## Values that fit a type, and values that do not -/

instance : Inhabited (Gen Value) := ⟨pure (.bool false)⟩

/-- A value near a value of a type, and whether a struct in it has lost or gained a field.

A count, a width or a selector is changed by one, at the root or inside a part. -/
partial def genNearValue (depth : Nat) (shape : Desc) (value : Value) : Gen (Value × Bool) :=
  let plain (changed : Gen Value) : Gen (Value × Bool) := (·, false) <$> changed
  let here : Gen (Value × Bool) :=
    match shape, value with
    | .uint width, _ => plain (Value.uint <$> Gen.element [2 ^ (8 * width), 2 ^ (8 * width) - 1,
        2 ^ (8 * width) + 5])
    | .byteVector _, .bytes data => plain (Gen.element [.bytes (data.push 0), .bytes data.pop])
    | .byteList limit, .bytes data =>
      plain (pure (.bytes (if limit ≤ 600 then data ++ Array.replicate (limit + 1 - data.size) 0
        else data)))
    | .bitVector _, .bits data => plain (Gen.element [.bits (data.push true), .bits data.pop])
    | .bitList limit, .bits data =>
      plain (pure (.bits (if limit ≤ 600 then data ++ Array.replicate (limit + 1 - data.size) true
        else data)))
    | .vector _ _, .seq values => plain (Gen.element [.seq (values ++ values.take 1),
        .seq values.dropLast])
    | .list _ limit, .seq values =>
      plain (pure (if limit ≤ 600 && !values.isEmpty then
        .seq (values ++ List.replicate (limit + 1 - values.length) (values.headD (.bool false)))
        else .seq values))
    | .container _ _, .seq values | .progressiveContainer _ _ _, .seq values =>
      (·, true) <$> Gen.element [.seq values.dropLast, .seq (values ++ values.take 1)]
    | .compatibleUnion selectors _, .union _ data => do
      let other ← Gen.element (([0, 1, 2, 3, 126, 127, 128] : List Nat).filter
        (!selectors.contains ·))
      pure (.union other data, false)
    | _, other => plain (pure other)
  match depth, shape, value with
  | depth + 1, .vector element _, .seq values | depth + 1, .list element _, .seq values
  | depth + 1, .progressiveList element _, .seq values =>
    if values.isEmpty then here
    else Gen.frequency [(1, here), (2, do
      let slot ← Gen.nat (.constant 0 (values.length - 1))
      let (bad, struct) ← genNearValue depth element (values.getD slot (.bool false))
      pure (.seq (values.set slot bad), struct))]
  | depth + 1, .container _ fields, .seq values
  | depth + 1, .progressiveContainer _ _ fields, .seq values =>
    Gen.frequency [(1, here), (3, do
      let slot ← Gen.nat (.constant 0 (fields.length - 1))
      let (bad, struct) ← genNearValue depth (fields.getD slot .bool)
        (values.getD slot (.bool false))
      pure (.seq (values.set slot bad), struct))]
  | depth + 1, .compatibleUnion selectors options, .union selector data =>
    match (selectors.zip options).lookup selector with
    | some option => Gen.frequency [(1, here), (1, do
        let (bad, struct) ← genNearValue depth option data
        pure (.union selector bad, struct))]
    | none => here
  | _, _, _ => here

/-- A value fits its type exactly when it has bytes, a root and a document.

The reference takes it exactly then.

The values are near ones of the type: a count, a width or a selector off by one, at any depth. -/
def sszFits (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let (near, struct) ← forAllWith (fun pair => valueText pair.1)
    (Gen.frequency [(1, pure (value, false)), (5, genNearValue 3 shape value)])
  pure do
    let fits := near.fits shape
    classify "the value fits" fits
    classify "the value does not fit" (!fits)
    classifyOne "does not fit, refused as" ["nothing: it fits", "WRONG_TYPE", "LIMIT", "SCOPE",
        "UNKNOWN_SELECTOR"]
      (match serialize shape near with
        | .ok _ => "nothing: it fits"
        | .error e => e.reason)
    classify "a struct with a value too few or too many" struct
    (serialize shape near).toOption.isSome === fits
    (hashTreeRoot shape near).toOption.isSome === fits
    (jsonOf shape .opaque near).toOption.isSome === fits
    -- The oracle pairs the fields of a struct with what values it is given.
    --
    -- So it is not asked about a struct of another count.
    if !struct then
      let cited ← oracle.ask ["sszenc", typeText shape, valueText near]
      annotate s!"the reference: {cited}"
      (!cited.startsWith "error") === fits
      if fits then encodedText shape near === cited

/-- The value with every integer, byte and bit set to zero, and its counts as they were.

It is the default only when every list in it holds nothing. -/
partial def zeroed : Desc → Value → Value
  | _, .bool _ => .bool false
  | _, .uint _ => .uint 0
  | _, .bytes data => .bytes (data.map fun _ => 0)
  | _, .bits data => .bits (data.map fun _ => false)
  | .vector element _, .seq values | .list element _, .seq values
  | .progressiveList element _, .seq values => .seq (values.map (zeroed element))
  | .container _ fields, .seq values | .progressiveContainer _ _ fields, .seq values =>
    .seq ((fields.zip values).map fun (field, value) => zeroed field value)
  | .compatibleUnion selectors options, .union selector data =>
    .union selector (zeroed (((selectors.zip options).lookup selector).getD .bool) data)
  | _, other => other

/-- A value is the zero of its type exactly when the specification says so.

The value is the default, the default with one part changed, or any value.

A type that holds a union has no default, and is refused under the name of the specification. -/
def sszIsZero (oracle : Oracle) : Property IO := propertyM do
  let shape ← forAllWith typeText genDesc
  let zero := shape.default.toOption
  let any ← forAllWith valueText (genValueOf true shape)
  let near ← forAllWith (fun pair => valueText pair.1) (genNearValue 3 shape (zero.getD any))
  let value ← forAllWith valueText (Gen.element [zero.getD any, any, zeroed shape any,
    zeroed shape any, if near.1.fits shape then near.1 else any])
  pure do
    let mine := shape.isZero value
    classifyOne "verdict" ["zero", "not zero", "no default: a union inside"]
      (match mine with
        | .ok true => "zero"
        | .ok false => "not zero"
        | .error _ => "no default: a union inside")
    classify "not zero, and every integer, byte and bit in it is zero"
      (mine.toOption == some false && valueText (zeroed shape value) == valueText value)
    let expected ← oracle.ask ["ssziszero", typeText shape, valueText value]
    match mine with
    | .ok verdict => toString verdict === expected
    | .error e => refusal e === faultOf expected

/-! ## The hasher, and the budget of nesting -/

/-- The root of a value under another hasher is the root of the tree model under that hash.

The hasher runs in a monad that counts its calls, so the monadic path is the one tested. -/
def sszHasher (oracle : Oracle) : Property IO := propertyM do
  let (shape, value) ← forAllWith typedText genTyped
  let name ← forAll (Gen.element ["sha256", "twice", "toy"])
  pure do
    classifyOne "hash" ["sha256", "twice", "toy"] name
    classifyAny "root" treeUniverse (treeClasses shape value)
    let counted (data : ByteArray) : StateM Nat ByteArray := do
      modify (· + 1)
      pure (namedHash name data)
    let (result, calls) := Id.run ((hashTreeRootM (Hasher.ofHash counted) shape value).run.run 0)
    classifyOne "calls of the hash" ["0", "1 to 9", "10 to 99", "100 or more"]
      (if calls == 0 then "0" else if calls < 10 then "1 to 9" else if calls < 100 then "10 to 99"
        else "100 or more")
    let expected ← oracle.ask ["modelnode", name, typeText shape, valueText value, "1"]
    match result with
    | .ok root => hex ⟨root⟩ === expected
    | .error e => failWith s!"no root: {repr e}"
    -- The same hash without a monad, and SHA-256 with its table of zero roots.
    let pure := (hashTreeRootM (m := Id) (Hasher.ofHash (namedHash name)) shape value).run
    pure.toOption.map (hex ⟨·⟩) === some expected
    if name == "sha256" then (hashTreeRoot shape value).toOption.map (hex ⟨·⟩) === some expected

open Ssz in
/-- The levels of types that the root of a value reads: one, and those of the values it holds. -/
partial def reach : Desc → Value → Nat
  | .vector element _, .seq values | .list element _, .seq values
  | .progressiveList element _, .seq values =>
    if element.isBasic then 1 else 1 + (values.map (reach element)).foldl max 0
  | .container _ fields, .seq values | .progressiveContainer _ _ fields, .seq values =>
    1 + ((fields.zip values).map fun (field, value) => reach field value).foldl max 0
  | .compatibleUnion selectors options, .union selector data =>
    match (selectors.zip options).lookup selector with
    | some option => 1 + reach option data
    | none => 1
  | _, _ => 1

/-- A root with a budget of nesting is the root, exactly when the budget reaches the value. -/
def sszBudget : Property Id := property do
  let (shape, value) ← forAllWith typedText genTyped
  let needed := reach shape value
  let budget ← forAll (Gen.frequency [(2, Gen.nat (.constant 0 (shape.nesting + 1))),
    (1, pure needed), (1, pure (needed - 1)), (2, Gen.nat (.constant needed shape.nesting))])
  classifyOne "budget" ["under what the value needs", "what the value needs",
      "between that and the nesting of the type", "the nesting of the type or more"]
    (if budget < needed then "under what the value needs"
      else if budget == needed then "what the value needs"
      else if budget < shape.nesting then "between that and the nesting of the type"
      else "the nesting of the type or more")
  ensure (needed ≤ shape.nesting) "a value deeper than its type"
  match hashTreeRootAt budget shape value with
  | .ok root =>
    ensure (budget ≥ needed) "a root under the budget the value needs"
    (hashTreeRoot shape value).toOption.map (hex ⟨·⟩) === some (hex ⟨root⟩)
  | .error e =>
    e.reason === "PROOF_INCOMPLETE"
    ensure (budget < needed) "no root with the budget the value needs"

/-! ## Typed collections of every element type and length -/

instance : Element UInt8 := { make := UInt8.ofNat }
instance : Element UInt32 := { make := fun n => UInt32.ofNat (n * 65537) }
instance : Element (BitVec 128) := { make := fun n => BitVec.ofNat 128 (n * 2 ^ 100 + n) }
instance : Element (SszList UInt16 3) :=
  { make := fun n => ⟨((List.range (n % 4)).map fun i => UInt16.ofNat (n + i)).toArray,
      by simp; omega⟩ }

/-- The typed value of an untyped one has the bytes and the root of the reference.

It gives its untyped value back, and it reads back from its bytes. -/
def typedAgrees (oracle : Oracle) (α : Type) [SszType α] (value : Value) : TestT IO Unit := do
  let shape := SszType.desc α
  match SszType.ofValue (α := α) value with
  | .error e => failWith s!"a value of the type was refused: {repr e}"
  | .ok typed =>
    let expected ← oracle.ask ["sszenc", typeText shape, valueText value]
    typedEncoded typed === expected
    valueText (SszType.toValue typed) === valueText value
    match SszType.encode typed >>= SszType.decode (α := α) with
    | .ok back => typedEncoded back === expected
    | .error e => failWith s!"the bytes do not read back: {repr e}"
    -- The typed path to the root is the root.
    (SszType.getGeneralizedIndex α []).toOption === some 1
    -- The root as a node of 32 bytes.
    (SszType.hashTreeRoot typed).toOption.map (fun node => hex ⟨node.toArray⟩) ===
      (hashTreeRoot shape value).toOption.map (hex ⟨·⟩)

/-- The element types of a typed collection, by name. -/
def elementNames : List String :=
  ["boolean", "uint8", "uint16", "uint32", "uint64", "uint128", "uint256", "Bytes32",
    "a container", "a list", "a bitlist", "a type chosen by a condition"]

/-- A continuation run at the element type of a number. -/
def withElement {β : Type} (element : Nat) (k : (α : Type) → [SszType α] → β) : β :=
  match element with
  | 0 => k Bool
  | 1 => k UInt8
  | 2 => k UInt16
  | 3 => k UInt32
  | 4 => k UInt64
  | 5 => k (BitVec 128)
  | 6 => k U256
  | 7 => k (Vector UInt8 32)
  | 8 => k Pair
  | 9 => k (SszList UInt16 3)
  | 10 => k (Bitlist 9)
  | _ => k (if element = 11 then Bitvector 3 else UInt16)

/-- The typed collections, by name. -/
def collectionNames : List String :=
  ["Vector", "SszList", "ProgressiveList", "Bitvector", "Bitlist", "ProgressiveBitlist",
    "Vector UInt8", "SszList UInt8", "RootedVector", "Rooted"]

/-- A continuation run at the collection of a number, of an element type and a length. -/
def withCollection {β : Type} (kind n : Nat) (α : Type) [SszType α]
    (k : (γ : Type) → [SszType γ] → β) : β :=
  match kind with
  | 0 => k (Vector α (max n 1))
  | 1 => k (SszList α n)
  | 2 => k (ProgressiveList α)
  | 3 => k (Bitvector (max n 1))
  | 4 => k (Bitlist n)
  | 5 => k ProgressiveBitlist
  | 6 => k (Vector UInt8 (max n 1))
  | 7 => k (SszList UInt8 n)
  | 8 => k (RootedVector α (max n 1))
  | _ => k (Rooted (SszList α n))

/-- A length at the edges of a byte and of a node, or a small one. -/
def genSize : Gen Nat :=
  Gen.frequency [(3, Gen.element [0, 1, 2, 7, 8, 9, 31, 32, 33, 255, 256, 257]),
    (1, Gen.nat (.linear 0 70))]

/-- A typed collection of every element type and length agrees with the reference.

The lengths and limits are those around a byte and a node: 0, 1, 7, 8, 9, 31 to 33, 255 to 257. -/
def typedCollections (oracle : Oracle) : Property IO := propertyM do
  -- The three collections of bits twice as often: each has eight lengths to reach.
  let kind ← forAll (Gen.frequency [(2, Gen.nat (.constant 0 (collectionNames.length - 1))),
    (1, Gen.element [3, 4, 5])])
  let element ← forAll (Gen.nat (.constant 0 (elementNames.length - 1)))
  let n ← forAll genSize
  -- A long sequence of large elements costs much and shows nothing a short one does not.
  let n := if [0, 1, 2, 8, 9].contains kind && element ≥ 7 then min n 33 else n
  let shape := withElement element fun α => withCollection kind n α fun γ => SszType.desc γ
  let value ← forAllWith valueText (genValueOf true shape)
  pure do
    classifyOne "collection" collectionNames (collectionNames.getD kind "")
    if [0, 1, 2, 8, 9].contains kind then
      classifyOne "element" elementNames (elementNames.getD element "")
    let sizes := (bitEdges ++ [2, 31, 32, 33]).map toString
    classifyOne "length or limit" (sizes ++ ["another"])
      (if sizes.contains (toString n) then toString n else "another")
    classifyAny "holds" valueUniverse.dropLast (valueClasses shape value)
    -- The limits here are small: no tree has a zero subtree deeper than nine levels.
    classifyAny "root" (treeUniverse.filter fun name =>
      !(name.startsWith "asks" || ["zero subtree: 32 to 63", "zero subtree: 64",
        "zero subtree: 65 or more"].contains name)) (treeClasses shape value)
    withElement element fun α => withCollection kind n α fun γ => typedAgrees oracle γ value

/-- A text of at most a count of bytes is a byte list, and bytes that spell no text are none. -/
def typedString (oracle : Oracle) : Property IO := propertyM do
  let limit ← forAll genSize
  let text ← forAll (Gen.string (.linear 0 12) (Gen.frequency [(3, Gen.alphaNum),
    (1, Gen.unicode)]))
  let raw ← forAllWith hex (Gen.frequency [(3, pure text.toUTF8),
    (1, genBytes (.linear 0 6)),
    (1, (text.toUTF8 ++ ·) <$> Gen.element [⟨#[0x80]⟩, ⟨#[0xc0, 0x80]⟩, ⟨#[0xed, 0xa0, 0x80]⟩,
      ⟨#[0xf4, 0x90, 0x80, 0x80]⟩, ⟨#[0xe2, 0x82]⟩])])
  pure do
    let valid := (String.fromUTF8? raw).isSome
    let read := SszType.ofValue (α := SszString limit) (.bytes raw.data)
    classifyOne "bytes" ["a text within the limit", "a text over the limit", "no text"]
      (if !valid then "no text" else if raw.size ≤ limit then "a text within the limit"
        else "a text over the limit")
    match read with
    | .ok typed =>
      ensure (valid && raw.size ≤ limit) "bytes that are no text of the type were read"
      hex typed.text.toUTF8 === hex raw
      typedAgrees oracle (SszString limit) (.bytes raw.data)
    | .error e =>
      ensure (!valid || raw.size > limit) s!"a text of the type was refused: {repr e}"
      e.reason === (if raw.size > limit then "LIMIT" else e.reason)

/-! ## Every pair of forks -/

/-- A container that a fork turns into a progressive one. -/
structure Forked (switch fork : Fork) where
  a : UInt16
  b : SszList UInt8 4
  c : Bitvector 3

instance {switch fork : Fork} : SszType (Forked switch fork) :=
  SszType.forkContainer switch fork [true, false, true, true] ["a", "b", "c"]
    (fun r => (r.a, r.b, r.c)) (fun (a, b, c) => ⟨a, b, c⟩)

/-- A container with a field from a fork on, one until a fork, and one between the two. -/
structure Phased (first last fork : Fork) where
  a : UInt16
  b : Since first fork (SszList UInt8 4)
  c : Until last fork UInt32
  d : During first last fork (Bitlist 5)
  e : SszList UInt16 2

instance {first last fork : Fork} : SszType (Phased first last fork) :=
  SszType.container
    (["a"] ++ sinceNames first fork ["b"] ++ untilNames last fork ["c"] ++
      duringNames first last fork ["d"] ++ ["e"])
    (fun r => (r.a, r.b, r.c, r.d, r.e)) (fun (a, b, c, d, e) => ⟨a, b, c, d, e⟩)

/-- The types that a fork changes, by name. -/
def forkedNames : List String :=
  ["ForkList", "ForkList UInt8", "ForkBitlist", "RootedForkList", "a fork container",
    "a container with fields of forks"]

/-- A continuation run at the type of a number, at forks, with an element type and a limit. -/
def withForked {β : Type} (kind : Nat) (first last fork : Fork) (limit : Nat) (α : Type)
    [SszType α] (k : (γ : Type) → [SszType γ] → β) : β :=
  match kind with
  | 0 => k (ForkList first fork α limit)
  | 1 => k (ForkList first fork UInt8 limit)
  | 2 => k (ForkBitlist first fork limit)
  | 3 => k (RootedForkList first fork α limit)
  | 4 => k (Forked first fork)
  | _ => k (Phased first last fork)

/-- A type that a fork changes agrees with the reference at every fork.

The switch, the first fork and the last fork of a field are each any fork. -/
def typedForks (oracle : Oracle) : Property IO := propertyM do
  let place (pair : Fork × Nat) := toString pair.2
  let (first, firstAt) ← forAllWith place genFork
  let (last, lastAt) ← forAllWith place genFork
  let (fork, forkAt) ← forAllWith place (Gen.frequency [(2, genFork),
    (1, pure (first, firstAt)), (1, pure (last, lastAt))])
  let kind ← forAll (Gen.nat (.constant 0 (forkedNames.length - 1)))
  let element ← forAll (Gen.nat (.constant 0 (elementNames.length - 1)))
  let limit ← forAll (Gen.element [0, 1, 2, 3, 4, 5, 8, 9, 33])
  let shape := withElement element fun α =>
    withForked kind first last fork limit α fun γ => SszType.desc γ
  let value ← forAllWith valueText (genValueOf true shape)
  pure do
    classifyOne "type" forkedNames (forkedNames.getD kind "")
    classifyOne "the fork is" ["before the first", "the first", "after the first"]
      (if forkAt < firstAt then "before the first" else if forkAt == firstAt then "the first"
        else "after the first")
    classifyOne "and" ["before the last", "the last", "after the last"]
      (if forkAt < lastAt then "before the last" else if forkAt == lastAt then "the last"
        else "after the last")
    classifyOne "root" ["ByteList", "Bitlist", "ProgressiveBitlist", "List", "ProgressiveList",
      "Container", "ProgressiveContainer"] (constructorOf shape)
    allForks.zipIdx.forM fun (_, at') => classify s!"at fork {at'}" (forkAt == at')
    ensure shape.wellFormed.toOption.isSome "the type is not well formed"
    withElement element fun α =>
      withForked kind first last fork limit α fun γ => typedAgrees oracle γ value

/-- A rooted list keeps its tree under writes, at every pair of forks and at every limit.

Before the switch it is a list under a limit, up to `2 ^ 70`; from it on, a progressive list. -/
def listEveryFork (oracle : Oracle) (α : Type) [Element α] (elementType : String) :
    Property IO := propertyM do
  let place (pair : Fork × Nat) := toString pair.2
  let (switch, switchAt) ← forAllWith place genFork
  let (fork, forkAt) ← forAllWith place (Gen.frequency [(2, genFork), (1, pure (switch, switchAt))])
  let limit ← forAll (Gen.frequency [(3, Gen.element [1, 2, 3, 4, 5, 8, 9, 33, 100]),
    (2, (2 ^ ·) <$> Gen.element [10, 32, 63, 64, 65, 70]),
    (1, (2 ^ · + 1) <$> Gen.element [10, 32, 63, 64, 65, 70])])
  let bounded := forkAt < switchAt
  let typeOf :=
    if bounded then s!"[\"list\",{elementType},{limit}]" else s!"[\"plist\",{elementType}]"
  let test ← ((listMachine oracle switch fork α limit typeOf).property (.linear 1 25)).test
  pure do
    classify "before the switch: a list under a limit" bounded
    classify "at the switch" (forkAt == switchAt)
    classify "after the switch: a progressive list" (!bounded && forkAt != switchAt)
    classifyOne "limit" ["up to 100", "2^10 to 2^63 + 1", "2^64 or more"]
      (if limit ≤ 100 then "up to 100" else if limit < 2 ^ 64 then "2^10 to 2^63 + 1"
        else "2^64 or more")
    test

/-- A write to a rooted vector. -/
inductive VectorStep where
  | set (index number : Nat)
  | shift (fresh : List Nat)
  | reload
  deriving Repr

/-- A rooted vector of every length keeps its tree under writes.

After each write the kept tree is the tree built afresh, and at the end the reference agrees. -/
def vectorEveryLength (oracle : Oracle) (α : Type) [Element α] (elementType : String)
    (most : Nat := 257) : Property IO := propertyM do
  -- Six leaves are neither a power of two nor one over: a length that fills them is drawn too.
  let perLeaf := if (SszType.desc α).isBasic then 32 / (SszType.desc α).itemLength else 1
  let length ← forAll (Gen.frequency [
    (3, Gen.element ([1, 2, 3, 4, 5, 7, 8, 9, 31, 32, 33, 63, 64, 65, 255, 256, 257,
      6 * perLeaf - 1, 6 * perLeaf].filter (· ≤ most))),
    (1, Gen.nat (.linear 1 (min most 70)))])
  let start ← forAll (Gen.list (.singleton length) (Gen.nat (.linear 0 255)))
  let steps ← forAll (Gen.list (.linear 0 8) (Gen.frequency [
    (4, Gen.zipWith VectorStep.set (Gen.frequency [(2, Gen.nat (.constant 0 (length - 1))),
      (1, Gen.element [0, length - 1])]) (Gen.nat (.linear 0 9999))),
    (2, VectorStep.shift <$> Gen.frequency [
      (3, Gen.list (.linear 0 (min length 6)) (Gen.nat (.linear 0 255))),
      (1, Gen.list (.constant (length - 1) length) (Gen.nat (.linear 0 255)))]),
    (1, pure .reload)]))
  pure do
    let element := SszType.desc α
    let leavesOf (count : Nat) :=
      if element.isBasic then (count * element.itemLength + 31) / 32 else count
    let classOf (leaves : Nat) :=
      if leaves == 1 then "one" else if isPow2 leaves then "a power of two"
      else if isPow2 (leaves - 1) then "one over a power of two" else "another count"
    -- Only the classes that a length up to the greatest one gives are listed.
    classifyOne "leaves" (((List.range most).map fun n => classOf (leavesOf (n + 1))).eraseDups)
      (classOf (leavesOf length))
    if element.isBasic && element.itemLength < 32 then
      classify "the last leaf is not full" (length * element.itemLength % 32 != 0)
    classify "steps: none" steps.isEmpty
    let mut vector : RootedVector α length :=
      .ofVector (Vector.ofFn fun i => Element.make (start.getD i.val 0))
    let mut model := start
    for step in steps do
      match step with
      | .set index number =>
        if inside : index < length then
          label "step: set"
          vector := vector.set index (Element.make number) inside
          model := model.set index number
      | .shift fresh =>
        if le : fresh.length ≤ length then
          label "step: shift"
          let added : Vector α fresh.length :=
            Vector.ofFn fun i => Element.make (fresh.getD i.val 0)
          vector := vector.shift added le
          model := model.drop fresh.length ++ fresh
      | .reload =>
        label "step: reload"
        match SszType.encode vector >>= SszType.decode (α := RootedVector α length) with
        | .ok fresh => vector := fresh
        | .error e => failWith s!"the vector does not read back: {repr e}"
      -- The tree kept through the write is the tree of the elements built afresh.
      typedEncoded vector === typedEncoded (RootedVector.ofVector vector.elements)
    typedEncoded vector === (← oracle.ask ["sszenc", s!"[\"vec\",{elementType},{length}]",
      elementsText α model])

/-! ## Generalized indices and branches -/

/-- The node of a chunk on a progressive spine is the one of EIP-7916, from any spine node.

The path and the branch of an index, and the join of two indices, are those of the text. -/
def gindexArithmetic (oracle : Oracle) : Property IO := propertyM do
  let chunk ← forAll (Gen.frequency [
    (2, Gen.element [0, 1, 4, 5, 20, 21, 84, 85, 340, 341, 1364, 1365]),
    (1, Gen.nat (.exponential 0 (2 ^ 40)))])
  let level ← forAll (Gen.frequency [(2, pure 0), (1, Gen.nat (.constant 1 5))])
  let spine ← forAll (Gen.frequency [(2, pure 2), (1, Gen.nat (.exponential 1 (2 ^ 20)))])
  let outer ← forAll (Gen.nat (.exponential 1 (2 ^ 70)))
  let inner ← forAll (Gen.frequency [(1, pure 1), (4, Gen.nat (.exponential 1 (2 ^ 70)))])
  pure do
    classify "the first run, from the contents node" (level == 0 && spine == 2)
    classify "another run or another node" (level != 0 || spine != 2)
    classifyOne "the run of the chunk" (countClasses 6)
      (countClass 6 ((List.range 30).find? (fun k => chunk < (4 ^ (k + 1) - 1) / 3) |>.getD 30))
    toString (progressiveChunkGindex chunk (2 * level) spine) ===
      (← oracle.ask ["pgindex", toString chunk, toString (2 * level), toString spine])
    if level == 0 && spine == 2 then
      progressiveChunkGindex chunk === progressiveChunkGindex chunk 0 2
    -- The join of two indices: the bits of the first, then those of the second after its first.
    let bits (n : Nat) := Nat.toDigits 2 n
    (gindexConcat outer inner).toOption.map bits === some (bits outer ++ (bits inner).drop 1)
    ensure (gindexConcat 0 inner).toOption.isNone "an index of 0 was joined"
    ensure (gindexConcat outer 0).toOption.isNone "an index of 0 was joined"
    -- The path and the branch of an index.
    let text (result : Except Err (List Nat)) := (result.toOption.map toString).getD "none"
    if outer > 1 then
      s!"{text (getPathIndices outer)} {text (getBranchIndices outer)}" ===
        (← oracle.ask ["indices", toString outer])
    (gindexDepth outer).toOption === some ((bits outer).length - 1)
    (getSubtreeIndex outer).toOption === some (outer - 2 ^ ((bits outer).length - 1))
    gindexRebase outer level === 2 ^ level + outer % 2 ^ level

/-- An element sits in the chunk and at the bytes that the specification gives it.

A generalized index reads the chunk only; the bytes inside it are compared here.

The count of chunks of a type and the bytes of one element are the specification's too. -/
def chunkPositions (oracle : Oracle) : Property IO := propertyM do
  let packed : Gen Desc := do
    let element ← genBasic
    Gen.element [.vector element 70, .list element 70, .progressiveList element none]
  let shape ← forAllWith typeText (Gen.frequency [(3, genDesc), (2, genShallow), (1, packed)])
  let step ← forAll (Gen.frequency [
    (4, Gen.nat (.constant 0 4)),
    (3, Gen.element [5, 7, 8, 15, 16, 31, 32, 33, 63, 64, 255, 256, 257]),
    (1, Gen.nat (.linear 0 600))])
  pure do
    let placed := shape.chunkPosition (.position step)
    labelOutcome ["NOT_STEPPABLE", "NO_SUCH_FIELD", "NO_SUCH_POSITION"] placed
    classifyOne "of" constructors (constructorOf shape)
    classifyAny "the element" ["starts a chunk", "starts inside a chunk", "ends its chunk",
        "is a bit", "is in a chunk past the first"]
      (match placed with
        | .ok at' =>
          (if at'.stop == 0 then ["is a bit"] else if at'.start == 0 then ["starts a chunk"]
            else ["starts inside a chunk"]) ++
          (if at'.stop == 32 then ["ends its chunk"] else []) ++
          (if at'.chunk > 0 then ["is in a chunk past the first"] else [])
        | .error _ => [])
    classify "chunk count: none, a progressive shape" shape.chunkCount.toOption.isNone
    let position := match placed with
      | .ok at' => s!"{at'.chunk} {at'.start} {at'.stop}"
      | .error e => refusal e
    let count := match shape.chunkCount with
      | .ok chunks => toString chunks
      | .error e => refusal e
    s!"{position} | {count} | {shape.itemLength}" ===
      (← oracle.ask ["sszposition", typeText shape, toString step])

/-- A branch climbs to the root of the text under any hash, from any level, at any depth.

A branch by depth and index reads its first `depth` nodes, at depths up to 70. -/
def branchEveryHash (oracle : Oracle) : Property IO := propertyM do
  let depth ← forAll (Gen.frequency [(1, Gen.element [0, 1, 32, 63, 64, 65]),
    (2, Gen.nat (.linear 0 70))])
  let index ← forAll (Gen.frequency [(2, Gen.nat (.constant 0 (2 ^ depth - 1))),
    (1, genNatBits 80)])
  let extra ← forAll (Gen.frequency [(3, pure 0), (1, Gen.nat (.constant 1 3))])
  let level ← forAll (Gen.frequency [(2, pure 0), (1, Gen.nat (.constant 1 5))])
  let leaf ← forAllWith nodesText (genNodes 1)
  let branch ← forAllWith nodesText (genNodes (depth + extra))
  let name ← forAll (Gen.element ["sha256", "twice", "toy"])
  pure do
    classifyOne "hash" ["sha256", "twice", "toy"] name
    classifyOne "depth" ["0", "1 to 31", "32 to 63", "64 or more"]
      (if depth == 0 then "0" else if depth < 32 then "1 to 31" else if depth < 64 then "32 to 63"
        else "64 or more")
    classify "from a level above the leaves" (level > 0)
    classify "a branch longer than the depth" (extra > 0)
    classify "an index of 2 ^ depth or more" (index ≥ 2 ^ depth)
    let node := leaf.headD #[]
    -- From a level, the bits of the index above that level choose the sides.
    hex ⟨(climbBranchM (m := Id) (namedHash name) index level node branch).run⟩ ===
      (← oracle.ask ["branchx", name, nodesText leaf, nodesText branch,
        toString (index >>> level)])
    let expected ← oracle.ask ["branchx", "sha256", nodesText leaf,
      nodesText (branch.take depth), toString index]
    (computeMerkleBranchRoot (chunkOf node) (branch.map chunkOf) depth index).toOption.map
      (fun root => hex ⟨root.toArray⟩) === some expected
    ensure ((computeMerkleBranchRoot (chunkOf node) ((branch.take depth).dropLast.map chunkOf)
      depth index).toOption.isNone == decide (depth > 0)) "a branch shorter than its depth"
    -- By generalized index, the same branch behind zero nodes.
    let root := chunkOf ((unhex? expected).getD .empty).data
    if index < 2 ^ depth then
      let zeros := List.replicate (index % 3) (Vector.replicate 32 (0 : UInt8))
      (isValidNormalizedMerkleBranch (chunkOf node) (zeros ++ (branch.take depth).map chunkOf)
        (2 ^ depth + index) root).toOption === some true
      (calculateMerkleRoot node (branch.take depth) (2 ^ depth + index)).toOption.map
        (hex ⟨·⟩) === (if depth == 0 then none else some expected)

/-- A branch with nodes after its depth is valid, as `is_valid_merkle_branch` of phase0 says.

EthLib asks for exactly `depth` nodes, so this fails: it is kept as a finding. -/
def branchLongerThanDepth (oracle : Oracle) : Property IO := propertyM do
  let depth ← forAll (Gen.nat (.linear 0 8))
  let index ← forAll (Gen.nat (.constant 0 (2 ^ depth - 1)))
  let leaf ← forAllWith nodesText (genNodes 1)
  let branch ← forAllWith nodesText (genNodes (depth + 1))
  pure do
    let root ← oracle.ask ["branchroot", nodesText leaf, nodesText branch, toString depth,
      toString index]
    let expected ← oracle.ask ["branch", nodesText leaf, nodesText branch, toString depth,
      toString index, root]
    toString (isValidMerkleBranch (chunkOf (leaf.headD #[])) (branch.map chunkOf) depth index
      (chunkOf ((unhex? root).getD .empty).data)) === expected

end SerializationProperty

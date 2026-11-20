import Hedgehog
import Support
import EthLib.Serialization.Ssz
import EthLib.Serialization.Rlp

/-!
# Generators and text forms of the serialization layer

An SSZ type and a value of it are generated together, by a recursion on a depth.

Both are sent to the oracle as JSON, which is also how a counterexample is shown.
-/

open Hedgehog Support EthLib.Serialization

namespace SerializationProperty

/-- Bytes in lower-case hexadecimal, and nothing for none. -/
def hexOf (bytes : Array UInt8) : String :=
  if bytes.isEmpty then "" else hex ⟨bytes⟩

/-- A JSON array of the parts. -/
def jsonArray (parts : List String) : String := "[" ++ ",".intercalate parts ++ "]"

/-- A JSON string of a text that needs no escape. -/
def quoted (text : String) : String := "\"" ++ text ++ "\""

/-! ## RLP items -/

/-- An item as JSON: a string of hexadecimal, or an array of items. -/
partial def itemText : Rlp.Item → String
  | .bytes data => quoted (hexOf data.data)
  | .list items => jsonArray (items.map itemText)

/-- A long byte string of one byte repeated: cheap to generate, and its length is the point. -/
def genRun (lengths : List Nat) : Gen ByteArray :=
  Gen.zipWith (fun length byte => ⟨Array.replicate length byte⟩) (Gen.element lengths)
    (Gen.element [0, 1, 0x7f, 0x80, 0xff])

/-- A byte string that reaches each form of the prefix.

A length is in the first byte up to 55, on one byte up to 255, on two up to 65535, then on three. -/
def genRlpBytes : Gen ByteArray :=
  Gen.frequency [
    (6, genBytes (.linear 0 8)),
    (1, pure .empty),
    (4, genBytes (.singleton 1)),
    (4, (fun b => ⟨#[b]⟩) <$> Gen.element [0, 0x7f, 0x80, 0xff]),
    (4, genBytes (.constant 54 57)),
    (3, genBytes (.constant 254 258)),
    (2, genRun [259, 1000, 65535]),
    (3, genRun [65536, 65537, 70000])]

/-- An item of at most the depth. -/
def genItemOf : Nat → Gen Rlp.Item
  | 0 => Rlp.Item.bytes <$> genRlpBytes
  | depth + 1 => Gen.frequency [
      (3, Rlp.Item.bytes <$> genRlpBytes),
      (3, Rlp.Item.list <$> Gen.list (.linear 0 4) (genItemOf depth)),
      (1, Rlp.Item.list <$> Gen.list (.constant 1 2) (genItemOf depth)),
      (1, Rlp.Item.list <$>
        Gen.list (.constant 50 58) (Rlp.Item.bytes <$> genBytes (.singleton 0))),
      (1, Rlp.Item.list <$>
        Gen.list (.constant 250 260) (Rlp.Item.bytes <$> genBytes (.singleton 0)))]

/-- An item, deeper at a larger size: up to five lists inside one another. -/
def genItem : Gen Rlp.Item := Gen.sized fun size => genItemOf (min 5 (size.log2 + 1))

/-! ## SSZ types -/

open Ssz in
/-- An SSZ type as JSON, in the form `oracle/serialization.py` reads. -/
partial def typeText : Desc → String
  | .bool => "[\"bool\"]"
  | .uint width => s!"[\"uint\",{width}]"
  | .byteVector length => s!"[\"bvec\",{length}]"
  | .byteList limit => s!"[\"blist\",{limit}]"
  | .bitVector length => s!"[\"bitvec\",{length}]"
  | .bitList limit => s!"[\"bitlist\",{limit}]"
  | .progressiveBitList _ => "[\"pbitlist\"]"
  | .vector element length => s!"[\"vec\",{typeText element},{length}]"
  | .list element limit => s!"[\"list\",{typeText element},{limit}]"
  | .progressiveList element _ => s!"[\"plist\",{typeText element}]"
  | .container names fields =>
    s!"[\"cont\",{jsonArray (names.map quoted)},{jsonArray (fields.map typeText)}]"
  | .progressiveContainer active names fields =>
    let bits := jsonArray (active.map fun bit => if bit then "1" else "0")
    s!"[\"pcont\",{bits},{jsonArray (names.map quoted)},{jsonArray (fields.map typeText)}]"
  | .compatibleUnion selectors options =>
    s!"[\"union\",{jsonArray (selectors.map toString)},{jsonArray (options.map typeText)}]"

open Ssz in
/-- An SSZ value as JSON, in the form `oracle/serialization.py` reads. -/
partial def valueText : Value → String
  | .bool b => if b then "true" else "false"
  | .uint n => quoted (toString n)
  | .bytes data => quoted (hexOf data)
  | .bits data => jsonArray (data.toList.map fun bit => if bit then "1" else "0")
  | .seq elements => jsonArray (elements.map valueText)
  | .union selector data => "{\"s\":" ++ toString selector ++ ",\"d\":" ++ valueText data ++ "}"

/-- The bytes and the root of a value, as the oracle writes them. -/
def encodedText (shape : Ssz.Desc) (value : Ssz.Value) : String :=
  match Ssz.serialize shape value, Ssz.hashTreeRoot shape value with
  | .ok bytes, .ok root => s!"{hex ⟨bytes⟩} {hex ⟨root⟩}"
  | .error e, _ => s!"error serialize {repr e}"
  | _, .error e => s!"error root {repr e}"

/-- A refusal as the oracle writes one of the specification: `error` and the name of the fault. -/
def refusal (e : Ssz.Err) : String := "error " ++ e.reason

/-- The first two words of an answer: for a refusal, `error` and the name of the fault. -/
def faultOf (answer : String) : String := " ".intercalate ((answer.splitOn " ").take 2)

/-- One of the edges twice in three draws, else a number of the range. -/
def genEdge (edges : List Nat) (range : Range Nat) : Gen Nat :=
  Gen.frequency [(2, Gen.element edges), (1, Gen.nat range)]

/-- A limit far above any count: a power of two up to `2 ^ 70`, or one more.

The tree under it is zero subtrees beside a few nodes, deeper than the table of zero roots. -/
def genHugeLimit : Gen Nat :=
  Gen.zipWith (fun power near => 2 ^ power + near)
    (Gen.element [10, 20, 32, 40, 62, 63, 64, 65, 66, 69, 70, 72, 73, 80]) (Gen.element [0, 0, 1])

open Ssz in
/-- A basic type. -/
def genBasic : Gen Desc :=
  Gen.frequency [(1, pure .bool), (5, Desc.uint <$> Gen.element [8, 1, 2, 4, 16, 32])]

open Ssz in
/-- A type that holds no other type: basic, bytes or bits. -/
def genLeaf : Gen Desc :=
  Gen.frequency [
    (4, genBasic),
    (1, Desc.byteVector <$> genEdge [1, 31, 32, 33, 64, 65] (.linear 1 70)),
    (1, Desc.byteList <$> genEdge [0, 1, 31, 32, 33, 64, 65] (.linear 0 70)),
    (2, Desc.byteList <$> genHugeLimit),
    (2, Desc.bitVector <$> genEdge [1, 7, 8, 9, 255, 256, 257, 512, 513] (.linear 1 520)),
    (2, Desc.bitList <$> genEdge [0, 1, 7, 8, 9, 255, 256, 257, 513] (.linear 0 520)),
    (2, Desc.bitList <$> genHugeLimit),
    (2, pure (.progressiveBitList none))]

/-- The names of the fields of a container. -/
def fieldNames (count : Nat) : List String := (List.range count).map fun i => s!"f{i}"

/-- A layout of a progressive container with the count of fields, which ends on a field. -/
def genActive (count : Nat) : Gen (List Bool) := do
  let gaps ← Gen.list (.singleton count) (Gen.frequency [(3, pure 0),
    (1, Gen.nat (.constant 1 3)),
    (1, Gen.element [4, 15, 16])])
  pure (gaps.flatMap fun gap => List.replicate gap false ++ [true])

open Ssz in
/-- The same tree under another spelling: a byte array as a sequence of bytes, or back. -/
def variant : Desc → Desc
  | .byteVector length => .vector (.uint 1) length
  | .vector (.uint 1) length => .byteVector length
  | .byteList limit => .list (.uint 1) limit
  | .list (.uint 1) limit => .byteList limit
  | .progressiveBitList _ => .progressiveBitList none
  | shape => shape

open Ssz in
/-- A legal type of at most the depth. -/
def genDescOf : Nat → Gen Desc
  | 0 => genLeaf
  | depth + 1 =>
    let inner := genDescOf depth
    Gen.frequency [
      (3, genLeaf),
      (2, do
        let element ← inner
        let length ← if element.isBasic then genEdge [1, 31, 32, 33, 64, 65] (.linear 1 70)
          else genEdge [1, 2, 3, 4, 5] (.linear 1 6)
        pure (.vector element length)),
      (2, do
        let element ← inner
        let limit ← Gen.frequency [
          (3, if element.isBasic then genEdge [0, 1, 31, 32, 33, 64, 65] (.linear 0 70)
            else genEdge [0, 1, 2, 3, 4, 5, 8, 9] (.linear 0 9)),
          (2, genHugeLimit)]
        pure (.list element limit)),
      (2, (Desc.progressiveList · none) <$> inner),
      (2, do
        let fields ← Gen.list (.linear 1 5) inner
        pure (.container (fieldNames fields.length) fields)),
      (2, do
        let fields ← Gen.list (.linear 1 5) inner
        let active ← genActive fields.length
        pure (.progressiveContainer active (fieldNames fields.length) fields)),
      (1, do
        let option ← inner
        let selectors ← Gen.element [[1], [127], [1, 2], [127, 1], [3, 64, 126], [2, 1, 127]]
        let options := selectors.zipIdx.map fun (_,
            i) => if i % 2 == 1 then variant option else option
        pure (.compatibleUnion selectors options))]

/-- A legal type, deeper at a larger size. -/
def genDesc : Gen Ssz.Desc := Gen.sized fun size => genDescOf (min 3 (size.log2 / 2 + 1))

instance : Inhabited (Gen Ssz.Value) := ⟨pure default⟩

open Ssz in
/-- A count of elements of a progressive shape: at the ends of the runs of 1, 4 and 16 nodes. -/
def genSpineCount (perNode : Nat) (wide : Bool) : Gen Nat :=
  if wide then do
    -- The runs hold 1, 4, 16, 64 and 256 nodes: 85 nodes fill four runs, and 341 fill five.
    let nodes ← Gen.frequency [(4, Gen.element [0, 1, 2, 5, 6, 21, 22]),
      (2, Gen.element [85, 86]), (if perNode ≤ 4 then 1 else 0, Gen.element [341, 342])]
    let off ← Gen.element [0, 0, 1, perNode - 1]
    Gen.frequency [(3, pure (nodes * perNode + off)), (1, Gen.nat (.linear 0 (30 * perNode)))]
  else Gen.frequency [(1, Gen.element [0, 1, 2, 5, 6]), (1, Gen.nat (.linear 0 7))]

/-- A count up to a limit: none, all, or some; a few under a limit far above any count. -/
def genCount (limit : Nat) : Gen Nat :=
  if limit > 600 then Gen.frequency [(1, pure 0), (1, pure 1), (2, Gen.nat (.linear 0 40))]
  else Gen.frequency [(1, pure 0), (1, pure limit), (1, pure (limit - 1)), (2,
      Gen.nat (.linear 0 limit))]

/-- A count of bits up to a limit: at the edges of a byte and of a node, where they fit. -/
def genBitCount (limit : Nat) : Gen Nat :=
  Gen.frequency [
    (3, Gen.element ([0, 1, 7, 8, 9, 255, 256, 257].filter (· ≤ limit))),
    (1, genCount limit)]

open Ssz in
/-- A value that fits the type; `wide` allows the long progressive values at the top only. -/
partial def genValueOf (wide : Bool) : Desc → Gen Value
  | .bool => .bool <$> Gen.bool
  | .uint width => .uint <$> genNatBits (8 * width)
  | .byteVector length => (fun b => .bytes b.data) <$> genBytesN length
  | .byteList limit =>
    -- Under a great limit, now and then more bytes than an offset of two bytes can pass.
    Gen.frequency [
      (12, do
        let count ← genCount limit
        (fun b => .bytes b.data) <$> genBytesN count),
      (if limit ≥ 70000 then 1 else 0, (fun b => .bytes b.data) <$> genRun [65536, 70000])]
  | .bitVector length => .bits <$> Gen.array (.singleton length) Gen.bool
  | .bitList limit => do
    let count ← genBitCount limit
    .bits <$> Gen.array (.singleton count) Gen.bool
  | .progressiveBitList _ => do
    let count ← Gen.frequency [(1, genSpineCount 256 wide), (1, genBitCount 300)]
    .bits <$> Gen.array (.singleton count) Gen.bool
  | .vector element length => .seq <$> Gen.list (.singleton length) (genValueOf false element)
  | .list element limit => do
    let count ← genCount limit
    .seq <$> Gen.list (.singleton count) (genValueOf false element)
  | .progressiveList element _ => do
    let count ← genSpineCount (if element.isBasic then 32 / element.itemLength else 1) wide
    .seq <$> Gen.list (.singleton count) (genValueOf false element)
  -- A struct keeps a value for each field when it shrinks: with one fewer it is no value of it.
  | .container _ fields | .progressiveContainer _ _ fields =>
    .seq <$> Gen.sequence (fields.map (genValueOf false)) (atLeast := fields.length)
  | .compatibleUnion selectors options => do
    let slot ← Gen.nat (.constant 0 (options.length - 1))
    .union (selectors.getD slot 0) <$> genValueOf wide (options.getD slot .bool)

/-- A type and a value of it. -/
def genTyped : Gen (Ssz.Desc × Ssz.Value) := do
  let shape ← genDesc
  let value ← genValueOf true shape
  pure (shape, value)

/-- A type and a value of it, as the oracle reads them. -/
def typedText (typed : Ssz.Desc × Ssz.Value) : String :=
  typeText typed.1 ++ " " ++ valueText typed.2

/-- Bytes changed a little: a byte, a length, an offset, the end. -/
def genMutation (bytes : ByteArray) : Gen ByteArray :=
  let size := bytes.size
  Gen.frequency [
    (2, pure bytes),
    (3, do
      let spot ← Gen.nat (.constant 0 (size - 1))
      let byte ← Gen.frequency [(2, Gen.element [0, 1, 2, 0x80, 0xff]), (1, genByte)]
      pure (if h : spot < size then bytes.set spot byte h else bytes)),
    (3, do
      -- An offset is four bytes: move one by a little.
      let spot ← Gen.nat (.constant 0 (size - 1))
      let delta ← Gen.element [1, 2, 4, 255]
      pure (if h : spot < size then bytes.set spot (bytes[spot] + delta) h else bytes)),
    (2, do
      let keep ← Gen.nat (.constant 0 size)
      pure (bytes.extract 0 keep)),
    (2, do
      let tail ← genBytes (.linear 1 5)
      pure (bytes ++ tail)),
    (1, do
      let spot ← Gen.nat (.constant 0 size)
      let byte ← Gen.element [0, 1, 4, 0xff]
      pure (bytes.extract 0 spot ++ ⟨#[byte]⟩ ++ bytes.extract spot size)),
    (1, do
      let spot ← Gen.nat (.constant 0 (size - 1))
      pure (bytes.extract 0 spot ++ bytes.extract (spot + 1) size))]

end SerializationProperty

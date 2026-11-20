import Hedgehog
import Support
import Property.Serialization.Common

/-!
# Bytes near a valid SSZ encoding, by the rule of the type that they break

A random change of a byte reaches the common refusals, and almost never the rare ones.

Here a fault is made for the type:

- A boolean of 2, and a padding bit of a bit vector.
- A bitlist without its delimiter, or with a zero byte after it.
- A selector the union lacks, and a union of no byte.
- A first offset inside its table, off a multiple of four, or past the end.
- An element more than the limit.

The fault is put at the root or inside a part, at any depth, and the parts around it are kept.

The parts are cut from a valid encoding and joined again by the two functions below.

They are written here from the specification, apart from the encoder under test.
-/

open Hedgehog Support EthLib.Serialization

namespace SerializationProperty

/-- A number on four bytes, least significant first: an offset. -/
def offsetBytes (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat n, UInt8.ofNat (n / 256), UInt8.ofNat (n / 65536), UInt8.ofNat (n / 16777216)]⟩

/-- The offset on the four bytes at a position. -/
def readOffset (data : ByteArray) (pos : Nat) : Nat :=
  (List.range 4).foldl (fun total i => total + (data.data.getD (pos + i) 0).toNat * 256 ^ i) 0

open Ssz in
/-- The parts of a valid encoding of a struct or of a sequence: one run of bytes for each type. -/
def splitParts (kinds : List Desc) (data : ByteArray) : List ByteArray := Id.run do
  let mut pos := 0
  let mut slots : Array (Option ByteArray × Nat) := #[]
  for kind in kinds do
    match kind.fixedSize with
    | some width =>
      slots := slots.push (some (data.extract pos (pos + width)), 0)
      pos := pos + width
    | none =>
      slots := slots.push (none, readOffset data pos)
      pos := pos + 4
  let ends := (slots.toList.filterMap fun (fixed, offset) =>
    if fixed.isNone then some offset else none).drop 1 ++ [data.size]
  let mut out : Array ByteArray := #[]
  let mut body := 0
  for (fixed, offset) in slots do
    match fixed with
    | some bytes => out := out.push bytes
    | none =>
      out := out.push (data.extract offset (ends.getD body data.size))
      body := body + 1
  return out.toList

open Ssz in
/-- The encoding of parts: the fixed ones and the offsets in order, then the other parts. -/
def joinParts (kinds : List Desc) (parts : List ByteArray) : ByteArray := Id.run do
  let pairs := kinds.zip parts
  let head := pairs.foldl (fun width (kind, part) =>
    width + (if kind.isFixed then part.size else 4)) 0
  let mut front := ByteArray.empty
  let mut back := ByteArray.empty
  for (kind, part) in pairs do
    if kind.isFixed then front := front ++ part
    else
      front := front ++ offsetBytes (head + back.size)
      back := back ++ part
  return front ++ back

open Ssz in
/-- The types of the parts of a valid encoding, for a type that has parts. -/
def partKinds (shape : Desc) (data : ByteArray) : List Desc :=
  let elements (element : Desc) : List Desc :=
    match element.fixedSize with
    | some width => List.replicate (if width == 0 then 0 else data.size / width) element
    | none => List.replicate (if data.size < 4 then 0 else readOffset data 0 / 4) element
  match shape with
  | .vector element _ | .list element _ | .progressiveList element _ => elements element
  | .container _ fields | .progressiveContainer _ _ fields => fields
  | _ => []

open Ssz in
/-- Where the offsets of the parts of variable size stand in the fixed part. -/
def offsetSpots (kinds : List Desc) : List Nat :=
  (kinds.foldl (fun (state : Nat × List Nat) kind =>
    match kind.fixedSize with
    | some width => (state.1 + width, state.2)
    | none => (state.1 + 4, state.2 ++ [state.1])) (0, [])).2

/-- The bytes with the offset at a spot replaced. -/
def withOffset (data : ByteArray) (spot offset : Nat) : ByteArray :=
  data.extract 0 spot ++ offsetBytes offset ++ data.extract (spot + 4) data.size

open Ssz in
/-- Bytes that break a rule of offsets of a struct or of a sequence, near a valid encoding. -/
def genBadOffsets (shape : Desc) (valid : ByteArray) : Gen ByteArray :=
  let size := valid.size
  let kinds := partKinds shape valid
  let spots := offsetSpots kinds
  let isList := match shape with
    | .list _ _ | .progressiveList _ _ => true
    | _ => false
  match spots with
  | [] =>
    -- A list of variable elements that holds none: a table that names no element.
    if isList && size == 0 then
      Gen.element [⟨#[0, 0, 0]⟩, offsetBytes 0, offsetBytes 3, offsetBytes 5, offsetBytes 8]
    else Gen.element [valid.push 0, valid.extract 0 (size - 1)]
  | first :: rest => do
    let start := readOffset valid first
    let later ← Gen.element (first :: rest)
    Gen.frequency [
      -- The first offset: inside the table, off a multiple of four, one element on, past the end.
      (4, withOffset valid first <$> Gen.element [0, 1, 2, 3, start + 1, start + 2, start - 1,
        start + 4, start - 4, size + 1, size + 4]),
      -- A later offset: before the one in front of it, or past the end.
      (4, withOffset valid later <$> Gen.element [start - 1, start - 4, 0, size + 1, size + 4,
        readOffset valid later + 1]),
      -- Cut inside the fixed part, or just after it.
      (1, pure (valid.extract 0 (first + 3))),
      (1, pure (valid.extract 0 (first + 4))),
      (1, pure (valid.extract 0 (size - 1)))]

open Ssz in
/-- Bytes near a valid encoding of a type, which break a rule of that type itself. -/
def genTargeted (shape : Desc) (valid : ByteArray) : Gen ByteArray :=
  let size := valid.size
  let resized : Gen ByteArray := Gen.element [valid.push 0, valid.extract 0 (size - 1)]
  let last := valid.data.getD (size - 1) 0
  match shape with
  | .bool => (fun byte => ⟨#[byte]⟩) <$> Gen.element [2, 3, 0x80, 0xff]
  | .uint _ | .byteVector _ => resized
  | .bitVector length =>
    if length % 8 == 0 then resized
    else Gen.frequency [(1, resized),
      -- A bit above the last one of the type.
      (3, (fun bit => valid.set! (size - 1) (last ||| (1 <<< UInt8.ofNat bit))) <$>
        Gen.nat (.constant (length % 8) 7))]
  | .bitList _ | .progressiveBitList _ =>
    let limit := match shape with
      | .bitList limit => some limit
      | .progressiveBitList limit => limit
      | _ => none
    let over := match limit with
      | some limit =>
        if limit ≤ 600 then
          [(ByteArray.mk (Array.replicate ((limit + 1) / 8) 0)).push
            (1 <<< UInt8.ofNat ((limit + 1) % 8))]
        else []
      | none => []
    Gen.element ([valid.push 0, valid.push 0, valid.push 0 |>.push 0,
      ⟨Array.replicate (max size 1) 0⟩, ⟨#[0]⟩, .empty, .empty, valid.set! (size - 1) 0] ++
      over ++ over)
  | .byteList limit =>
    if limit ≤ 600 then pure (valid ++ ⟨Array.replicate (limit + 1 - size) 0⟩)
    else pure valid
  | .compatibleUnion selectors _ => do
    let other ← Gen.element (([0, 1, 2, 3, 126, 127, 128, 255] : List Nat).filter
      (!selectors.contains ·))
    Gen.element [.empty, .empty, valid.set! 0 (UInt8.ofNat other), ⟨#[UInt8.ofNat other]⟩]
  | .list element limit =>
    match element.fixedSize with
    | some width =>
      -- A byte more than whole elements, or an element more than the limit.
      Gen.element ((if width > 1 then [valid.push 0, valid.extract 0 (size - 1)] else []) ++
        (if limit ≤ 600 then
          [valid ++ ⟨Array.replicate (width * (limit + 1) - size) 0⟩,
            valid ++ ⟨Array.replicate (width * (limit + 1) - size) 0⟩]
        else [valid]))
    | none => genBadOffsets shape valid
  | .progressiveList element _ =>
    match element.fixedSize with
    | some width => if width > 1 then resized else pure valid
    | none => genBadOffsets shape valid
  | .vector _ _ | .container _ _ | .progressiveContainer _ _ _ => genBadOffsets shape valid

open Ssz in
/-- A fault at the root of a value or inside one of its parts, down to a depth. -/
partial def genDeep (depth : Nat) (shape : Desc) (valid : ByteArray) : Gen ByteArray :=
  let here := genTargeted shape valid
  match depth, shape with
  | 0, _ => here
  | depth + 1, .compatibleUnion selectors options =>
    match (selectors.zip options).lookup (valid.data.getD 0 0).toNat with
    | some option => Gen.frequency [(2, here),
        (3, (valid.extract 0 1 ++ ·) <$> genDeep depth option (valid.extract 1 valid.size))]
    | none => here
  | depth + 1, _ =>
    let kinds := partKinds shape valid
    let parts := splitParts kinds valid
    if parts.isEmpty then here
    else Gen.frequency [(1, here), (3, do
      -- A part whose type has a fault of its own is taken first now and then: it is rare.
      let flags := kinds.zipIdx.filterMap fun (kind, at') =>
        match kind with
        | .bool | .bitVector _ | .bitList _ | .progressiveBitList _ | .compatibleUnion _ _ =>
          some at'
        | _ => none
      let slot ← Gen.frequency [(if flags.isEmpty then 0 else 1, Gen.element flags),
        (1, Gen.nat (.constant 0 (parts.length - 1)))]
      let bad ← genDeep depth (kinds.getD slot .bool) (parts.getD slot .empty)
      pure (joinParts kinds (parts.set slot bad)))]

/-- Bytes near a valid encoding: changed at random, or with a fault made for the type. -/
def genNearEncoding (shape : Ssz.Desc) (valid : ByteArray) : Gen ByteArray :=
  Gen.frequency [(2, genMutation valid), (5, genDeep 4 shape valid)]

open Ssz in
/-- The reasons for which the decoder can refuse the bytes of a list, before it reads an element. -/
def listReasons (element : Desc) : List String :=
  match element.fixedSize with
  | some width => if width > 1 then ["SCOPE_UNDIVIDED"] else []
  | none => ["SCOPE_TOO_SMALL", "OFFSET_BELOW_TABLE", "OFFSET_UNALIGNED", "OFFSET_PAST_SCOPE",
      "OFFSET_UNORDERED"]

open Ssz in
/-- The reasons for which the decoder can refuse bytes of the right count for a type.

A part of fixed size inside a struct or a sequence is cut to its size, so `SCOPE` is not one. -/
partial def reachableReasons : Desc → List String
  | .bool => ["NOT_A_BIT"]
  | .uint _ | .byteVector _ => []
  | .byteList _ => ["LIMIT"]
  | .bitVector length => if length % 8 == 0 then [] else ["PADDING_BITS"]
  | .bitList _ => ["EMPTY_ENCODING", "NO_DELIMITER", "TRAILING_ZEROS", "LIMIT"]
  | .progressiveBitList limit =>
    ["EMPTY_ENCODING", "NO_DELIMITER", "TRAILING_ZEROS"] ++ (if limit.isSome then ["LIMIT"] else [])
  | .vector element length =>
    (if element.isFixed then []
      else ["SCOPE_TOO_SMALL", "FIRST_OFFSET"] ++
        (if length > 1 then ["OFFSET_PAST_SCOPE", "OFFSET_UNORDERED"] else [])) ++
      reachableReasons element
  | .list element _ => listReasons element ++ ["LIMIT"] ++ reachableReasons element
  | .progressiveList element limit =>
    listReasons element ++ (if limit.isSome then ["LIMIT"] else []) ++ reachableReasons element
  | .container _ fields | .progressiveContainer _ _ fields =>
    let loose := (fields.filter (!·.isFixed)).length
    (if loose == 0 then []
      else ["SCOPE_TOO_SMALL", "FIRST_OFFSET"] ++
        (if loose > 1 then ["OFFSET_PAST_SCOPE", "OFFSET_UNORDERED"] else [])) ++
      fields.flatMap reachableReasons
  -- The option of a union takes the bytes that are left, whatever their count.
  | .compatibleUnion _ options =>
    ["NO_SELECTOR", "UNKNOWN_SELECTOR"] ++ options.flatMap fun option =>
      (if option.isFixed then ["SCOPE"] else []) ++ reachableReasons option

/-- The reasons for which the decoder can refuse bytes of any count for a type.

A type of fixed size is refused for `SCOPE` on another count of bytes. -/
def rootReasons (shape : Ssz.Desc) : List String :=
  (if shape.isFixed then ["SCOPE"] else []) ++ reachableReasons shape

end SerializationProperty

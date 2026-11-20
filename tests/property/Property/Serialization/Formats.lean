import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Classes
import Property.Serialization.Misc
import Property.Serialization.Streams
import EthLib.Serialization.Der
import EthLib.Serialization.E2store
import EthLib.Serialization.JsonRpc

/-!
# DER, e2store and JSON-RPC at every tag, record type and width

- DER: a value of each of the 256 tags, with its length on up to 126 octets.
- E2store: a header of every type and of a length on each of its four bytes.
- JSON-RPC: a fixed byte string of every length, a quantity below every power of two.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Serialization

namespace SerializationProperty

/-! ## DER -/

/-- One value of any tag, with its length in any form, on up to 126 octets. -/
def genDerInput : Gen ByteArray := do
  let tag : UInt8 ← Gen.frequency [(3, genByte),
    (1, Gen.element [0, 1, 0x1e, 0x1f, 0x20, 0x3f, 0x5f, 0x7f, 0x80, 0x9f, 0xbf, 0xdf, 0xff])]
  let size ← genEdge [0, 1, 127, 128, 129, 255, 256, 257] (.linear 0 300)
  let content ← genBytesN size
  let digits := if size == 0 then [0] else bigEndianDigits size []
  let count ← Gen.frequency [(1, Gen.element [1, 2, 3, 4, 8, 125, 126]),
    (1, Gen.nat (.constant 1 126))]
  let junk ← genByteList (.singleton count)
  let top : UInt8 ← Gen.integral (.constant 1 255)
  let cut ← Gen.nat (.constant 0 count)
  let octets ← Gen.frequency [
    (5, pure (lengthOctets .shortest size)),
    (2, pure (lengthOctets .long size)),
    -- The long form on a count of octets, zero octets in front.
    (2, pure (UInt8.ofNat (128 + max count digits.length) ::
      List.replicate (count - digits.length) 0 ++ digits)),
    -- A length of any octets, which no input holds: with a first octet that is not zero.
    (2, pure (UInt8.ofNat (128 + count) :: top :: junk.drop 1)),
    (1, pure (UInt8.ofNat (128 + count) :: junk)),
    (1, pure (UInt8.ofNat (128 + count) :: junk.take cut)),
    (1, pure [128]),
    (1, pure [255])]
  let tail ← genByteList (.linear 0 3)
  Gen.frequency [(8, pure (⟨(tag :: octets).toArray⟩ ++ content ++ ⟨tail.toArray⟩)),
    (1, pure ⟨#[tag]⟩), (1, pure .empty)]

/-- One value of every tag reads as X.690 writes it, and a refusal says what the input lacks.

The length is on up to 126 octets, the most that the long form has. -/
def derEveryTag (oracle : Oracle) : Property IO := propertyM do
  let input ← forAllWith hex genDerInput
  let other ← forAll genByte
  pure do
    let got := Der.read input
    classifyOne "verdict" (derVerdicts.take 4) (derVerdict got)
    classifyOne "length" (lengthForms.dropLast ++ ["long on 3 to 8 octets",
        "long on 9 to 124 octets", "long on 125 or 126 octets"])
      (match input.data[1]? with
        | some first =>
          if 131 ≤ first.toNat && first.toNat ≤ 136 then "long on 3 to 8 octets"
          else if 137 ≤ first.toNat && first.toNat ≤ 252 then "long on 9 to 124 octets"
          else if first.toNat == 253 || first.toNat == 254 then "long on 125 or 126 octets"
          else lengthForm input
        | none => lengthForm input)
    classifyOne "tag" tagClasses (tagClass input)
    let expected ← oracle.ask ["dertlvx", hex input]
    match got with
    | .ok (value, rest) =>
      s!"{value.tag} {hex value.content} {hex rest}" === expected
      hex (value.encoded ++ rest) === hex input
      -- A reader that asks for a tag takes that tag only, and `exact` takes no byte after.
      let wanted := if other.toNat % 2 == 0 then value.tag else other
      classify "a tag is asked for: the one of the value" (wanted == value.tag)
      classify "a tag is asked for: another" (wanted != value.tag)
      (Der.readTag wanted input).toOption.isSome === (wanted == value.tag)
      (Der.exact wanted input).toOption.isSome === (wanted == value.tag && rest.isEmpty)
      if wanted != value.tag then
        match Der.readTag wanted input with
        | .error (.tag (some asked) actual) => (asked, actual) === (wanted, value.tag)
        | _ => failWith "another error than the tag"
    | .error (.truncated needed available) => s!"truncated {needed} {available}" === expected
    | .error (.tag none _) => expected === "tag"
    | .error (.length _) => expected === "length"
    | .error e => failWith s!"another error: {repr e}"

/-- A value of every tag is valid exactly when the model of X.690 says so.

The tags that validation does not read are refused as tags, each of them.

A string of code points on a fixed count of octets is valid for every count. -/
def derValidateEveryTag (oracle : Oracle) : Property IO := propertyM do
  let tag ← forAll (Gen.frequency [(2, genByte), (2, UInt8.ofNat <$> Gen.nat (.constant 1 62)),
    (5, Gen.element [1, 2, 3, 4, 5, 6, 12, 19, 22, 28, 30, 48, 49]),
    (1, Gen.element [0, 31, 63, 0x7f, 0xbf, 0xff])])
  let content ← forAllWith hex (Gen.frequency [(3, genContent tag), (1, genBytes (.linear 0 6)),
    (2, genBadContent tag)])
  let width ← forAll (Gen.nat (.constant 1 5))
  let units ← forAllWith hex (Gen.frequency [(3, genContent (if width == 2 then 30 else 28)),
    (1, genBytes (.linear 0 12))])
  pure do
    let input := tlv .shortest tag content
    let known := validatedTags.contains (toString tag)
    classify "a tag that validation reads" known
    classify "another tag" (!known)
    let expected ← oracle.ask ["dervalid", hex input]
    match Der.read input with
    | .ok (value, _) =>
      let verdict := Der.validate value
      classify "valid" verdict.toOption.isSome
      classify "not valid, of a tag that validation reads" (known && verdict.toOption.isNone)
      (if verdict.toOption.isSome then "ok" else "error") === expected
      if !known then
        ensure (derVerdict verdict == "tag") "a tag outside the subset has another error"
      -- The octet-aligned reader of a bit string: no unused bit, and the octets after.
      (Der.bitString value).toOption.map hex ===
        (if tag == 3 && content.data[0]? == some 0 then some (hex (content.extract 1 content.size))
          else none)
    | .error _ =>
      label "the tag has no value: 0 or a high tag number"
      expected === "error"
    classifyOne "code points on" ["1 octet", "2 octets", "3 octets", "4 octets", "5 octets"]
      (if width == 1 then "1 octet" else s!"{width} octets")
    let valid := Der.fixedString width units.data.toList
    classify "code points: valid" valid
    classify "code points: not valid" (!valid)
    (if valid then "ok" else "error") ===
      (← oracle.ask ["derstring", toString width, hex units])

/-! ## E2store -/

/-- A header of every type and length is the one of the format, and reads back at any offset.

A record whose data is not there is refused with the length that its four bytes write. -/
def e2sHeaders (oracle : Oracle) : Property IO := propertyM do
  let type ← forAll (Gen.frequency [
    (1, Gen.element [0, 0x6532, 0x3265, 0xffff, 0x00ff, 0xff00, 0x0100, 0x0001]),
    (1, Gen.nat (.constant 0 65535))])
  let length ← forAll (Gen.frequency [
    (2, Gen.element [0, 1, 255, 256, 65535, 65536, 2 ^ 24 - 1, 2 ^ 24, 2 ^ 31, 2 ^ 32 - 1]),
    (1, Gen.nat (.exponential 0 (2 ^ 32 - 1)))])
  let front ← forAllWith hex (genBytes (.linear 0 9))
  let data ← forAllWith hex (genBytes (.linear 0 12))
  let reserved ← forAll (Gen.frequency [(4, pure (0, 0)),
    (1, (fun b => (b, 0)) <$> Gen.element [1, 0x80, 0xff]),
    (1, (fun b => (0, b)) <$> Gen.element [1, 0x80, 0xff])])
  pure do
    classifyOne "length written on" ["no byte", "1 byte", "2 bytes", "3 bytes", "4 bytes"]
      (if length == 0 then "no byte" else if length < 256 then "1 byte"
        else s!"{byteLength length} bytes")
    classify "type: a second byte of 0x80 or more" (type % 256 ≥ 128)
    classify "type: a first byte of 0x80 or more" (type / 256 ≥ 128)
    classify "reserved: zero" (reserved == (0, 0))
    classify "reserved: not zero" (reserved != (0, 0))
    classify "from an offset past the start" (front.size > 0)
    let kind := UInt16.ofNat type
    let header := E2store.encodeHeader kind length
    hex header === (← oracle.ask ["e2shead", toString type, toString length])
    let header := (header.set! 6 reserved.1).set! 7 reserved.2
    let expected : Except E2store.E2storeError E2store.Header :=
      if reserved == (0, 0) then .ok ⟨kind, length⟩
      else .error (.reservedNotZero reserved.1 reserved.2)
    E2store.readHeader (front ++ header ++ data) front.size === expected
    E2store.readHeader (front ++ header.extract 0 7) front.size ===
      .error (.truncatedHeader front.size (front.size + 7))
    -- The records from an offset: the data is there, or the refusal names the length read.
    let read := E2store.decodeFrom (front ++ header ++ data) front.size #[]
    classifyOne "the record" ["read", "reserved not zero", "truncated data"] (fileVerdict read)
    if reserved != (0, 0) then
      read.map (fun _ => ()) === .error (.reservedNotZero reserved.1 reserved.2)
    else if length == data.size then
      decodedText read === recordsText [(kind, data)]
    else if length > data.size then
      read.map (fun _ => ()) ===
        .error (.truncatedData front.size length (front.size + 8 + data.size))
    -- The starts of records, from a position.
    E2store.recordStarts front.size [⟨kind, data⟩, ⟨kind, front⟩, ⟨kind, data⟩] ===
      [front.size, front.size + 8 + data.size, front.size + 16 + data.size + front.size]

/-- The data of an index record reads as the format writes it, or is refused. -/
def e2sIndex (oracle : Oracle) : Property IO := propertyM do
  let start ← forAll (genNatBits 64)
  let offsets ← forAll (Gen.list (.linear 0 5) (Gen.frequency [
    (2, Gen.int (.linearFrom 0 (-1000) 1000)),
    (1, Gen.element [-(2 : Int) ^ 63, 2 ^ 63 - 1, -1, 0, 2 ^ 32, -(2 : Int) ^ 32])]))
  let count ← forAll (Gen.frequency [(6, pure (offsets.length : Int)),
    (1, pure (offsets.length + 1)), (1, pure (offsets.length - 1)),
    (1, Gen.element [(2 : Int) ^ 63, 2 ^ 32 + offsets.length, 256 + offsets.length])])
  let valid : ByteArray := ⟨(int64Bytes start ++ offsets.flatMap int64Bytes ++
    int64Bytes count).toArray⟩
  let data ← forAllWith hex (Gen.frequency [(4, pure valid), (1, genMutation valid),
    (1, genBytes (.constant 0 17))])
  pure do
    let got := E2store.readIndex data
    classify "verdict: read" got.toOption.isSome
    classify "verdict: refused" got.toOption.isNone
    classifyAny "entries" (countClasses 3) (got.toOption.toList.map (countClass 3 ·.offsets.length))
    classify "an entry below zero" (got.toOption.any (·.offsets.any (· < 0)))
    classify "refused: fewer than 16 bytes" (data.size < 16)
    classify "refused: 16 bytes or more" (got.toOption.isNone && data.size ≥ 16)
    let expected ← oracle.ask ["e2sindex", hex data]
    match got with
    | .ok index =>
      " ".intercalate (toString index.start :: index.offsets.map toString) === expected
    | .error e =>
      expected === "error"
      ensure (e == .indexSize data.size) s!"another error: {repr e}"

/-! ## JSON-RPC -/

/-- A hexadecimal text of about a count of bytes, in either case, now and then not one. -/
def genHexOf (bytes : Nat) : Gen String := do
  let marker ← Gen.frequency [(12, pure "0x"), (1, Gen.element ["0X", "", "x", "00x"])]
  let count ← Gen.frequency [(5, pure (2 * bytes)), (1, pure (2 * bytes + 1)),
    (1, pure (2 * bytes - 1)), (2, pure (2 * bytes + 2)), (1, pure (2 * bytes - 2)),
    (1, Gen.nat (.linear 0 20))]
  let upper ← Gen.frequency [(2, pure 0), (1, pure 1), (1, pure 6)]
  let digit := Gen.frequency [
    (40 - 6 * upper, Gen.element "0123456789abcdef".toList),
    (1 + 6 * upper, Gen.element "ABCDEF".toList),
    (1, Gen.element "gGxX -+@`/:".toList)]
  let digits ← Gen.list (.singleton count) digit
  pure (marker ++ String.ofList digits)

/-- A fixed byte string of every length reads as the pattern of the schema at that length.

So does a byte string of at most a length, and a quantity below every power of two. -/
def rpcWidths (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll (genEdge [0, 1, 8, 20, 32, 48, 96] (.linear 0 40))
  let upper ← forAll Gen.bool
  let text ← forAll (genHexOf n)
  let bits ← forAll (genEdge [0, 1, 4, 8, 64, 256] (.linear 0 300))
  let near ← forAll (Gen.int (.linearFrom 0 (-2) 2))
  let value ← forAll (Gen.frequency [(3, pure ((2 : Int) ^ bits + near).toNat),
    (1, genNatBits (bits + 4))])
  let lead ← forAll (Gen.frequency [(8, pure ""), (1, pure "0")])
  pure do
    let json := Lean.Json.str text
    let fixed := JsonRpc.fixed "x" n json upper
    classify "fixed: read" fixed.toOption.isSome
    classify "fixed: read with an upper-case digit" (fixed.toOption.isSome && text.toLower != text)
    classify "fixed: an upper-case digit, refused where the pattern has none"
      (!upper && fixed.toOption.isNone && (JsonRpc.fixed "x" n json true).toOption.isSome)
    classify "fixed: of no byte" (n == 0)
    classify "fixed: the reader takes upper case" upper
    readText fixed (fun v => hex ⟨v.toArray⟩) ===
      (← oracle.ask ["rpcfixed", toString n, if upper then "1" else "0", hex text.toUTF8])
    let most := JsonRpc.bytesMax "x" n json
    classify "at most: read" most.toOption.isSome
    classify "at most: refused, and bytes"
      (most.toOption.isNone && (JsonRpc.bytes "x" json).toOption.isSome)
    readText most hex === (← oracle.ask ["rpcmax", toString n, hex text.toUTF8])
    let digits := "0x" ++ lead ++ String.ofList (Nat.toDigits 16 value)
    let quantity := JsonRpc.quantity "x" bits (.str digits)
    classify "quantity: read" quantity.toOption.isSome
    classify "quantity: 2 ^ bits or more" (value ≥ 2 ^ bits)
    classify "quantity: exactly 2 ^ bits - 1" (value + 1 == 2 ^ bits)
    classify "quantity: a leading zero" (lead == "0")
    readText quantity toString ===
      (← oracle.ask ["rpcquantity", toString bits, hex digits.toUTF8])

/-- The readers of the structure of a request: arrays, null, the members of an object. -/
def rpcStructure (oracle : Oracle) : Property IO := propertyM do
  let numbers ← forAll (Gen.list (.linear 0 4) (Gen.nat (.linear 0 300)))
  let shape ← forAll (Gen.element ["array", "null", "object", "string", "true", "number"])
  let names ← forAll (Gen.subsequence ["a", "b", "c", "d"])
  let nulls ← forAll (Gen.subsequence ["a", "b", "c", "d"])
  let wanted ← forAll (Gen.frequency [(2, Gen.subsequence ["a", "b", "c", "d"]),
    (1, pure (names.filter (!nulls.contains ·)))])
  let mantissa ← forAll (Gen.frequency [(1, Gen.int (.linearFrom 0 (-5000) 5000)),
    (1, (fun (n : Int) => n * 1000) <$> Gen.int (.linearFrom 0 (-50) 50)),
    (1, pure 0)])
  let exponent ← forAll (Gen.nat (.linear 0 6))
  pure do
    let quantities := numbers.map JsonRpc.quantityJson
    let object := Lean.Json.mkObj (names.map fun name =>
      (name, if nulls.contains name then .null else .str name))
    let json : Lean.Json := match shape with
      | "array" => .arr quantities.toArray
      | "null" => .null
      | "object" => object
      | "string" => .str "0x1"
      | "true" => .bool true
      | _ => .num 1
    classifyOne "value" ["array", "null", "object", "string", "true", "number"] shape
    let below (n : Nat) := decide (n < 256)
    (JsonRpc.array "x" (JsonRpc.quantity "x" 8) json).toOption ===
      (if shape == "array" && numbers.all below then some numbers else none)
    (JsonRpc.paramsArray json).toOption.map (·.length) ===
      (if shape == "array" then some numbers.length else none)
    (JsonRpc.nullable (JsonRpc.uint "x") json).toOption ===
      (if shape == "null" then some none else if shape == "string" then some (some 1) else none)
    (JsonRpc.bool "x" json).toOption === (if shape == "true" then some true else none)
    (JsonRpc.string "x" json).toOption === (if shape == "string" then some "0x1" else none)
    (JsonRpc.listJson JsonRpc.quantityJson numbers).compress === (Lean.Json.arr
      quantities.toArray).compress
    (JsonRpc.optionJson JsonRpc.quantityJson numbers.head?).compress ===
      (match numbers.head? with
        | some n => (JsonRpc.quantityJson n).compress
        | none => "null")
    -- The members of an object that are not null, and the two questions asked of them.
    let present := names.filter (!nulls.contains ·)
    match JsonRpc.fields "x" json with
    | .ok members =>
      ensure (shape == "object") "the members of a value that is no object"
      (members.map (·.1)).mergeSort === present.mergeSort
      classify "members: exactly those asked for" (JsonRpc.hasExactly members wanted)
      classify "members: only among those asked for" (JsonRpc.hasOnly members wanted)
      JsonRpc.hasExactly members wanted === (present.mergeSort == wanted.mergeSort)
      JsonRpc.hasOnly members wanted === present.all (wanted.contains ·)
      (JsonRpc.field "x" members "a").toOption.isSome === present.contains "a"
    | .error _ => ensure (shape != "object") "an object has no members"
    -- A number of a mantissa and an exponent is an integer when the power of ten divides.
    let number := Lean.Json.num ⟨mantissa, exponent⟩
    let read := JsonRpc.integer "x" number
    classify "a number: an integer" read.toOption.isSome
    classify "a number: an integer with an exponent" (read.toOption.isSome && exponent > 0)
    classify "a number: not an integer" read.toOption.isNone
    readText read toString ===
      (← oracle.ask ["jsonint", hex s!"{mantissa}e-{exponent}".toUTF8])

end SerializationProperty

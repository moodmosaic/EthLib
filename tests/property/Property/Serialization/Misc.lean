import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Rooted
import EthLib.Serialization.Der
import EthLib.Serialization.JsonRpc

/-!
# DER, JSON-RPC, the JSON form of SSZ, typed containers and typed RLP
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Serialization

namespace SerializationProperty

/-! ## DER -/

/-- The base-256 digits of a number, most significant first; none for zero. -/
def bigEndianDigits : Nat → List UInt8 → List UInt8
  | 0, done => done
  | n + 1, done => bigEndianDigits ((n + 1) / 256) (UInt8.ofNat ((n + 1) % 256) :: done)
decreasing_by omega

/-- How the length octets of a value are written. -/
inductive LengthStyle where
  /-- The one form DER allows. -/
  | shortest
  /-- The long form, whatever the length. -/
  | long
  /-- The long form with a zero octet in front. -/
  | padded
  /-- The indefinite form. -/
  | indefinite
  /-- The reserved first octet. -/
  | reserved
  deriving Repr

/-- The length octets of a count, in a style. -/
def lengthOctets (style : LengthStyle) (count : Nat) : List UInt8 :=
  let digits := if count == 0 then [0] else bigEndianDigits count []
  match style with
  | .shortest =>
    if count < 128 then [UInt8.ofNat count] else UInt8.ofNat (128 + digits.length) :: digits
  | .long => UInt8.ofNat (128 + digits.length) :: digits
  | .padded => UInt8.ofNat (129 + digits.length) :: 0 :: digits
  | .indefinite => [128]
  | .reserved => [255]

/-- A tag, its length octets and its content. -/
def tlv (style : LengthStyle) (tag : UInt8) (content : ByteArray) : ByteArray :=
  ⟨(tag :: lengthOctets style content.size).toArray⟩ ++ content

/-- A style: the shortest one most of the time. -/
def genStyle : Gen LengthStyle :=
  Gen.frequency [(8, pure .shortest), (2, pure .long), (1, pure .padded), (1, pure .indefinite),
    (1, pure .reserved)]

/-- A tag: one the validation reads, an edge, or any. -/
def genTag : Gen UInt8 :=
  Gen.frequency [
    (6, Gen.element [2, 1, 3, 4, 5, 6, 12, 19, 22, 28, 30, 48, 49]),
    (2, Gen.element [0, 31, 63, 0x7f, 0x9f, 0xa0, 0xbf, 0xff, 23, 24]),
    (1, genByte)]

/-- One tag, length and value read as X.690 writes them, and the bytes after. -/
def derRead (oracle : Oracle) : Property IO := propertyM do
  let tag ← forAll genTag
  let size ← forAll (genEdge [0, 1, 127, 128, 129, 255, 256] (.linear 0 20))
  let style ← forAll genStyle
  let content ← forAllWith hex (genBytesN size)
  let input ← forAllWith hex (genMutation (tlv style tag content))
  pure do
    let expected ← oracle.ask ["dertlv", hex input]
    match Der.read input with
    | .ok (value, rest) =>
      s!"{value.tag} {hex value.content} {hex rest}" === expected
      hex (value.encoded ++ rest) === hex input
    | .error e =>
      annotate s!"EthLib refused: {repr e}"
      expected === "error"

/-- The content octets of an integer in two's complement, the fewest that hold it. -/
def integerOctets (n : Int) : List UInt8 :=
  let size := (List.range 40).find?
      (fun k => -(2 : Int) ^ (8 * k + 7) ≤ n ∧ n < 2 ^ (8 * k + 7))
    |>.getD 40
  let word := (n % 2 ^ (8 * (size + 1))).toNat
  (List.range (size + 1)).reverse.map fun i => UInt8.ofNat (word / 256 ^ i)

/-- An integer at the edges of each count of octets. -/
def genInteger : Gen Int := do
  let bits ← Gen.element [7, 8, 15, 16, 63, 64, 255, 256, 1015, 1016]
  let near ← Gen.int (.linearFrom 0 (-3) 3)
  let sign ← Gen.element [1, -1]
  Gen.frequency [(3, pure (sign * (2 : Int) ^ bits + near)), (2,
      Gen.int (.linearFrom 0 (-70000) 70000))]

/-- The content of an INTEGER: its octets, or those with one octet too many, or none. -/
def genIntegerContent : Gen ByteArray := do
  let n ← genInteger
  let octets := integerOctets n
  let content ← Gen.frequency [
    (5, pure octets),
    (2, pure ((if n < 0 then 0xff else 0) :: octets)),
    (1, pure (0 :: octets)),
    (1, pure (0xff :: octets)),
    (1, pure [])]
  pure ⟨content.toArray⟩

/-- An INTEGER has the value of X.690, and one with a redundant octet has none. -/
def derInteger (oracle : Oracle) : Property IO := propertyM do
  let content ← forAllWith hex genIntegerContent
  let style ← forAll genStyle
  let tag ← forAll (Gen.frequency [(9, pure 2), (1, Gen.element [3, 0x22, 10])])
  let input := tlv style tag content
  pure do
    let expected ← oracle.ask ["derint", hex input]
    match Der.exact 2 input >>= Der.integer with
    | .ok n =>
      toString n === expected
      -- The natural number reader takes the same integers, without the negative ones.
      (Der.exact 2 input >>= Der.natural).toOption === (if n < 0 then none else some n.toNat)
    | .error _ => expected === "error"

/-- A signature of two integers reads as the reference reads it. -/
def derSignature (oracle : Oracle) : Property IO := propertyM do
  let r ← forAllWith hex genIntegerContent
  let s ← forAllWith hex genIntegerContent
  let styles ← forAll (Gen.zip genStyle (Gen.zip genStyle genStyle))
  let body := tlv styles.2.1 2 r ++ tlv styles.2.2 2 s
  let input ← forAllWith hex (Gen.frequency [(4, pure (tlv styles.1 0x30 body)),
    (1, genMutation (tlv styles.1 0x30 body))])
  pure do
    let expected ← oracle.ask ["dss", hex input]
    let got : Except Der.Error String := do
      let outer ← Der.exact 0x30 input
      match ← Der.children outer.content with
      -- The reference reads the two integers as natural numbers.
      | [first, second] => return s!"{← Der.natural first} {← Der.natural second}"
      | _ => throw .value
    match got with
    | .ok text => text === expected
    | .error e =>
      annotate s!"EthLib refused: {repr e}"
      expected === "error"

/-- The content of a value of a tag: valid most of the time, and near it. -/
def genContent (tag : UInt8) : Gen ByteArray :=
  let ofList (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩
  let units (width : Nat) : Gen ByteArray := do
    let scalars ← Gen.list (.linear 0 3) (Gen.frequency [
      (3, Gen.nat (.constant 0x20 0x7e)),
      (2, Gen.element [0, 0xd7ff, 0xd800, 0xdfff, 0xe000, 0xffff, 0x10000, 0x10ffff, 0x110000]),
      (1, Gen.nat (.exponential 0 (256 ^ width - 1)))])
    let extra ← Gen.frequency [(5, pure []), (1, pure [0])]
    pure (ofList (scalars.flatMap (fun n => (List.range width).reverse.map fun i =>
      UInt8.ofNat (n / 256 ^ i)) ++ extra))
  match tag.toNat with
  | 1 => ofList <$> Gen.element [[0], [255], [1], [], [0, 0], [254]]
  | 2 => genIntegerContent
  | 3 => do
    let unused : UInt8 ← Gen.frequency [(3, Gen.integral (.constant 0 7)), (1, pure 8)]
    let bytes ← genByteList (.linear 0 3)
    let clean ← Gen.bool
    let last := bytes.getLast?.map fun b => if clean then (b >>> unused) <<< unused else b
    pure (ofList (unused :: bytes.dropLast ++ last.toList))
  | 5 => ofList <$> Gen.element [[], [], [0]]
  | 6 => ofList <$> Gen.list (.linear 0 5) (Gen.frequency [(3, Gen.integral (.constant 0 127)),
      (2, Gen.element [0x80, 0x81, 0xff]), (1, genByte)])
  | 12 => Gen.frequency [
      (3, String.toUTF8 <$> Gen.string (.linear 0 4) Gen.unicode),
      (2, ofList <$> Gen.element [[0xc0, 0x80], [0xed, 0xa0, 0x80], [0xf4, 0x90, 0x80, 0x80],
        [0xe2, 0x82], [0x80], [0xf8, 0x88, 0x80, 0x80, 0x80], [0xed, 0x9f, 0xbf], [0xf4, 0x8f, 0xbf,
            0xbf],
        [0xc1, 0xbf], [0xe0, 0x9f, 0xbf], [0xf0, 0x8f, 0xbf, 0xbf], [0xef, 0xbf, 0xbf]]),
      (1, genBytes (.linear 0 4))]
  | 19 | 22 => ofList <$> Gen.list (.linear 0 5) (Gen.frequency [
      (4, Gen.integral (.constant 0x20 0x7e)), (1, Gen.element [0, 0x7f, 0x80, 0x2a, 0x40, 0x5f])])
  | 28 => units 4
  | 30 => units 2
  | _ => genBytes (.linear 0 4)

/-- A value of the subset that validation reads, of at most the depth. -/
def genDerOf : Nat → Gen ByteArray
  | 0 => do
    let tag ← Gen.element [1, 2, 3, 4, 5, 6, 12, 19, 22, 28, 30]
    let content ← genContent tag
    pure (tlv .shortest tag content)
  | depth + 1 => Gen.frequency [
      (2, genDerOf 0),
      (2, do
        let children ← Gen.list (.linear 0 4) (genDerOf depth)
        pure (tlv .shortest 48 (children.foldl (· ++ ·) .empty))),
      (2, do
        -- A set: its members in the order of their encodings, or as they came.
        let children ← Gen.list (.linear 0 4) (genDerOf depth)
        let sorted := children.mergeSort fun a b => a.data.toList ≤ b.data.toList
        let members ← Gen.element [sorted, children, sorted.reverse]
        pure (tlv .shortest 49 (members.foldl (· ++ ·) .empty)))]

/-- A value is valid DER of its type exactly when the model of X.690 says so. -/
def derValidate (oracle : Oracle) : Property IO := propertyM do
  let valid ← forAllWith hex (Gen.sized fun size => genDerOf (min 2 size.log2))
  let input ← forAllWith hex (Gen.frequency [(3, pure valid), (1, genMutation valid)])
  pure do
    let expected ← oracle.ask ["dervalid", hex input]
    let got := match Der.read input with
      | .ok (value, rest) => if rest.isEmpty then (Der.validate value).toOption.isSome else false
      | .error _ => false
    (if got then "ok" else "error") === expected

/-! ## JSON-RPC -/

/-- A text near a hexadecimal one: a marker, digits, and now and then what does not belong. -/
def genHexText : Gen String := do
  let marker ← Gen.frequency [(12, pure "0x"), (1, Gen.element ["0X", "", "x", "00x", " 0x",
      "0x0x"])]
  let count ← genEdge [0, 1, 2, 3, 15, 16, 17, 40, 41, 63, 64, 65] (.linear 0 20)
  let digit := Gen.frequency [
    (40, Gen.element "0123456789abcdef".toList),
    (1, Gen.element "ABCDEF".toList),
    (1, Gen.element "gGxX -+_\n٣é".toList)]
  let digits ← Gen.list (.singleton count) digit
  let lead ← Gen.frequency [(3, pure ""), (1, pure "0"), (1, pure "00")]
  let upper ← Gen.frequency [(9, pure false), (1, pure true)]
  let body := lead ++ String.ofList digits
  pure (marker ++ if upper then body.toUpper else body)

/-- What a reader made of a text, as the oracle writes it. -/
def readText {α : Type} (result : JsonRpc.Read α) (text : α → String) : String :=
  match result with
  | .ok value => text value
  | .error _ => "error"

/-- The readers accept exactly the patterns of `base-types.yaml`, with their values. -/
def rpcRead (oracle : Oracle) : Property IO := propertyM do
  let text ← forAll genHexText
  pure do
    let json := Lean.Json.str text
    let ask (kind : String) := oracle.ask ["rpc", kind, hex text.toUTF8]
    readText (JsonRpc.bytes "x" json) hex === (← ask "bytes")
    readText (JsonRpc.fixed "x" 32 json) (fun v => hex ⟨v.toArray⟩) === (← ask "hash32")
    readText (JsonRpc.fixed "x" 8 json) (fun v => hex ⟨v.toArray⟩) === (← ask "bytes8")
    readText (JsonRpc.address "x" json) (fun v => hex ⟨v.toArray⟩) === (← ask "address")
    readText (JsonRpc.uint "x" json) toString === (← ask "uint")
    readText (JsonRpc.uint64 "x" json) (toString ·.toNat) === (← ask "uint64")
    readText (JsonRpc.quantity "x" 256 json) toString === (← ask "uint256")

/-- The writers write texts of the patterns, which read back. -/
def rpcWrite (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll (Gen.choice [genNatBits 64, genNatBits 256, Gen.nat (.linear 0 300)])
  let bytes ← forAllWith hex (genBytes (.linear 0 40))
  pure do
    match JsonRpc.quantityJson n with
    | .str text => toString n === (← oracle.ask ["rpc", "uint", hex text.toUTF8])
    | _ => failWith "a quantity is not a string"
    tripping n JsonRpc.quantityJson (JsonRpc.uint "x")
    match JsonRpc.dataJson bytes.toList with
    | .str text => hex bytes === (← oracle.ask ["rpc", "bytes", hex text.toUTF8])
    | _ => failWith "data is not a string"
    (JsonRpc.bytes "x" (JsonRpc.dataJson bytes.toList)).toOption.map hex === some (hex bytes)

/-- A JSON number in text: digits, a fraction, an exponent. -/
def genNumberText : Gen String := do
  let sign ← Gen.element ["", "", "-"]
  let whole ← Gen.frequency [(1, pure "0"), (3, toString <$> Gen.nat (.exponential 1 (10 ^ 25)))]
  let fraction ← Gen.frequency [(2, pure ""),
    (1, (fun n => s!".{n}") <$> Gen.nat (.linear 0 5000)),
    (1, Gen.element [".0", ".000", ".50", ".05"])]
  let exponent ← Gen.frequency [(2, pure ""), (1, do
    let mark ← Gen.element ["e", "E", "e+", "e-", "E-"]
    let power ← Gen.nat (.linear 0 30)
    pure s!"{mark}{power}")]
  pure (sign ++ whole ++ fraction ++ exponent)

/-- A JSON number reads as an integer exactly when its value is one. -/
def rpcInteger (oracle : Oracle) : Property IO := propertyM do
  let text ← forAll genNumberText
  pure do
    let expected ← oracle.ask ["jsonint", hex text.toUTF8]
    match Lean.Json.parse text with
    | .ok json => readText (JsonRpc.integer "x" json) toString === expected
    | .error e => failWith s!"the number does not parse: {e}"

/-- An error object reads back, with its data kept apart from no data. -/
def rpcError : Property IO := pureIO do
  let code ← forAll (Gen.int (.linearFrom 0 (-40000) 40000))
  let message ← forAll (Gen.string (.linear 0 8) Gen.alphaNum)
  let data ← forAll (Gen.element [none, some "null", some "1", some "\"x\"", some "[]"])
  let extra ← forAll (Gen.element [none, none, some "id", some "Code"])
  let json := fun (d : Option String) => d.bind fun t => (Lean.Json.parse t).toOption
  let error : JsonRpc.RpcError := ⟨code, message, json data⟩
  let written := JsonRpc.rpcErrorJson error
  let written := match extra with
    | some name => written.setObjVal! name (.num 1)
    | none => written
  match JsonRpc.rpcErrorOfJson written with
  | .ok read =>
    ensure extra.isNone "a member other than code, message and data was accepted"
    (read.code, read.message, read.data.map (·.compress)) === (code, message,
        (json data).map (·.compress))
  | .error _ => ensure extra.isSome "an error object does not read back"

/-! ## The JSON form of SSZ -/

open Ssz in
/-- The document of a value under no spelling mark, written from the mapping. -/
partial def documentText : Desc → Value → String
  | _, .bool b => if b then "true" else "false"
  | _, .uint n => quoted (toString n)
  | _, .bytes data => quoted ("0x" ++ hexOf data)
  | shape, .bits data => quoted ("0x" ++ hexOf ((serialize shape (.bits data)).toOption.getD #[]))
  | .container names fields, .seq values | .progressiveContainer _ names fields, .seq values =>
    "{" ++ ",".intercalate ((names.zip (fields.zip values)).map fun (name, field, value) =>
      quoted name ++ ":" ++ documentText field value) ++ "}"
  | .vector element _, .seq values | .list element _, .seq values
  | .progressiveList element _, .seq values => jsonArray (values.map (documentText element))
  | .compatibleUnion selectors options, .union selector data =>
    let option := (selectors.zip options).lookup selector |>.getD .bool
    "{\"data\":" ++ documentText option data ++ ",\"selector\":" ++ quoted (toString selector) ++
        "}"
  | _, _ => "?"

instance : Inhabited (Gen Ssz.Spelling) := ⟨pure .opaque⟩

open Ssz in
/-- A spelling for a type: marks where they have an effect, and some where they have none. -/
partial def genSpelling (shape : Desc) : Gen Spelling :=
  let parts (children : List Desc) : Gen Spelling := .plain <$>
      Gen.sequence (children.map genSpelling)
  let any := Gen.element [Spelling.opaque, .byte, .digits, .text]
  match shape with
  | .uint 1 => Gen.element [.opaque, .byte, .digits]
  | .byteList _ => any
  | .vector element _ | .list element _ | .progressiveList element _ =>
    Gen.frequency [(3, parts [element]), (1, any)]
  | .container _ fields | .progressiveContainer _ _ fields => parts fields
  | .compatibleUnion _ options => parts options
  | _ => Gen.frequency [(5, pure .opaque), (1, any)]

/-- A value written as a document reads back, under every spelling. -/
def sszJsonTrip : Property IO := pureIO do
  let (shape, value) ← forAllWith typedText genTyped
  let spelling ← forAllWith (fun _ => "a spelling") (genSpelling shape)
  match Ssz.jsonOf shape spelling value with
  | .ok document =>
    annotate document.compress
    match Ssz.valueOf shape spelling document with
    | .ok read => valueText read === valueText value
    | .error e => failWith s!"the document was refused: {repr e}"
    -- A document survives its text.
    match Lean.Json.parse document.compress with
    | .ok parsed =>
      (Ssz.valueOf shape spelling parsed).toOption.map valueText === some (valueText value)
    | .error e => failWith s!"the text of the document does not parse: {e}"
  | .error e => failWith s!"no document: {repr e}"

/-- Under no spelling mark, the document is the one the mapping describes. -/
def sszJsonModel : Property IO := pureIO do
  let (shape, value) ← forAllWith typedText genTyped
  (Ssz.jsonOf shape .opaque value).toOption.map (·.compress) === some (documentText shape value)

/-- A text near the digits of a number. -/
def genDigits (n : Nat) : Gen String :=
  Gen.element [toString n, s!"0{n}", s!"+{n}", s!" {n}", s!"{n} ", s!"{n}.0", "", s!"0x{n}",
      s!"-{n}",
    s!"{n}e0", s!"٣{n}", s!"{n}_"]

/-- An integer is read from its digits alone, and only within its width. -/
def sszJsonUint : Property IO := pureIO do
  let width ← forAll (Gen.element [1, 2, 4, 8, 16, 32])
  let n ← forAll (Gen.frequency [(2, genNatBits (8 * width)),
    (1, (2 ^ (8 * width) + ·) <$> Gen.nat (.linear 0 3))])
  let text ← forAll (genDigits n)
  let read := (Ssz.valueOf (.uint width) .opaque (.str text)).toOption.map valueText
  let valid := text == toString n && n < 2 ^ (8 * width)
  read === (if valid then some (quoted (toString n)) else none)
  -- A bare number reads as its digits do.
  (Ssz.valueOf (.uint width) .opaque (.num n)).toOption.isSome === decide (n < 2 ^ (8 * width))

/-! ## Typed containers -/

/-- A container with fixed and variable fields of each kind. -/
structure Record where
  a : UInt64
  b : Ssz.SszList UInt16 5
  c : Ssz.Bitlist 9
  d : Vector UInt8 4
  e : Ssz.ProgressiveList UInt32
  f : Ssz.Bitvector 10
  g : Ssz.SszList Pair 3
  h : Bool
  i : Vector (Ssz.SszList UInt8 3) 2
  j : U256

open Ssz in
instance : SszType Record :=
  SszType.container ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]
    (fun r => (r.a, r.b, r.c, r.d, r.e, r.f, r.g, r.h, r.i, r.j))
    (fun (a, b, c, d, e, f, g, h, i, j) => ⟨a, b, c, d, e, f, g, h, i, j⟩)

/-- A progressive container with gaps in its layout, and lists that a fork changes. -/
structure Sparse where
  a : UInt32
  b : Ssz.ForkList .glamsterdam .glamsterdam UInt16 4
  c : Ssz.ForkList .glamsterdam .fusaka UInt8 6
  d : Ssz.ForkBitlist .glamsterdam .glamsterdam 3
  e : Ssz.ProgressiveBitlist
  f : Pair

open Ssz in
instance : SszType Sparse :=
  SszType.progressiveContainer [true, false, true, true, false, false, true, true, true]
    ["a", "b", "c", "d", "e", "f"]
    (fun r => (r.a, r.b, r.c, r.d, r.e, r.f)) (fun (a, b, c, d, e, f) => ⟨a, b, c, d, e, f⟩)

/-- Fields only, all of fixed size. -/
structure Fixed where
  a : Vector UInt16 3
  b : Pair
  c : Ssz.Bitvector 3

open Ssz in
instance : SszType Fixed :=
  SszType.container ["a", "b", "c"] (fun r => (r.a, r.b, r.c)) (fun (a, b, c) => ⟨a, b, c⟩)

open Ssz in
/-- A typed value has the bytes and the root of the reference, and its decoder accepts the same. -/
def typedCodec (oracle : Oracle) (α : Type) [SszType α] : Property IO := propertyM do
  let shape := SszType.desc α
  let value ← forAllWith valueText (genValueOf true shape)
  let valid := (serialize shape value).toOption.getD #[]
  let input ← forAllWith hex (genMutation ⟨valid⟩)
  pure do
    match SszType.ofValue (α := α) value with
    | .error e => failWith s!"a value of the type was refused: {repr e}"
    | .ok typed =>
      typedEncoded typed === (← oracle.ask ["sszenc", typeText shape, valueText value])
      valueText (SszType.toValue typed) === valueText value
    let expected ← oracle.ask ["sszdec", typeText shape, hex input]
    match SszType.decode (α := α) input with
    | .ok typed =>
      annotate s!"EthLib read {valueText (SszType.toValue typed)}"
      typedEncoded typed === expected
    | .error e =>
      annotate s!"the specification: {expected}"
      refusal e === faultOf expected
    -- The typed decoder and the untyped one refuse the same input.
    (SszType.decode (α := α) input).toOption.isSome ===
        (deserialize shape input.data).toOption.isSome

/-! ## Typed RLP -/

/-- A typed value written as an item reads back, and an item out of the type's range does not. -/
def rlpCodec : Property IO := pureIO do
  let n ← forAll (genNatBits 70)
  let bytes ← forAllWith hex (genBytes (.linear 0 40))
  tripping n (Rlp.Codec.toItem (α := Nat)) (Rlp.Codec.ofItem (α := Nat))
  let item := Rlp.Item.scalar n
  (Rlp.Codec.ofItem (α := UInt64) item).toOption.map (·.toNat) ===
      (if n < 2 ^ 64 then some n else none)
  (Rlp.Codec.ofItem (α := UInt32) item).toOption.map (·.toNat) ===
      (if n < 2 ^ 32 then some n else none)
  (Rlp.Codec.ofItem (α := UInt16) item).toOption.map (·.toNat) ===
      (if n < 2 ^ 16 then some n else none)
  (Rlp.Codec.ofItem (α := UInt8) item).toOption.map (·.toNat) ===
      (if n < 2 ^ 8 then some n else none)
  (Rlp.Codec.ofItem (α := Bool) item).toOption === (if n < 2 then some (n == 1) else none)
  (Rlp.Codec.ofItem (α := U256) item).toOption.map (·.toNat) === some n
  -- A byte string of a fixed length, and an optional one: empty is none.
  (Rlp.Codec.ofItem (α := Vector UInt8 20) (.bytes bytes)).toOption.isSome === (bytes.size == 20)
  (Rlp.Codec.ofItem (α := Option (Vector UInt8 20)) (.bytes bytes)).toOption.map (·.isSome) ===
    (if bytes.size == 20 then some true else if bytes.size == 0 then some false else none)
  -- A scalar with a leading zero byte is no value of any integer type.
  let padded := Rlp.Item.bytes (⟨#[0]⟩ ++ Rlp.bigEndian n)
  (Rlp.Codec.ofItem (α := Nat) padded).toOption === none
  (Rlp.Codec.ofItem (α := List UInt64) (.list [item, padded])).toOption.map (·.length) === none

end SerializationProperty

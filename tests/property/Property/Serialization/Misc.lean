import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Classes
import Property.Serialization.Near
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

/-- The verdict of a DER reader, by the constructor of its error. -/
def derVerdict {α : Type} : Except Der.Error α → String
  | .ok _ => "accepted"
  | .error (.truncated ..) => "truncated"
  | .error (.tag ..) => "tag"
  | .error (.length _) => "length"
  | .error .value => "value"
  | .error (.trailing _) => "trailing"

/-- The verdicts of a DER reader. -/
def derVerdicts : List String := ["accepted", "truncated", "tag", "length", "value", "trailing"]

/-- The form of the length octets of an input, by its second byte. -/
def lengthForm (input : ByteArray) : String :=
  match input.data[1]? with
  | none => "none"
  | some first =>
    if first < 128 then "short"
    else if first == 128 then "indefinite, 0x80"
    else if first == 255 then "reserved, 0xff"
    else if first == 129 then "long on 1 octet"
    else if first == 130 then "long on 2 octets"
    else "long on 3 octets or more"

/-- The forms of the length octets. -/
def lengthForms : List String :=
  ["none", "short", "indefinite, 0x80", "reserved, 0xff", "long on 1 octet", "long on 2 octets",
    "long on 3 octets or more"]

/-- The tag of an input, by the branch of the reader that takes it. -/
def tagClass (input : ByteArray) : String :=
  match input.data[0]? with
  | none => "none"
  | some tag =>
    if tag == 0 then "0"
    else if tag.toNat % 32 == 31 then "a high tag number"
    else if tag.toNat ≥ 64 then "of another class than universal"
    else if tag.toNat ≥ 32 then "universal, constructed" else "universal, primitive"

/-- The classes of a tag. -/
def tagClasses : List String :=
  ["none", "0", "a high tag number", "of another class than universal", "universal, constructed",
    "universal, primitive"]

/-- One tag, length and value read as X.690 writes them, and the bytes after. -/
def derRead (oracle : Oracle) : Property IO := propertyM do
  let tag ← forAll genTag
  -- A content of 65536 bytes has its length on three octets.
  let size ← forAll (Gen.frequency [(8, genEdge [0, 1, 127, 128, 129, 255, 256] (.linear 0 20)),
    (1, Gen.element [65535, 65536])])
  let style ← forAll genStyle
  let content ← forAllWith hex (if size > 1000 then genRun [size] else genBytesN size)
  let input ← forAllWith hex (genMutation (tlv style tag content))
  pure do
    -- The reader of one value judges no content, and leaves the bytes after it.
    classifyOne "verdict" (derVerdicts.take 4) (derVerdict (Der.read input))
    classifyOne "length" lengthForms (lengthForm input)
    classifyOne "tag" tagClasses (tagClass input)
    classify "bytes follow the value"
      (match Der.read input with
        | .ok (_, rest) => !rest.isEmpty
        | .error _ => false)
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
  Gen.frequency [(3, pure (sign * (2 : Int) ^ bits + near)),
    (2, Gen.int (.linearFrom 0 (-70000) 70000)),
    -- The integers of one octet, and those at its edges.
    (3, Gen.element [0, 0, 0, 0, 0, 1, -1, 2, 127, -128, 128, -129, 255, 256])]

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
  let whole := tlv style tag content
  -- The value cut by a byte, or with a byte after it, now and then.
  let input ← forAllWith hex (Gen.frequency [(8, pure whole),
    (1, pure (whole.extract 0 (whole.size - 1))), (1, pure (whole.push 0))])
  pure do
    classifyOne "verdict" derVerdicts (derVerdict (Der.exact 2 input >>= Der.integer))
    classifyOne "integer" ["none", "negative", "0", "positive"]
      (match Der.exact 2 input >>= Der.integer with
        | .error _ => "none"
        | .ok n => if n < 0 then "negative" else if n == 0 then "0" else "positive")
    classifyOne "content" ["no octet", "1 octet", "2 to 8 octets", "9 octets or more"]
      (if content.size == 0 then "no octet" else if content.size == 1 then "1 octet"
        else if content.size ≤ 8 then "2 to 8 octets" else "9 octets or more")
    let expected ← oracle.ask ["derint", hex input]
    match Der.exact 2 input >>= Der.integer with
    | .ok n =>
      toString n === expected
      -- The natural number reader takes the same integers, without the negative ones.
      (Der.exact 2 input >>= Der.natural).toOption === (if n < 0 then none else some n.toNat)
    | .error _ => expected === "error"

/-- A signature of two integers reads as the reference reads it. -/
def derSignature (oracle : Oracle) : Property IO := propertyM do
  -- Two natural numbers in the shortest form most of the time, so that many signatures read.
  let natural : Gen ByteArray := Gen.frequency [
    (3, (fun (n : Int) => ⟨(integerOctets n.natAbs).toArray⟩) <$> genInteger),
    (1, genIntegerContent)]
  let r ← forAllWith hex natural
  let s ← forAllWith hex natural
  let styles ← forAll (Gen.frequency [(3, pure (.shortest, .shortest, .shortest)),
    (1, Gen.zip genStyle (Gen.zip genStyle genStyle))])
  let body := tlv styles.2.1 2 r ++ tlv styles.2.2 2 s
  let input ← forAllWith hex (Gen.frequency [(6, pure (tlv styles.1 0x30 body)),
    (2, genMutation (tlv styles.1 0x30 body)),
    -- Another tag than SEQUENCE, and an INTEGER too many.
    (1, (tlv styles.1 · body) <$> Gen.element [0x31, 0x10, 0x04]),
    (1, pure (tlv styles.1 0x30 (body ++ tlv .shortest 2 r)))])
  pure do
    let expected ← oracle.ask ["dss", hex input]
    let got : Except Der.Error String := do
      let outer ← Der.exact 0x30 input
      match ← Der.children outer.content with
      -- The reference reads the two integers as natural numbers.
      | [first, second] => return s!"{← Der.natural first} {← Der.natural second}"
      | _ => throw .value
    classifyOne "verdict" derVerdicts (derVerdict got)
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

/-- The tag of every value that an input holds, itself first, while it reads. -/
partial def tagsOf (input : ByteArray) : List String :=
  match Der.read input with
  | .error _ => []
  | .ok (value, _) =>
    toString value.tag :: (if value.tag == 48 || value.tag == 49 then
      match Der.children value.content with
      | .ok values => values.flatMap fun child => tagsOf child.encoded
      | .error _ => []
    else [])

/-- The tags that validation reads. -/
def validatedTags : List String :=
  [1, 2, 3, 4, 5, 6, 12, 19, 22, 28, 30, 48, 49].map toString

/-- A content that is not valid for a tag, by one rule of the type of that tag. -/
def genBadContent (tag : UInt8) : Gen ByteArray :=
  let ofList (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩
  let child : ByteArray := ofList [2, 1, 5]
  ofList <$> match tag.toNat with
  | 1 => Gen.element [[], [1], [0, 0], [254], [255, 255]]
  | 2 => Gen.element [[], [0, 0], [0, 0x7f], [0xff, 0x80], [0xff, 0xff], [0, 0, 0x80]]
  | 3 => Gen.element [[], [8], [1], [7], [3, 0xff], [1, 0, 1], [9, 0]]
  | 5 => Gen.element [[0], [0, 0], [5]]
  | 6 => Gen.element [[], [0x80, 1], [0x81], [1, 0x80, 1], [1, 2, 0xff]]
  | 12 => Gen.element [[0xc0, 0x80], [0xed, 0xa0, 0x80], [0xf4, 0x90, 0x80, 0x80], [0xe2, 0x82],
      [0x80], [0xf8, 0x88, 0x80, 0x80, 0x80], [0xc1, 0xbf], [0x41, 0xff]]
  | 19 => Gen.element [[0x2a], [0x40], [0x41, 0x5f], [0], [0x80], [0x26]]
  | 22 => Gen.element [[0x80], [0x41, 0xff], [0xc3, 0xa9]]
  | 28 => Gen.element [[0], [0, 0, 0], [0, 0, 0xd8, 0], [0, 0x11, 0, 0], [0, 0, 0, 0x41, 0],
      [0xff, 0xff, 0xff, 0xff]]
  | 30 => Gen.element [[0], [0, 0x41, 0], [0xd8, 0], [0xdf, 0xff], [0, 0x41, 0xdc, 0]]
  | 48 => Gen.element [[2], [2, 2, 5], [2, 0], [2, 1, 5, 1, 1, 7], [0, 0], [31, 1, 0],
      [48, 3, 1, 1, 9]]
  -- A set: a member that is not valid, or members out of the order of their encodings.
  | _ => Gen.element [[2], [2, 0], child.toList ++ [1, 1, 0], [4, 1, 9, 4, 1, 8],
      [49, 3, 5, 1, 0], [2, 1, 5, 2, 1, 4]]

/-- A value with a content that is not valid for its tag, at the root or as a member. -/
def genBadDer : Gen ByteArray := do
  let tag ← Gen.element [1, 2, 3, 5, 6, 12, 19, 22, 28, 30, 48, 49]
  let bad := tlv .shortest tag (← genBadContent tag)
  let good ← genDerOf 0
  Gen.frequency [(4, pure bad), (1, pure (tlv .shortest 48 (good ++ bad))),
    (1, pure (tlv .shortest 49 bad))]

/-- A value is valid DER of its type exactly when the model of X.690 says so. -/
def derValidate (oracle : Oracle) : Property IO := propertyM do
  let valid ← forAllWith hex (Gen.sized fun size => genDerOf (min 2 size.log2))
  let input ← forAllWith hex (Gen.frequency [(3, pure valid), (1, genMutation valid),
    (5, genBadDer)])
  pure do
    let expected ← oracle.ask ["dervalid", hex input]
    let got := match Der.read input with
      | .ok (value, rest) => if rest.isEmpty then (Der.validate value).toOption.isSome else false
      | .error _ => false
    classify "verdict: valid" got
    classify "verdict: not valid" (!got)
    classify "the generated value, unchanged" (input == valid)
    let tags := (tagsOf input).filter (validatedTags.contains ·)
    classifyAny "holds the tag" validatedTags tags
    -- An OCTET STRING, the tag 4, is valid whatever it holds.
    (validatedTags.filter (· != "4")).forM fun tag =>
      classify s!"not valid, at the root the tag: {tag}" (!got && tags.head? == some tag)
    (if got then "ok" else "error") === expected

/-! ## JSON-RPC -/

/-- A text near a hexadecimal one: a marker, digits, and now and then what does not belong. -/
def genHexText : Gen String := do
  let marker ← Gen.frequency [(12, pure "0x"), (1, Gen.element ["0X", "", "x", "00x", " 0x",
      "0x0x"])]
  let count ← Gen.frequency [(3, Gen.element [16, 40, 64]),
    (3, Gen.element [0, 1, 2, 3, 15, 17, 39, 41, 63, 65, 65, 66]),
    (2, Gen.nat (.linear 0 20))]
  -- Most texts hold digits of the pattern only: one stray digit in 64 refuses nearly all.
  let quality ← Gen.frequency [(5, pure 0), (2, pure 1), (2, pure 2)]
  let digit := Gen.frequency [
    (40, Gen.element "0123456789abcdef".toList),
    (if quality ≥ 1 then 6 else 0, Gen.element "ABCDEF".toList),
    (if quality ≥ 2 then 1 else 0, Gen.element "gGxX -+_\n٣é".toList)]
  let digits ← Gen.list (.singleton count) digit
  let lead ← Gen.frequency [(8, pure ""), (1, pure "0"), (1, pure "00")]
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
    classify "bytes: accepted" (JsonRpc.bytes "x" json).toOption.isSome
    classify "hash32: accepted" (JsonRpc.fixed "x" 32 json).toOption.isSome
    classify "bytes8: accepted" (JsonRpc.fixed "x" 8 json).toOption.isSome
    classify "address: accepted" (JsonRpc.address "x" json).toOption.isSome
    classify "address: accepted with an upper-case digit"
      ((JsonRpc.address "x" json).toOption.isSome && text.toLower != text)
    classify "uint: accepted" (JsonRpc.uint "x" json).toOption.isSome
    classify "uint64: accepted" (JsonRpc.uint64 "x" json).toOption.isSome
    classify "uint64: refused, uint accepted"
      ((JsonRpc.uint64 "x" json).toOption.isNone && (JsonRpc.uint "x" json).toOption.isSome)
    classify "uint256: accepted" (JsonRpc.quantity "x" 256 json).toOption.isSome
    classify "uint256: refused, uint accepted"
      ((JsonRpc.quantity "x" 256 json).toOption.isNone && (JsonRpc.uint "x" json).toOption.isSome)
    classify "no reader accepts"
      ((JsonRpc.bytes "x" json).toOption.isNone && (JsonRpc.uint "x" json).toOption.isNone &&
        (JsonRpc.address "x" json).toOption.isNone)
    readText (JsonRpc.bytes "x" json) hex === (← ask "bytes")
    readText (JsonRpc.fixed "x" 32 json) (fun v => hex ⟨v.toArray⟩) === (← ask "hash32")
    readText (JsonRpc.fixed "x" 8 json) (fun v => hex ⟨v.toArray⟩) === (← ask "bytes8")
    readText (JsonRpc.address "x" json) (fun v => hex ⟨v.toArray⟩) === (← ask "address")
    readText (JsonRpc.uint "x" json) toString === (← ask "uint")
    readText (JsonRpc.uint64 "x" json) (toString ·.toNat) === (← ask "uint64")
    readText (JsonRpc.quantity "x" 256 json) toString === (← ask "uint256")

/-- The writers write texts of the patterns, which read back. -/
def rpcWrite (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll (Gen.frequency [(3, genNatBits 64), (3, genNatBits 256),
    (3, Gen.nat (.linear 0 300)), (1, Gen.element [0, 1, 15, 16])])
  let bytes ← forAllWith hex (genBytes (.linear 0 40))
  pure do
    classifyOne "quantity" ["0", "1 to 15", "16 to 2^64 - 1", "2^64 or more"]
      (if n == 0 then "0" else if n < 16 then "1 to 15" else if n < 2 ^ 64 then "16 to 2^64 - 1"
        else "2^64 or more")
    classify "data: no byte" bytes.isEmpty
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
    let read := (Lean.Json.parse text).toOption.bind fun json =>
      (JsonRpc.integer "x" json).toOption
    classify "verdict: an integer" read.isSome
    classify "verdict: not an integer" read.isNone
    classify "an integer written with a fraction or an exponent"
      (read.isSome && (text.contains '.' || text.contains 'e' || text.contains 'E'))
    classify "an integer below zero" (read.any (· < 0))
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
  classify "verdict: read" (JsonRpc.rpcErrorOfJson written).toOption.isSome
  classify "verdict: refused" (JsonRpc.rpcErrorOfJson written).toOption.isNone
  classify "with data" data.isSome
  classify "with the data null" (data == some "null")
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

/-- The marks of a spelling, wherever they sit. -/
partial def marksOf : Ssz.Spelling → List String
  | .byte => ["byte"]
  | .digits => ["digits"]
  | .text => ["text"]
  | .plain parts => parts.flatMap marksOf

/-- The marks under which a value has another document than under none. -/
def effectiveMarks (shape : Ssz.Desc) (spelling : Ssz.Spelling) (value : Ssz.Value) :
    List String :=
  let text (s : Ssz.Spelling) := (Ssz.jsonOf shape s value).toOption.map (·.compress)
  if text spelling == text .opaque then [] else marksOf spelling

/-- A value written as a document reads back, under every spelling. -/
def sszJsonTrip : Property IO := pureIO do
  let (shape, value) ← forAllWith typedText genTyped
  let spelling ← forAllWith (fun _ => "a spelling") (genSpelling shape)
  classifyAny "spelling" ["byte", "digits", "text"] (marksOf spelling)
  classifyAny "a mark that changes the document" ["byte", "digits", "text"]
    (effectiveMarks shape spelling value)
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
  let text ← forAll (Gen.frequency [(1, pure (toString n)), (2, genDigits n)])
  let read := (Ssz.valueOf (.uint width) .opaque (.str text)).toOption.map valueText
  let valid := text == toString n && n < 2 ^ (8 * width)
  classifyOne "width" ["1", "2", "4", "8", "16", "32"] (toString width)
  classify "digits: read" valid
  classify "digits: out of the width" (text == toString n && !valid)
  classify "digits: another text" (text != toString n)
  classify "a number: out of the width" (n ≥ 2 ^ (8 * width))
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
  let input ← forAllWith hex (genNearEncoding shape ⟨valid⟩)
  pure do
    match SszType.ofValue (α := α) value with
    | .error e => failWith s!"a value of the type was refused: {repr e}"
    | .ok typed =>
      typedEncoded typed === (← oracle.ask ["sszenc", typeText shape, valueText value])
      valueText (SszType.toValue typed) === valueText value
    -- Only the reasons that the parts of the type can give are listed.
    labelOutcome (decodeReasons.filter ((rootReasons shape).contains ·))
      (SszType.decode (α := α) input)
    classify "the encoding of a value, unchanged" (input.data == valid)
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
  let bits ← forAll (Gen.element [1, 8, 16, 32, 64, 70, 256, 264])
  let n ← forAll (genNatBits bits)
  let bytes ← forAllWith hex (Gen.frequency [(1, genBytesN 20), (2, genBytes (.linear 0 40))])
  classifyOne "scalar" ["below 2", "2 to 2^8 - 1", "2^8 to 2^16 - 1", "2^16 to 2^32 - 1",
      "2^32 to 2^64 - 1", "2^64 to 2^256 - 1", "2^256 or more"]
    (if n < 2 then "below 2" else if n < 2 ^ 8 then "2 to 2^8 - 1"
      else if n < 2 ^ 16 then "2^8 to 2^16 - 1" else if n < 2 ^ 32 then "2^16 to 2^32 - 1"
      else if n < 2 ^ 64 then "2^32 to 2^64 - 1" else if n < 2 ^ 256 then "2^64 to 2^256 - 1"
      else "2^256 or more")
  classifyOne "bytes" ["none", "20", "another count"]
    (if bytes.size == 0 then "none" else if bytes.size == 20 then "20" else "another count")
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
  (Rlp.Codec.ofItem (α := U256) item).toOption.map (·.toNat) ===
      (if n < 2 ^ 256 then some n else none)
  -- A byte string of a fixed length, and an optional one: empty is none.
  (Rlp.Codec.ofItem (α := Vector UInt8 20) (.bytes bytes)).toOption.isSome === (bytes.size == 20)
  (Rlp.Codec.ofItem (α := Option (Vector UInt8 20)) (.bytes bytes)).toOption.map (·.isSome) ===
    (if bytes.size == 20 then some true else if bytes.size == 0 then some false else none)
  -- A scalar with a leading zero byte is no value of any integer type.
  let padded := Rlp.Item.bytes (⟨#[0]⟩ ++ Rlp.bigEndian n)
  (Rlp.Codec.ofItem (α := Nat) padded).toOption === none
  (Rlp.Codec.ofItem (α := List UInt64) (.list [item, padded])).toOption.map (·.length) === none

end SerializationProperty

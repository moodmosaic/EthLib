import Hedgehog
import Support
import EthLib.Base

/-!
# The base layer, on generated inputs

Each property generates inputs and requires an answer that EthLib did not compute.

It is that of a reference implementation (`oracle/base.py`), or of arithmetic on `Nat` and `Int`.

    lake exe base-property            # 100 cases of each
    lake exe base-property 10000
-/

open Hedgehog Support EthLib EthLib.Base

namespace BaseProperty

/-! ## Base64 -/

/-- The encoder writes the text of the reference. -/
def base64Encode (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAll (genBytes (.linear 0 64))
  pure do
    let text := Base64.encode bytes
    (if text.isEmpty then "-" else text) === (← oracle.ask ["b64enc", hex bytes])

/-- A text over the alphabet and a little outside it, of a length that reaches every tail. -/
def genBase64Text : Gen String :=
  Gen.string (.linear 0 12) (Gen.frequency [
    (8, Gen.element "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList),
    (1, Gen.element "=+/ ".toList)])

/-- The decoder accepts the canonical texts, and gives the bytes of the reference. -/
def base64Decode (oracle : Oracle) : Property IO := propertyM do
  let text ← forAll genBase64Text
  pure do
    let expected ← oracle.ask ["b64dec", hex text.toUTF8]
    match Base64.decode text with
    | .ok bytes => hex bytes === expected
    | .error _ => expected === "error"

/-! ## NFKD -/

/-- A code point: mostly from the blocks that decompose or combine. -/
def genChar : Gen Char :=
  Gen.frequency [
    (2, Gen.char (.constant 'a' 'z')),
    (3, Gen.char (.constant (Char.ofNat 0xA0) (Char.ofNat 0x36F))),
    (2, Gen.char (.constant (Char.ofNat 0x900) (Char.ofNat 0x33FF))),
    (2, Gen.char (.constant (Char.ofNat 0xAC00) (Char.ofNat 0xD7A3))),
    (2, Gen.char (.constant (Char.ofNat 0xF900) (Char.ofNat 0xFFEF))),
    (2, Gen.char (.constant (Char.ofNat 0x10000) (Char.ofNat 0x1FBFF))),
    (1, Gen.unicode)]

/-- Code points in hexadecimal. -/
def points (chars : List Char) : List String :=
  chars.map fun c => String.ofList (Nat.toDigits 16 c.toNat)

/-- NFKD is the host's, on the code points the host knows. -/
def nfkd (oracle : Oracle) : Property IO := propertyM do
  let chars ← forAllWith (fun cs => " ".intercalate (points cs)) (Gen.list (.linear 0 8) genChar)
  pure do
    let expected ← oracle.ask ("nfkd" :: points chars)
    if expected = "skip" then pure ()
    else
      let got := points (Unicode.nfkd (String.ofList chars)).toList
      (if got.isEmpty then "-" else " ".intercalate got) === expected

/-! ## Integers -/

/-- The integer square root is the reference's. -/
def squareRoot (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll genUInt64
  pure do
    toString (Uint64.integerSquareroot n).toNat === (← oracle.ask ["isqrt", toString n.toNat])

/-- Checked arithmetic is arithmetic on `Nat`, and an error exactly out of range. -/
def checked : Property IO := pureIO do
  let a ← forAll genUInt64
  let b ← forAll genUInt64
  let agrees (got : Except ArithError UInt64) (want : Option Nat) : Bool :=
    match got, want with
    | .ok x, some n => x.toNat == n && n < 2 ^ 64
    | .error _, some n => n ≥ 2 ^ 64
    | .error _, none => true
    | .ok _, none => false
  ensure (agrees (Uint64.addChecked a b) (some (a.toNat + b.toNat))) "addChecked"
  ensure (agrees (Uint64.mulChecked a b) (some (a.toNat * b.toNat))) "mulChecked"
  ensure (agrees (Uint64.subChecked a b) (if b ≤ a then some (a.toNat - b.toNat) else none))
    "subChecked"
  ensure (agrees (Uint64.divChecked a b) (if b = 0 then none else some (a.toNat / b.toNat)))
    "divChecked"
  (Uint64.saturatingSub a b).toNat === a.toNat - b.toNat

/-- A 256-bit word read as two's complement and written back. -/
def signed : Property IO := pureIO do
  let n ← forAll (genNatBits 256)
  let w : U256 := BitVec.ofNat 256 n
  let v := U256.toSigned w
  ensure (-(2 : Int) ^ 255 ≤ v ∧ v < 2 ^ 255) "toSigned is out of range"
  ensure (v % 2 ^ 256 == (n : Int)) "toSigned is not the word modulo 2^256"
  (U256.fromSigned v).toNat === n

/-- Big-endian and little-endian bytes are the digits of the number. -/
def endian : Property IO := pureIO do
  let len ← forAll (Gen.nat (.linear 0 40))
  let n ← forAll (genNatBits (8 * len))
  let be := natToBytes len n
  be.length === len
  bytesToNat be === n
  let le := (uintToBytes len n).toList
  le === be.reverse
  bytesToUint (uintToBytes len n) === n

/-- Hexadecimal text reads back, in either case, and nothing else reads. -/
def hexRoundTrip : Property IO := pureIO do
  let bytes ← forAll (genByteList (.linear 0 40))
  let marked := hexString bytes
  ensure (marked.toList.take 2 == ['0', 'x']) "no 0x marker"
  let text := String.ofList (marked.toList.drop 2)
  ensure ((hexBytes? text.toList).map (·.toList) == some bytes) "lower case does not read back"
  ensure ((hexBytes? text.toUpper.toList).map (·.toList) == some bytes)
    "upper case does not read back"
  let junk ← forAll (Gen.string (.linear 0 6) Gen.ascii)
  let valid := junk.length % 2 == 0 &&
    junk.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  (hexBytes? junk.toList).isSome === valid

/-- The gas limit moves toward the target and stays within the bound of a child. -/
def gasLimit : Property IO := pureIO do
  let parent ← forAll (genNatBits 40)
  let target ← forAll (Gen.choice [genNatBits 40, (parent + ·) <$> Gen.nat (.linear 0 5000),
    (parent - ·) <$> Gen.nat (.linear 0 5000)])
  let limit := gasLimitToward parent target
  let delta := parent / 1024
  -- EIP-1559: the limit differs from the parent's by less than a 1024th of it.
  ensure (limit == parent || ((limit : Int) - parent).natAbs < delta) "the limit is out of bounds"
  ensure (((limit : Int) - target).natAbs ≤ ((parent : Int) - target).natAbs) "the limit moved away"
  -- No valid limit is closer to the target.
  ensure (limit == target ||
    (¬ ((limit + 1 : Int) - parent).natAbs < delta ∨ target < limit) ∧
    (¬ ((limit : Int) - 1 - parent).natAbs < delta ∨ limit < target)) "a closer limit is valid"

/-! ## The byte reader, as a state machine -/

/-- The model of a reader: the whole input and how far it was read. -/
structure ReaderModel where
  data : List UInt8
  /-- The position before the last read. -/
  before : Nat
  pos : Nat
  deriving Repr

/-- What a reader can be asked.  The set is fixed, so it is one type. -/
inductive Read where
  | bytes (n : Nat)
  | uint (n : Nat)
  | require (holds : Bool)
  deriving Repr, BEq

/-- The width a read consumes. -/
def Read.width : Read → Nat
  | .bytes n | .uint n => n
  | .require _ => 0

/-- Whether the read succeeds from a position of the model. -/
def ReaderModel.accepts (s : ReaderModel) : Read → Bool
  | .require holds => holds
  | t => s.before + t.width ≤ s.data.length

/-- A read moves the position when the bytes are there, and otherwise changes nothing. -/
def readerModel : Model ReaderModel Read where
  initState := (fun data => ⟨data, 0, 0⟩) <$> genByteList (.linear 0 40)
  transitions s :=
    let left := s.data.length - s.pos
    -- Widths up to the bytes left, exactly the bytes left, and one past them.
    let width :=
      Gen.frequency [(6, Gen.nat (.constant 0 left)), (1, pure left), (2, pure (left + 1))]
    Gen.frequency
      [(4, Read.bytes <$> width), (4, Read.uint <$> width), (1, Read.require <$> Gen.bool)]
  apply s t :=
    let s := { s with before := s.pos }
    if s.accepts t then { s with pos := s.pos + t.width } else s

/-- The reader on what is left of the input, against the model. -/
def readerMachine : StateMachine ReaderModel Read (List UInt8) IO where
  toModel := readerModel
  initSut s := pure s.data
  applySut input _ s t := do
    let field := (s.data.drop s.before).take t.width
    let run {α : Type} [BEq α] [Repr α] (reader : ByteReader.Reader Unit α) (want : α) :
        TestT IO (List UInt8) :=
      match reader input with
      | .ok (got, rest) => do
        ensure (s.accepts t) "the reader read past the end, or past a failed requirement"
        got === want
        pure rest
      | .error () => do
        ensure (!s.accepts t) "the reader refused a field that is there"
        pure input
    match t with
    | .bytes n => run (ByteReader.bytes () n) field
    | .uint n => run (ByteReader.uint () n) (bytesToNat field)
    | .require holds => run (ByteReader.require (holds = true) ()) ()
  invariants input s := input === s.data.drop s.pos

/-! ## A stream of values, as commands -/

/-- A value written to the stream, as it must read back. -/
inductive Item where
  | be (len n : Nat)
  | le (len n : Nat)
  | hex (bytes : List UInt8)
  | base64 (bytes : List UInt8)
  deriving Repr, BEq

/-- The stream written so far and not yet read, and the values it holds in order. -/
structure Stream where
  bytes : List UInt8 := []
  pending : List Item := []
  deriving Repr, Inhabited

/-- Text as the bytes of the stream, behind its length in one byte. -/
def framed (text : String) : List UInt8 :=
  UInt8.ofNat text.utf8ByteSize :: text.toUTF8.toList

/-- Write a big-endian number. -/
structure PutBE where
  len : Nat
  n : Nat

instance : Command PutBE Stream Unit IO where
  apply _ c s :=
    pure { bytes := s.bytes ++ natToBytes c.len c.n, pending := s.pending ++ [.be c.len c.n] }
  label c := s!"PUT_BE({c.len}, {c.n})"
  build _ := do
    let len ← Gen.nat (.constant 0 33)
    PutBE.mk len <$> genNatBits (8 * len)

/-- Write a little-endian number. -/
structure PutLE where
  len : Nat
  n : Nat

instance : Command PutLE Stream Unit IO where
  apply _ c s := pure { bytes := s.bytes ++ (uintToBytes c.len c.n).toList,
                        pending := s.pending ++ [.le c.len c.n] }
  label c := s!"PUT_LE({c.len}, {c.n})"
  build _ := do
    let len ← Gen.nat (.constant 0 33)
    PutLE.mk len <$> genNatBits (8 * len)

/-- Write bytes as hexadecimal text. -/
structure PutHex where
  bytes : List UInt8

instance : Command PutHex Stream Unit IO where
  apply _ c s := pure { bytes := s.bytes ++ framed (hexString c.bytes),
                        pending := s.pending ++ [.hex c.bytes] }
  label c := s!"PUT_HEX({hexString c.bytes})"
  build _ := PutHex.mk <$> genByteList (.linear 0 40)

/-- Write bytes as base64 text. -/
structure PutBase64 where
  bytes : List UInt8

instance : Command PutBase64 Stream Unit IO where
  apply _ c s := pure { bytes := s.bytes ++ framed (Base64.encode ⟨c.bytes.toArray⟩),
                        pending := s.pending ++ [.base64 c.bytes] }
  label c := s!"PUT_BASE64({hexString c.bytes})"
  build _ := PutBase64.mk <$> genByteList (.linear 0 40)

/-- Read the oldest value back, with the reader of its kind. -/
structure Take where

/-- Read a text behind its length. -/
def takeText : ByteReader.Reader Unit String := do
  let len ← ByteReader.uint () 1
  let bytes ← ByteReader.bytes () len
  match String.fromUTF8? ⟨bytes.toArray⟩ with
  | some text => pure text
  | none => throw ()

instance : Command Take Stream Unit IO where
  check _ _ s := !s.pending.isEmpty
  apply _ _ s := do
    let item :: pending := s.pending | failWith "nothing to read"
    let finish {α : Type} (reader : ByteReader.Reader Unit α) (holds : α → TestT IO Unit) :
        TestT IO Stream :=
      match reader s.bytes with
      | .ok (got, rest) => do holds got; pure { bytes := rest, pending }
      | .error () => failWith "the stream is short"
    match item with
    | .be len n => finish (ByteReader.uint () len) (· === n)
    | .le len n => finish (ByteReader.bytes () len) fun field =>
        if h : field.length = len then
          bytesToUint (⟨field.toArray, by simpa using h⟩ : Vector UInt8 len) === n
        else failWith "the field has another length"
    | .hex bytes => finish takeText fun text =>
        (hexBytes? (text.toList.drop 2)).map (·.toList) === some bytes
    | .base64 bytes => finish takeText fun text =>
        match Base64.decode text with
        | .ok got => got.toList === bytes
        | .error e => failWith s!"base64 refused its own text: {repr e}"
  label _ := "TAKE"
  build _ := pure {}

/-- A check that nothing is left behind: every value was read and the stream is empty. -/
structure Drain where

instance : Command Drain Stream Unit IO where
  check _ _ s := s.pending.isEmpty
  apply _ _ s := do s.bytes === []; pure s
  label _ := "DRAIN"
  build _ := pure {}

/-- Values written in any order read back in that order, each where the last one ended. -/
def stream (mode : Mode) : Property IO :=
  scenario mode () [Command.gen PutBE, Command.gen PutLE, Command.gen PutHex,
    Command.gen PutBase64, Command.gen Take, Command.gen Take, Command.gen Drain]

end BaseProperty

open BaseProperty in
def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "base"
  let ok ← checkGroup "base" [
    ("base64 encodes as RFC 4648", (base64Encode oracle).withTests cases),
    ("base64 decodes the canonical texts only", (base64Decode oracle).withTests cases),
    ("NFKD is the host's", (nfkd oracle).withTests cases),
    ("the integer square root", (squareRoot oracle).withTests cases),
    ("checked 64-bit arithmetic", checked.withTests cases),
    ("two's complement of a word", signed.withTests cases),
    ("big-endian and little-endian bytes", endian.withTests cases),
    ("hexadecimal reads back", hexRoundTrip.withTests cases),
    ("the gas limit toward a target", gasLimit.withTests cases),
    ("state machine: the byte reader against its model", readerMachine.property.withTests cases),
    ("commands in order: a stream of values reads back", stream .deterministic),
    ("commands in madhouse: a stream of values reads back", (stream .madhouse).withTests cases)]
    (← Selection.fromEnv)
  pure (if ok then 0 else 1)

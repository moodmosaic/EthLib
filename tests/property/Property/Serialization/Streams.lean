import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Classes
import EthLib.Serialization.E2store

/-!
# Streams of records, as state machines

- `StateMachine`: RLP items written to one buffer and read back in order by `decodeItem`.
- `Command`: an e2store file that grows by records, read by `decode`, in madhouse mode.
-/

open Hedgehog Support EthLib EthLib.Serialization

namespace SerializationProperty

/-! ## An RLP stream: `StateMachine` -/

/-- A step of a writer and a reader of one buffer. -/
inductive StreamStep where
  | write (item : Rlp.Item)
  | read
  /-- Read the whole buffer as the payload of one list. -/
  | readAsList
  /-- Read at the reader's position with the last byte of the buffer cut off. -/
  | readShort

/-- A step, as a report shows it. -/
def StreamStep.text : StreamStep → String
  | .write item => s!"write {itemText item}"
  | .read => "read"
  | .readAsList => "readAsList"
  | .readShort => "readShort"

instance : Repr StreamStep := ⟨fun step _ => step.text⟩

/-- The model of a stream: the items written, and how many of them were read. -/
structure StreamModel where
  written : Array Rlp.Item
  read : Nat

instance : Repr StreamModel := ⟨fun s _ => s!"{s.written.toList.map itemText} read {s.read}"⟩

/-- The model: a queue of items. -/
def streamModel : Model StreamModel StreamStep where
  initState := pure ⟨#[], 0⟩
  transitions _ := Gen.frequency [
    (4, .write <$> genItem), (4, pure .read), (1, pure .readAsList), (1, pure .readShort)]
  apply s
    | .write item => { s with written := s.written.push item }
    | .read => { s with read := s.read + 1 }
    | .readAsList | .readShort => s
  preconditions s
    | .read | .readShort => s.read < s.written.size
    | _ => true

/-- The buffer and the position of its reader. -/
structure Stream where
  buffer : ByteArray
  position : Nat

/-- The stream against the queue of its items.

A read gives the next item written and moves the reader by exactly its encoding.

The buffer under a list prefix decodes to the list of every item written.

A read of the last item from a buffer one byte short is refused. -/
def streamMachine : StateMachine StreamModel StreamStep Stream IO where
  toModel := streamModel
  initSut _ := pure ⟨.empty, 0⟩
  applySut sut _ s step := do
    match step with
    | .write item =>
      label "step: write"
      classifyAny "wrote" itemUniverse [(itemClasses item).1.headD ""]
      match Rlp.encode item with
      | .ok bytes => pure { sut with buffer := sut.buffer ++ bytes }
      | .error e => failWith s!"no encoding: {repr e}"
    | .read =>
      label "step: read"
      classify "read: not at the start of the buffer" (sut.position > 0)
      classify "read: the last item written" (s.read == s.written.size)
      match Rlp.decodeItem sut.buffer sut.position sut.buffer.size (Nat.le_refl _) with
      | .ok (item, next) =>
        let expected := s.written[s.read - 1]?
        ensure (expected == some item) s!"read {itemText item}"
        let size := (expected.bind fun e => (Rlp.encode e).toOption).map (·.size)
        some (next.val - sut.position) === size
        pure { sut with position := next.val }
      | .error e => failWith s!"the read was refused: {repr e}"
    | .readAsList =>
      label "step: read as a list"
      classifyAny "read as a list, a payload of" lengthClasses [lengthClass sut.buffer.size]
      match Rlp.lengthPrefix .list sut.buffer.size with
      | .ok front =>
        ensure (Rlp.decode (front ++ sut.buffer) == .ok (.list s.written.toList))
          "the buffer under a list prefix is not the list of the items"
        pure sut
      | .error e => failWith s!"no prefix: {repr e}"
    | .readShort =>
      -- Only the last item ends at the end of the buffer, so only its read must fail.
      let stop := sut.buffer.size - 1
      let result := Rlp.decodeItem sut.buffer sut.position stop (Nat.sub_le _ _)
      label "step: read short"
      classify "read short: of the last item, refused" (s.read + 1 == s.written.size)
      classify "read short: of an item inside, read" (s.read + 1 != s.written.size)
      if s.read + 1 == s.written.size then
        ensure result.toOption.isNone "a read past the end of the input was accepted"
      else
        ensure (result.toOption.map (·.1) == s.written[s.read]?) "a read inside the input differs"
      pure sut
  invariants sut s := do
    ensure (sut.position ≤ sut.buffer.size) "the reader is past the buffer"
    if s.read == s.written.size then sut.position === sut.buffer.size

/-! ## An e2store file: `Command`, in madhouse mode -/

/-- A file under test, and the records it should hold. -/
structure FileState where
  bytes : ByteArray := .empty
  records : Array (UInt16 × ByteArray) := #[]

instance : Inhabited FileState := ⟨{}⟩

/-- The records of a file as the oracle writes them. -/
def recordsText (records : List (UInt16 × ByteArray)) : String :=
  let texts := records.map fun (type, data) =>
    hex ⟨#[UInt8.ofNat (type.toNat / 256), UInt8.ofNat type.toNat]⟩ ++ ":" ++ hex data
  if texts.isEmpty then "-" else " ".intercalate texts

/-- The outcome of a decoding as the oracle writes it. -/
def decodedText (result : Except E2store.E2storeError (List E2store.Record)) : String :=
  match result with
  | .ok records => recordsText (records.map fun r => (r.type, r.data))
  | .error _ => "error"

/-- The file with one more record. -/
def appendRecord (s : FileState) (type : UInt16) (data : ByteArray) : TestT IO FileState := do
  classifyAny "appended a record of" ["no byte", "1 to 255 bytes", "256 bytes or more"]
    [if data.size == 0 then "no byte" else if data.size < 256 then "1 to 255 bytes"
      else "256 bytes or more"]
  classify "appended: a Version record" (type == E2store.VERSION)
  classify "appended: a Version record with data" (type == E2store.VERSION && data.size != 0)
  classify "appended: a type with a high second byte" (type.toNat % 256 ≥ 128)
  match E2store.encode [⟨type, data⟩] with
  | .ok bytes => pure { bytes := s.bytes ++ bytes, records := s.records.push (type, data) }
  | .error e => failWith s!"the record has no encoding: {repr e}"

/-- Append a Version record. -/
structure AppendVersion where

instance : Command AppendVersion FileState Oracle IO where
  apply _ _ s := appendRecord s E2store.VERSION .empty
  label _ := "VERSION"
  build _ := pure {}
  next _ _ s := { s with records := s.records.push (E2store.VERSION, .empty) }

/-- Append a record of some type, now and then a Version record that holds data. -/
structure AppendRecord where
  type : UInt16
  data : ByteArray

instance : Command AppendRecord FileState Oracle IO where
  apply _ c s := appendRecord s c.type c.data
  label c := s!"RECORD({c.type}, {hex c.data})"
  build _ := Gen.zipWith AppendRecord.mk
    (Gen.frequency [(3, Gen.element [0x0100, 0x0300, 0x6932, 0x0000, 0xffff, 0x3265]),
      (1, pure E2store.VERSION), (1, UInt16.ofNat <$> Gen.nat (.constant 0 65535))])
    (Gen.frequency [(3, genBytes (.linear 0 12)), (1, genBytes (.constant 255 257))])
  next _ c s := { s with records := s.records.push (c.type, c.data) }

/-- Eight little-endian bytes of an integer in two's complement. -/
def int64Bytes (n : Int) : List UInt8 :=
  let word := (n % 2 ^ 64).toNat
  (List.range 8).map fun i => UInt8.ofNat (word / 256 ^ i)

/-- Append an index record, and read its data back as an index. -/
structure AppendIndex where
  start : Nat
  offsets : List Int

/-- The data of an index record: the start, the offsets, their count. -/
def AppendIndex.data (c : AppendIndex) : ByteArray :=
  ⟨(int64Bytes c.start ++ c.offsets.flatMap int64Bytes ++ int64Bytes c.offsets.length).toArray⟩

instance : Command AppendIndex FileState Oracle IO where
  apply _ c s := do
    label "ran: INDEX"
    classify "INDEX: no entry" c.offsets.isEmpty
    classify "INDEX: a negative offset" (c.offsets.any (· < 0))
    classify "INDEX: a start of 2^63 or more" (c.start ≥ 2 ^ 63)
    let data := c.data
    E2store.readIndex data === .ok ⟨c.start, c.offsets⟩
    -- An index a byte short, a byte long, or with another count is no index.
    ensure (E2store.readIndex (data.extract 0 (data.size - 1))).toOption.isNone "a short index"
    ensure (E2store.readIndex (data.push 0)).toOption.isNone "a long index"
    ensure (E2store.readIndex (data.set! (data.size - 8) (UInt8.ofNat (c.offsets.length + 1)))
      ).toOption.isNone "an index with the wrong count"
    appendRecord s 0x6932 data
  label c := s!"INDEX({c.start}, {c.offsets})"
  build _ := Gen.zipWith AppendIndex.mk (genNatBits 64)
    (Gen.list (.linear 0 4) (Gen.frequency [
      (2, Gen.int (.linearFrom 0 (-1000) 1000)),
      (1, Gen.element [-(2 : Int) ^ 63, 2 ^ 63 - 1, -1, 0])]))
  next _ c s := { s with records := s.records.push (0x6932, c.data) }

/-- Where each record of the model starts in the file, and the end of the file. -/
def boundaries (records : List (UInt16 × ByteArray)) : List Nat :=
  records.foldl (fun starts (_, data) => starts ++ [starts.getLastD 0 + 8 + data.size]) [0]

/-- The verdict of the reader of a file, by the constructor of its error. -/
def fileVerdict {α : Type} : Except E2store.E2storeError α → String
  | .ok _ => "read"
  | .error (.truncatedHeader ..) => "truncated header"
  | .error (.truncatedData ..) => "truncated data"
  | .error (.reservedNotZero ..) => "reserved not zero"
  | .error (.dataTooLong _) => "data too long"
  | .error (.noVersion _) => "no version"
  | .error (.versionData _) => "version with data"
  | .error (.indexSize _) => "index size"

/-- Decode the file and compare it with the model and with the reference. -/
structure CheckFile where

instance : Command CheckFile FileState Oracle IO where
  apply oracle _ s := do
    let records := s.records.toList
    label "ran: CHECK"
    classifyAny "CHECK, records" ["0", "1", "2 or more"] [countClass 2 records.length]
    classifyAny "CHECK, as a file" ["read", "no version", "version with data"]
      [fileVerdict (E2store.decodeFile s.bytes)]
    decodedText (E2store.decode s.bytes) === recordsText records
    decodedText (E2store.decode s.bytes) === (← oracle.ask ["e2s", hex s.bytes])
    -- All records at once are the records one by one.
    (E2store.encode (records.map fun (type, data) => ⟨type, data⟩)).toOption.map hex ===
      some (hex s.bytes)
    -- A header at the start of each record names its type and its length.
    let starts := E2store.recordStarts 0 (records.map fun (type, data) => ⟨type, data⟩)
    starts === (boundaries records).dropLast
    for (start, (type, data)) in starts.zip records do
      E2store.readHeader s.bytes start === .ok ⟨type, data.size⟩
    -- A file starts with a Version record, and no Version record holds data.
    let first := records.head?.map (·.1)
    let bad := records.findIdx? fun (type, data) => type == E2store.VERSION && data.size != 0
    let expected : Except E2store.E2storeError Unit :=
      if first != some E2store.VERSION then .error (.noVersion first)
      else match bad with
        | some index => .error (.versionData index)
        | none => .ok ()
    (E2store.decodeFile s.bytes).map (fun _ => ()) === expected
    pure s
  label _ := "CHECK"
  build _ := pure {}

/-- Cut the file short: it decodes only where the cut falls between two records. -/
structure CutFile where
  cut : Nat

instance : Command CutFile FileState Oracle IO where
  check _ c s := c.cut ≤ s.bytes.size
  apply oracle c s := do
    let kept := s.bytes.extract 0 (s.bytes.size - c.cut)
    let result := E2store.decode kept
    annotate s!"the file of {s.bytes.size} bytes cut to {kept.size}"
    label "ran: CUT"
    classifyAny "CUT" ["read", "truncated header", "truncated data"] [fileVerdict result]
    result.toOption.isSome === (boundaries s.records.toList).contains kept.size
    decodedText result === (← oracle.ask ["e2s", hex kept])
    -- The cut copy was refused or read; the file itself is as it was.
    pure s
  label c := s!"CUT({c.cut})"
  build _ := CutFile.mk <$> Gen.frequency [(3, Gen.nat (.constant 1 8)),
    (1, Gen.nat (.linear 1 40))]
  -- For the file that the commands before lead to: a cut between two records, or inside one.
  buildIn _ s :=
    let ends := boundaries s.records.toList
    let total := ends.getLastD 0
    CutFile.mk <$> Gen.frequency [(2, (total - ·) <$> Gen.element ends),
      (2, Gen.nat (.constant 1 8)), (1, Gen.nat (.linear 1 40))]

/-- Set a reserved byte of the header of one record: the copy is refused. -/
structure SetReserved where
  record : Nat
  second : Bool
  byte : UInt8

instance : Command SetReserved FileState Oracle IO where
  check _ c s := c.record < s.records.size
  apply _ c s := do
    label "ran: SET_RESERVED"
    classify "SET_RESERVED: not in the first record" (c.record > 0)
    let start := (boundaries s.records.toList).getD c.record 0
    let spot := start + (if c.second then 7 else 6)
    let bad := s.bytes.set! spot c.byte
    let reserved := if c.second then (0, c.byte) else (c.byte, 0)
    (E2store.decode bad).map (fun _ => ()) === .error (.reservedNotZero reserved.1 reserved.2)
    pure s
  label c := s!"SET_RESERVED({c.record}, {c.second}, {c.byte})"
  build _ := do
    let record ← Gen.nat (.linear 0 6)
    let second ← Gen.bool
    let byte ← Gen.frequency [(1, Gen.element [1, 0x80, 0xff]),
      (1, Gen.integral (.constant 1 255))]
    pure ⟨record, second, byte⟩
  -- For the file that the commands before lead to: one of its records, if it has any.
  buildIn _ s := do
    let record ← Gen.nat (.constant 0 (s.records.size - 1))
    let second ← Gen.bool
    let byte ← Gen.frequency [(1, Gen.element [1, 0x80, 0xff]),
      (1, Gen.integral (.constant 1 255))]
    pure ⟨record, second, byte⟩

/-- Random appends to a file, with refused copies between them, in madhouse mode. -/
def fileScenario (oracle : Oracle) : Property IO :=
  scenario .madhouse oracle [
    Command.gen AppendVersion, Command.gen AppendRecord, Command.gen AppendRecord,
    Command.gen AppendIndex, Command.gen CheckFile, Command.gen CheckFile, Command.gen CutFile,
    Command.gen SetReserved] (.linear 1 30)

/-- The same commands in the order of a file that a writer makes, once. -/
def fileScript (oracle : Oracle) : Property IO :=
  scenario .deterministic oracle [
    Command.gen AppendVersion, Command.gen AppendRecord, Command.gen AppendIndex,
    Command.gen CheckFile, Command.gen CutFile, Command.gen SetReserved, Command.gen CheckFile]

end SerializationProperty

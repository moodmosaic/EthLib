import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Networking.Encoding.Protobuf
import EthLib.Networking.Gossip.Rpc

/-!
# The protobuf wire reader and the gossipsub RPC, on generated inputs

The reader of records is compared with a reader written from the encoding guide.

It is also compared with the unknown fields that the `protobuf` package keeps of the same bytes.

The RPC is compared with a model of the libp2p schema that makes EthLib's documented choices.

Where no such choice applies, it is compared with the `protobuf` package under that schema.
-/

open Hedgehog Support EthLib
open EthLib.Networking.Encoding.Protobuf
open EthLib.Networking.Gossip

namespace DecodersProperty.Protobuf

open DecodersProperty

/-! ## The text that both sides write -/

/-- Bytes in hexadecimal, with nothing for none. -/
def rawHex (bytes : ByteArray) : String :=
  if bytes.isEmpty then "" else hex bytes

/-- A record as the oracle writes one. -/
def showRecord (r : Record) : String :=
  match r.value with
  | .varint v => s!"{r.field}:0:{v.toNat}"
  | .i64 b => s!"{r.field}:1:{hexv b}"
  | .len b => s!"{r.field}:2:{rawHex b}"
  | .group => s!"{r.field}:3:"
  | .i32 b => s!"{r.field}:5:{hexv b}"

/-- The records of a message, or the rule that refused it. -/
def showRecords (result : Except ProtobufError (List Record)) : String :=
  match result with
  | .ok [] => "-"
  | .ok rs => ",".intercalate (rs.map showRecord)
  | .error (.varint _) => "error:varint"
  | .error (.fieldNumber _) => "error:field-number"
  | .error (.wireType _) => "error:wire-type"
  | .error (.truncated ..) => "error:truncated"
  | .error (.groupEnd _) => "error:group-end"

/-- Bytes behind a mark, so that no bytes differ from no value. -/
def x (bytes : ByteArray) : String := "x" ++ rawHex bytes

/-- A flag. -/
def bit (flag : Bool) : String := if flag then "1" else "0"

/-- A list of items between brackets. -/
def bracket (items : List String) : String := "[" ++ ",".intercalate items ++ "]"

/-- A list of message IDs. -/
def ids (values : List ByteArray) : String := bracket (values.map x)

/-- An RPC as the oracle writes one. -/
def showRpc (rpc : Rpc) : String :=
  let sub (s : SubOpts) :=
    s!"({bit s.subscribe},{x s.topicId.toUTF8},{bit s.requestsPartial}," ++
      s!"{bit s.supportsSendingPartial})"
  let prune (p : Prune) :=
    let peers := p.peers.map fun q => s!"({x q.peerId},{x q.signedPeerRecord})"
    s!"({x p.topicId.toUTF8},{bracket peers},{p.backoff.toNat})"
  let c := rpc.control
  let extensions := match c.extensions with
    | none => "-"
    | some e => bit e.partialMessages
  let option : Option ByteArray → String
    | none => "~"
    | some b => x b
  let part := match rpc.partialMessage with
    | none => "-"
    | some p => s!"({x p.topicId},{x p.groupId},{option p.partialMessage}," ++
        s!"{option p.partsMetadata})"
  bracket (rpc.subscriptions.map sub) ++
    bracket (rpc.publish.map fun m => s!"({x m.data},{x m.topic.toUTF8})") ++ "{" ++
    bracket (c.ihave.map fun h => s!"({x h.topicId.toUTF8},{ids h.messageIds})") ++
    bracket (c.iwant.map (ids ·.messageIds)) ++ bracket (c.graft.map (x ·.topicId.toUTF8)) ++
    bracket (c.prune.map prune) ++ bracket (c.idontwant.map (ids ·.messageIds)) ++
    extensions ++ "}" ++ part

/-- A decoded RPC, or `error`. -/
def showDecoded (result : Except RpcError Rpc) : String :=
  match result with
  | .ok rpc => showRpc rpc
  | .error _ => "error"

/-! ## Bytes of the wire format, valid and nearly valid -/

/-- The rules that a generated input may break; with none of them it is valid. -/
structure Twist where
  /-- Varints are padded, to ten bytes and to eleven. -/
  varints : Bool := false
  /-- A length says more or fewer bytes than follow it. -/
  lengths : Bool := false
  /-- Field numbers are 0 or past `2^29 - 1`, and wire types are 4, 6 and 7. -/
  keys : Bool := false
  /-- A group ends with another number, or does not end. -/
  groups : Bool := false
  /-- A singular field is missing or comes twice, and fields are out of order. -/
  counts : Bool := false
  /-- A message holds fields outside its schema, or named ones with another wire type. -/
  extras : Bool := false
  /-- A flag is above one, a number is past 64 bits, a string is not UTF-8. -/
  values : Bool := false
  deriving Repr, BEq

/-- Some rules to break: mostly one, so that a case is not refused for another rule first. -/
def genTwist : Gen Twist :=
  let flag := Gen.frequency [(2, pure false), (1, pure true)]
  Gen.frequency [
    (3, Gen.element [{ varints := true }, { lengths := true }, { keys := true },
      { groups := true }, { counts := true }, { extras := true }, { values := true },
      { extras := true, groups := true }, { counts := true, extras := true }]),
    (1, do pure { varints := ← flag, lengths := ← flag, keys := ← flag, groups := ← flag,
                  counts := ← flag, extras := ← flag, values := ← flag })]

/-- A rule of the wire format to break, or several. -/
def genWireTwist : Gen Twist :=
  let flag := Gen.bool
  Gen.frequency [
    (4, Gen.element [{ varints := true }, { lengths := true }, { keys := true },
      { groups := true }, { values := true }]),
    (1, do pure { varints := ← flag, lengths := ← flag, keys := ← flag, groups := ← flag,
                  values := ← flag })]

/-- The groups of seven bits of a number, least significant first. -/
def groupsOf (n : Nat) : List Nat :=
  if n < 128 then [n] else n % 128 :: groupsOf (n / 128)
termination_by n
decreasing_by omega

/-- A varint with `pad` zero groups after those its value needs. -/
def varintBytes (n pad : Nat) : List UInt8 :=
  let groups := groupsOf n ++ List.replicate pad 0
  groups.mapIdx fun i g => UInt8.ofNat (g + if i + 1 < groups.length then 128 else 0)

/-- A varint of a value: the shortest, or at times padded, to ten bytes or to eleven. -/
def genVarint (t : Twist) (n : Nat) : Gen (List UInt8) :=
  if !t.varints then pure (varintBytes n 0)
  else
    let length := (groupsOf n).length
    (varintBytes n ·) <$> Gen.frequency [(60, pure 0), (4, Gen.nat (.constant 1 3)),
      (2, pure (10 - length)), (1, pure (11 - length))]

/-- The value of a varint field: any 64-bit one, or at times a larger one. -/
def genVarintValue (t : Twist) : Gen Nat :=
  if !t.values then genNatBits 64
  else Gen.frequency [(6, genNatBits 64), (1, (2 ^ 64 + ·) <$> genNatBits 6),
    (1, genNatBits 70)]

/-- A field number: mostly small, at the edges of the key lengths, or outside the range. -/
def genFieldNumber (t : Twist) : Gen Nat :=
  Gen.frequency ([(10, Gen.nat (.constant 1 15)), (3, Gen.nat (.constant 16 2047)),
    (2, Gen.element [2047, 2048, 262143, 262144, 33554431, 33554432, 2 ^ 29 - 1]),
    (1, Gen.nat (.constant 1 (2 ^ 29 - 1)))] ++
    if !t.keys then [] else [
      (2, Gen.element [0, 2 ^ 29, 2 ^ 29, 2 ^ 29 + 1, 2 ^ 32, 2 ^ 61 - 1, 2 ^ 61, 2 ^ 66]),
      (2, Gen.nat (.constant (2 ^ 29) (2 ^ 61 - 1)))])

/-- The key of a field and a wire type. -/
def genKey (t : Twist) (field wire : Nat) : Gen (List UInt8) :=
  genVarint t (field * 8 + wire)

/-- A length and the bytes behind it; the length is at times another. -/
def genLen (t : Twist) (bytes : List UInt8) : Gen (List UInt8) := do
  let declared ← if !t.lengths then pure bytes.length
    else Gen.frequency [(8, pure bytes.length), (1, (bytes.length + ·) <$> Gen.nat (.linear 1 3)),
      (1, pure (bytes.length - 1))]
  pure ((← genVarint t declared) ++ bytes)

/-- A record of any field and any wire type, with groups down to a depth. -/
def genRecordBytes (t : Twist) : Nat → Gen (List UInt8)
  | 0 => do
    let field ← genFieldNumber t
    let wire ← Gen.frequency ([(3, pure 0), (2, pure 1), (3, pure 2), (2, pure 5)] ++
      if !t.keys then [] else [(2, Gen.element [4, 6, 7])])
    let key ← genKey t field wire
    let value ← match wire with
      | 0 => do genVarint t (← genVarintValue t)
      | 1 => genByteList (.singleton 8)
      | 2 => do genLen t (← genByteList (.linear 0 6))
      | 5 => genByteList (.singleton 4)
      | _ => pure []
    pure (key ++ value)
  | depth + 1 => Gen.frequency [(5, genRecordBytes t 0), (2, do
    let field ← genFieldNumber t
    let start ← genKey t field 3
    let inner ← Gen.list (.linear 0 3) (genRecordBytes t depth)
    let last ← if !t.groups then genKey t field 4
      else Gen.frequency [(2, genKey t field 4), (1, genKey t (field + 1) 4), (1, pure [])]
    pure (start ++ inner.flatten ++ last))]

/-- Whether the input is as generated or changed in one place. -/
inductive Shape where
  | clean
  | twisted
  | mutated
  deriving Repr, BEq

/-- The bytes of a shape.

A clean input breaks no rule, a twisted one breaks the rules of a drawn `Twist`.

A mutated one is a clean input with one byte changed, dropped or added, or cut short. -/
def genShaped (twist : Gen Twist) (gen : Twist → Gen (List UInt8)) :
    Gen (Shape × List UInt8) := do
  let shape ← Gen.frequency [(4, pure Shape.clean), (5, pure .twisted), (2, pure .mutated)]
  match shape with
  | .clean => do pure (shape, ← gen {})
  | .twisted => do pure (shape, ← gen (← twist))
  | .mutated => do
    let bytes ← gen {}
    if bytes.isEmpty then pure (shape, bytes) else pure (shape, ← genMutation bytes)

/-- A shape and its bytes as text. -/
def showShaped (input : Shape × List UInt8) : String :=
  s!"{repr input.1} {hex (packed input.2)}"

/-- The answer of the oracle in its words: the model, the package, and the rest. -/
def answerWords (answer : String) : TestT IO (String × String × List String) :=
  match words answer with
  | model :: package :: rest => pure (model, package, rest)
  | _ => failWith s!"the oracle answered {answer}"

/-- Count the case under each thing that the reference saw in it. -/
def classifySeen (seen : String) (names : List String) : TestT IO Unit :=
  let found := seen.splitOn ","
  names.forM fun name => classify name (found.contains name)

/-- What the package reads in another way than the guide and EthLib's docstring say.

The package refuses a key or a length of more than five bytes, which the guide does not ask.

It drops the bits of a varint past the 64th, and EthLib refuses such a varint. -/
def wireDifferences : List String :=
  ["key-over-5-bytes", "length-over-5-bytes", "varint-past-64-bits", "varint-of-11-bytes"]

/-- Whether the reference saw one of the named things. -/
def sawAny (seen : String) (names : List String) : Bool :=
  (seen.splitOn ",").any names.contains

/-! ## The reader of records -/

/-- The reader gives the records of the guide's reader, or refuses by the same rule.

Where the package reads by the same rules, its unknown fields are the same records. -/
def recordsRead (oracle : Oracle) : Property IO := propertyM do
  let (shape, bytes) ← forAllWith showShaped
    (genShaped genWireTwist fun t =>
      List.flatten <$> Gen.list (.linear 0 6) (genRecordBytes t 2))
  pure do
    let (model, package, rest) ← answerWords (← oracle.ask ["pb_records", hex (packed bytes)])
    let seen := rest.headD "-"
    let got := showRecords (records bytes)
    cover 12 "valid as generated" (shape == .clean)
    cover 12 "changed and still accepted by the reference" (shape != .clean && !refused model)
    cover 5 "refused by the reference" (refused model)
    classifySeen seen (["group", "nested-group", "padded-varint", "field-0", "field-past-2^29-1",
      "length-past-the-input", "group-not-closed", "group-end-of-another-field",
      "group-end-alone", "wire-type-6-or-7"] ++ wireDifferences)
    -- A group that the input ends in is refused as a short varint or as truncated, by its depth.
    if sawAny seen ["group-not-closed"] then verdict got === "error" else got === model
    -- The package keeps `00 00` as field 0 of a message of no fields.
    if !sawAny seen ("field-0" :: wireDifferences) then
      if refused got then verdict package === "error" else got === package

/-- A record that the encoding can carry, with any value. -/
def genRecord : Gen Record := do
  let field ← genFieldNumber {}
  let value ← Gen.choice [Value.varint <$> genUInt64, Value.i64 <$> genVector 8,
    Value.len <$> genBytes (.linear 0 8), pure .group, Value.i32 <$> genVector 4]
  pure ⟨field, value⟩

/-- What the writer writes, the guide's reader and the package read as the same records.

EthLib reads them back too. -/
def recordsWritten (oracle : Oracle) : Property IO := propertyM do
  let rs ← forAllWith (fun rs => ",".intercalate (rs.map showRecord))
    (Gen.list (.linear 0 8) genRecord)
  pure do
    let bytes := serialize rs
    let want := showRecords (.ok rs)
    let (model, package, _) ← answerWords (← oracle.ask ["pb_records", hex bytes])
    classify "a group" (rs.any (·.value == .group))
    classify "a key of five bytes" (rs.any (2 ^ 25 ≤ ·.field))
    model === want
    package === want
    showRecords (records bytes.data.toList) === want

/-! ## The RPC -/

/-- The messages of the schema. -/
inductive Msg where
  | rpc | sub | message | control | ihave | iwant | graft | prune | peer | idontwant | ext | part
  deriving Repr, BEq

/-- The type of a field of the schema. -/
inductive Kind where
  | bool
  | uint
  | bytes
  | str
  | msg (m : Msg)

/-- The fields of a message: number, type, and whether it repeats.

This is the schema of the libp2p specifications, written out for the generator. -/
def fieldsOf : Msg → List (Nat × Kind × Bool)
  | .rpc => [(1, .msg .sub, true), (2, .msg .message, true), (3, .msg .control, false),
      (10, .msg .part, false)]
  | .sub => [(1, .bool, false), (2, .str, false), (3, .bool, false), (4, .bool, false)]
  | .message => [(2, .bytes, false), (4, .str, false)]
  | .control => [(1, .msg .ihave, true), (2, .msg .iwant, true), (3, .msg .graft, true),
      (4, .msg .prune, true), (5, .msg .idontwant, true), (6, .msg .ext, false)]
  | .ihave => [(1, .str, false), (2, .bytes, true)]
  | .iwant | .idontwant => [(1, .bytes, true)]
  | .graft => [(1, .str, false)]
  | .prune => [(1, .str, false), (2, .msg .peer, true), (3, .uint, false)]
  | .peer => [(1, .bytes, false), (2, .bytes, false)]
  | .ext => [(10, .bool, false)]
  | .part => [(1, .bytes, false), (2, .bytes, false), (3, .bytes, false), (4, .bytes, false)]

/-- A topic: a few names, so that the same one comes again, in one to three bytes a character. -/
def genTopic : Gen String :=
  Gen.element ["", "a", "blocks", "/eth2/b5303f2a/beacon_block/ssz_snappy", "é", "日本", "𝔸"]

/-- The bytes of a string field: a topic, or at times any bytes. -/
def genStringBytes (t : Twist) : Gen (List UInt8) :=
  if !t.values then (·.toUTF8.data.toList) <$> genTopic
  else Gen.frequency [(10, (·.toUTF8.data.toList) <$> genTopic), (1, genByteList (.linear 1 4)),
    (1, Gen.element [[0xc3], [0xe6, 0x97], [0xed, 0xa0, 0x80], [0xc0, 0x80],
      [0xf4, 0x90, 0x80, 0x80], [0x61, 0xff]])]

/-- How many times a field occurs. -/
def genCount (t : Twist) (repeats required : Bool) : Gen Nat :=
  if repeats then Gen.nat (.linear 0 2)
  else if !t.counts then (if required then pure 1 else Gen.frequency [(3, pure 1), (1, pure 0)])
  else Gen.frequency [(6, pure 1), (2, pure 0), (2, pure 2)]

/-- A field outside the schema of its message, or a named one that breaks a rule. -/
def genExtra (t : Twist) (m : Msg) : Gen (List UInt8) :=
  let named := (fieldsOf m).map (·.1)
  Gen.frequency ([
    -- A field that the schema does not name, of any wire type, a group included.
    (8, genRecordBytes t 2),
    -- The experimental fields of the extensions.
    (1, do pure ((← genKey t 6492434 2) ++ (← genLen t [8, 1]))),
    (1, do pure ((← genKey t 6492435 0) ++ [1])),
    -- A named field with another wire type.
    (2, do
      let field ← Gen.element named
      let wire ← Gen.element [0, 1, 2, 5]
      let value ← match wire with
        | 0 => pure [1]
        | 1 => genByteList (.singleton 8)
        | 2 => pure [1, 0x61]
        | _ => genByteList (.singleton 4)
      pure ((← genKey t field wire) ++ value)),
    (1, do
      let field ← Gen.element named
      pure ((← genKey t field 3) ++ (← genKey t field 4)))] ++
    -- The fields that StrictNoSign forbids, with their own wire type and with another.
    if m == .message then [(6, do
      let field ← Gen.element [1, 3, 5, 6]
      let wire ← Gen.frequency [(3, pure 2), (1, pure 0)]
      let value ← if wire = 2 then genLen t [] else pure [0]
      pure ((← genKey t field wire) ++ value))] else [])

/-- A message of the schema as bytes.

With no twist it holds the named fields in order, each with its own wire type.

Otherwise fields are missing, repeated, out of order, unknown, or malformed. -/
def genMessage (t : Twist) : Nat → Msg → Gen (List UInt8)
  | 0, _ => pure []
  | fuel + 1, m => do
    let fields ← (fieldsOf m).mapM fun (field, kind, repeats) => do
      let count ← genCount t repeats (m == .message && field == 4)
      let values ← (List.range count).mapM fun _ => do
        let value ← match kind with
          | .bool => do
            let flag ← if !t.values then Gen.nat (.constant 0 1)
              else Gen.frequency [(4, Gen.nat (.constant 0 1)), (1, genNatBits 64),
                (1, pure (2 ^ 64))]
            genVarint t flag
          | .uint => do genVarint t (← genVarintValue t)
          | .bytes => do genLen t (← genByteList (.linear 0 6))
          | .str => do genLen t (← genStringBytes t)
          | .msg inner => do genLen t (← genMessage t fuel inner)
        let wire := match kind with
          | .bool | .uint => 0
          | _ => 2
        pure ((← genKey t field wire) ++ value)
      pure values
    let fields := fields.flatten
    let extras ← if !t.extras then pure []
      else Gen.frequency [(2, pure []), (1, Gen.list (.constant 1 2) (genExtra t m))]
    let ordered ← if !t.counts then pure (fields ++ extras)
      else Gen.frequency [(3, pure (fields ++ extras)), (1, Gen.shuffle (fields ++ extras))]
    pure ordered.flatten

/-- The choices of EthLib that differ from the package, each named in the docstring of the module.

A named field with another wire type is rejected, where protobuf keeps it as unknown.

A singular message field keeps its last occurrence whole, where protobuf merges.

The four fields of a signed message are rejected, and a topic that is not UTF-8. -/
def rpcDifferences : List String :=
  ["named-field-with-another-wire-type", "extensions-twice", "partial-twice", "signed-field",
    "string-not-utf8"]

/-- A field with a key in its shortest form. -/
def fieldBytes (number wire : Nat) (value : List UInt8) : List UInt8 :=
  varintBytes (number * 8 + wire) 0 ++ value

/-- A length-delimited field. -/
def lenField (number : Nat) (bytes : List UInt8) : List UInt8 :=
  fieldBytes number 2 (varintBytes bytes.length 0 ++ bytes)

/-- An RPC that meets one of the rules that EthLib's docstring states, built field by field.

Each is a rule on which a general protobuf reader would answer otherwise. -/
def genRuleCase : Gen (List UInt8) := do
  let topic ← genStringBytes {}
  let bad : List UInt8 ← Gen.element [[0xc3], [0xff], [0xed, 0xa0, 0x80], [0xc0, 0x80],
    [0x61, 0x80], [0xf4, 0x90, 0x80, 0x80]]
  let data ← genByteList (.linear 0 4)
  let number ← Gen.element [1, 3, 5, 6]
  let wire ← Gen.element [0, 1, 2, 3, 5]
  let value ← match wire with
    | 0 => (varintBytes · 0) <$> genNatBits 64
    | 1 => genByteList (.singleton 8)
    | 2 => (fun bytes => varintBytes bytes.length 0 ++ bytes) <$> genByteList (.linear 0 3)
    | 3 => pure (varintBytes (number * 8 + 4) 0)
    | _ => genByteList (.singleton 4)
  let position ← Gen.nat (.constant 0 2)
  let message := [lenField 2 data, lenField 4 topic]
  let signed := (message.take position ++ [fieldBytes number wire value] ++
    message.drop position).flatten
  let publish (body : List UInt8) := lenField 2 body
  let control (body : List UInt8) := lenField 3 body
  let extensions (flag : Option UInt8) := lenField 6 (match flag with
    | some f => fieldBytes 10 0 [f]
    | none => [])
  let part (fields : List (List UInt8)) := lenField 10 fields.flatten
  let flag ← Gen.element [none, some 0, some 1]
  let other ← Gen.element [none, some 0, some 1]
  let named ← Gen.element [fieldBytes 1 0 [1], fieldBytes 1 5 [0, 0, 0, 0],
    lenField 1 (fieldBytes 2 0 [1]), lenField 1 (fieldBytes 1 2 [1, 1]),
    lenField 3 (lenField 4 (lenField 1 topic ++ lenField 3 [1])),
    lenField 3 (lenField 4 (lenField 2 (fieldBytes 1 0 [1]))),
    lenField 3 (lenField 6 (lenField 10 [1])), lenField 10 (fieldBytes 3 0 [1]),
    lenField 2 (lenField 4 topic ++ fieldBytes 2 0 [1])]
  Gen.element [
    -- A message with a field that StrictNoSign forbids, at any place and of any wire type.
    publish signed,
    publish signed ++ publish message.flatten,
    -- A message without a topic, and one with two.
    publish (lenField 2 data),
    publish (lenField 4 topic ++ lenField 4 topic ++ lenField 2 data),
    -- A string that is not UTF-8, in the last occurrence and in an earlier one.
    publish (lenField 4 topic ++ lenField 4 bad),
    publish (lenField 4 bad ++ lenField 4 topic),
    lenField 1 (fieldBytes 1 0 [1] ++ lenField 2 bad),
    control (lenField 1 (lenField 1 bad)),
    control (lenField 3 (lenField 1 bad)),
    control (lenField 4 (lenField 1 bad)),
    -- The bytes of a partial message need not be UTF-8.
    part [lenField 1 bad, lenField 2 bad],
    -- The extensions twice in one control field, and in two.
    control (extensions flag ++ extensions other),
    control (extensions flag) ++ control (extensions other),
    control (extensions flag) ++ control (lenField 3 (lenField 1 topic)),
    -- A partial message twice.
    part [lenField 1 data, lenField 3 data] ++ part [lenField 2 data],
    part [lenField 3 data, lenField 3 [], lenField 4 data, lenField 4 [7]],
    -- A named field with another wire type.
    named]

/-- An RPC decodes as the model of the schema with EthLib's documented choices.

Where none of those choices applies, it decodes as the `protobuf` package does. -/
def rpcDecodeOf (gen : Gen (Shape × List UInt8)) (oracle : Oracle) : Property IO := propertyM do
  let (shape, bytes) ← forAllWith showShaped gen
  pure do
    let (model, package, rest) ← answerWords (← oracle.ask ["rpc", hex (packed bytes)])
    let seen := rest.getD 1 "-"
    let got := showDecoded (decodeRpc (packed bytes))
    annotate s!"model {model}, package {package}, seen {seen}"
    classify "valid as generated" (shape == .clean)
    cover 10 "changed and still accepted by the reference" (shape != .clean && !refused model)
    cover 8 "refused by the reference" (refused model)
    cover 10 "compared with the package"
      (!sawAny seen ("field-0" :: rpcDifferences ++ wireDifferences))
    classifySeen seen (rpcDifferences ++ wireDifferences ++ ["singular-field-twice",
      "control-twice", "extensions-in-later", "message-without-topic", "bool-above-1",
      "unknown-field-of-wire-type-0", "unknown-field-of-wire-type-1",
      "unknown-field-of-wire-type-2", "unknown-field-of-wire-type-3",
      "unknown-field-of-wire-type-5", "group", "padded-varint", "length-past-the-input",
      "field-0", "field-past-2^29-1"])
    classify "an RPC with control messages" (got.any (· == '(') && !refused got)
    got === verdict model
    -- The package reads a key of field number 0 inside a group, and refuses it elsewhere.
    if !sawAny seen ("field-0" :: rpcDifferences ++ wireDifferences) then
      got === verdict package

/-- An RPC of generated fields, valid, with rules broken, or changed in one place. -/
def rpcDecode (oracle : Oracle) : Property IO :=
  rpcDecodeOf (genShaped genTwist fun t => genMessage t 5 .rpc) oracle

/-- An RPC that meets one documented rule: the signed fields, the topic, UTF-8, the last one. -/
def rpcRules (oracle : Oracle) : Property IO :=
  rpcDecodeOf ((Shape.twisted, ·) <$> genRuleCase) oracle

/-- A message ID or other short bytes. -/
def genId : Gen ByteArray := genBytes (.linear 0 6)

/-- An RPC with every part, each list short. -/
def genRpc : Gen Rpc := do
  let few {α : Type} (gen : Gen α) : Gen (List α) := Gen.list (.linear 0 3) gen
  let subscriptions ← few do
    pure { subscribe := ← Gen.bool, topicId := ← genTopic, requestsPartial := ← Gen.bool,
           supportsSendingPartial := ← Gen.bool : SubOpts }
  let publish ← few do pure { data := ← genBytes (.linear 0 12), topic := ← genTopic : Message }
  let ihave ← few do pure { topicId := ← genTopic, messageIds := ← few genId : IHave }
  let iwant ← few do pure { messageIds := ← few genId : IWant }
  let graft ← few do pure { topicId := ← genTopic : Graft }
  let prune ← few do
    let peers ← few do pure { peerId := ← genId, signedPeerRecord := ← genId : PeerInfo }
    pure { topicId := ← genTopic, peers, backoff := ← genUInt64 : Prune }
  let idontwant ← few do pure { messageIds := ← few genId : IDontWant }
  let extensions ← Gen.option do pure { partialMessages := ← Gen.bool : ControlExtensions }
  let partialMessage ← Gen.option do
    pure { topicId := ← genId, groupId := ← genId, partialMessage := ← Gen.option genId,
           partsMetadata := ← Gen.option genId : PartialMessagesExtension }
  let control ← Gen.frequency [(1, pure {}),
    (4, pure { ihave, iwant, graft, prune, idontwant, extensions })]
  pure { subscriptions, publish, control, partialMessage }

/-- The package reads what EthLib writes, and writes the same bytes for it.

EthLib reads its own bytes back to the RPC. -/
def rpcEncode (oracle : Oracle) : Property IO := propertyM do
  let rpc ← forAllWith showRpc genRpc
  pure do
    let bytes := rpc.encode
    let (model, package, rest) ← answerWords (← oracle.ask ["rpc", hex bytes])
    classify "no control field" (rpc.control == {})
    classify "extensions" rpc.control.extensions.isSome
    classify "a partial message" rpc.partialMessage.isSome
    classify "a prune with peers" (rpc.control.prune.any (!·.peers.isEmpty))
    model === showRpc rpc
    package === showRpc rpc
    rest.headD "-" === hex bytes
    showDecoded (decodeRpc bytes) === showRpc rpc

/-- The flags of a subscription count only when it subscribes, as the partial messages text says.

A sender that asks for partial messages can send them. -/
def partialFlags : Property IO := pureIO do
  let subscribe ← forAll Gen.bool
  let requests ← forAll Gen.bool
  let supports ← forAll Gen.bool
  let s : SubOpts := { subscribe, requestsPartial := requests, supportsSendingPartial := supports }
  s.asksPartial === (subscribe && requests)
  s.sendsPartial === (subscribe && (supports || requests))

/-- The extensions message is in the first RPC of a stream or in none, as gossipsub v1.3 says.

"MUST be included in the first message on the stream", and "MUST NOT be sent more than once". -/
def extensionsOrder : Property IO := pureIO do
  let flags ← forAll (Gen.list (.constant 0 5) Gen.bool)
  let rpcs := flags.map fun flag =>
    ({ control := { extensions := if flag then some {} else none } } : Rpc)
  -- The places of the RPCs that carry the message: none, or the first alone.
  let places := (List.range flags.length).filter fun i => flags.getD i false
  cover 4 "in the first RPC alone" (places == [0])
  cover 8 "in no RPC" places.isEmpty
  cover 20 "in a later RPC" (places.any (· > 0))
  checkExtensionsOrder rpcs === (places.isEmpty || places == [0])

/-- The properties that must pass. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("protobuf: the records of a message", (recordsRead oracle).withTests cases),
  ("protobuf: the references read what the writer writes", (recordsWritten oracle).withTests cases),
  ("rpc: an RPC decodes as the schema says", (rpcDecode oracle).withTests cases),
  ("rpc: the rules that EthLib documents", (rpcRules oracle).withTests cases),
  ("rpc: the package reads and writes EthLib's bytes", (rpcEncode oracle).withTests cases),
  ("rpc: the flags of a subscription", partialFlags.withTests cases),
  ("rpc: the extensions message in the first RPC alone", extensionsOrder.withTests cases)]

/-- The properties that fail by design: each is a finding. -/
def findings (_oracle : Oracle) (_cases : Nat) : List (String × Property IO) := []

end DecodersProperty.Protobuf

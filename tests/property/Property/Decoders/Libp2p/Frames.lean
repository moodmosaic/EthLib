import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Networking.Libp2p.Mplex
import EthLib.Networking.Libp2p.Multistream
import EthLib.Networking.Libp2p.Yamux

/-!
# The byte codecs of yamux, mplex and multistream-select

A stream of frames is written by an encoder written here from the text of each format.

EthLib's decoder then reads it back one frame at a time, from the position of the model.

Every read is also given to a reader in the oracle, written from the same text in Python.

A transition changes one byte of the next frame, and the two readers must still agree.
-/

open Hedgehog Support EthLib EthLib.Networking EthLib.Networking.Libp2p

namespace DecodersProperty.Libp2p.Frames

open DecodersProperty

/-- One thing written to a stream. -/
structure Entry where
  /-- The kind of frame, for the labels. -/
  name : String
  /-- The bytes, as the text of the format gives them. -/
  bytes : List UInt8
  /-- What a reader finds, when the bytes are a valid frame as generated. -/
  expected : Option String
  /-- EthLib's bytes of the same frame, when it is one that EthLib encodes. -/
  encoded : Option (List UInt8)
  /-- Whether a byte was changed after the frame was written. -/
  mutated : Bool := false

instance : Repr Entry where
  reprPrec e _ := s!"{e.name} {hex (packed e.bytes)}{if e.mutated then " (mutated)" else ""}"

/-- The model: the frames not yet read, and how many bytes were read before them. -/
structure Wire where
  pending : List Entry
  position : Nat
  deriving Repr

/-- A transition of the stream. -/
inductive Step where
  /-- Append a frame. -/
  | write (entry : Entry)
  /-- Read the frame at the position. -/
  | read
  /-- Change one byte of the next frame to read. -/
  | corrupt (offset : Nat) (mask : UInt8)
  deriving Repr

/-- The next frame with one byte changed. -/
def corrupted (e : Entry) (offset : Nat) (mask : UInt8) : Entry :=
  let i := offset % e.bytes.length
  { e with bytes := e.bytes.set i (e.bytes.getD i 0 ^^^ mask), expected := none, mutated := true }

/-- The model of a stream: frames queue up, and a read moves the position past one of them. -/
def model (genEntry : Gen Entry) : Model Wire Step where
  initState := pure ⟨[], 0⟩
  transitions s :=
    Gen.frequency ([(5, Step.write <$> genEntry), (4, pure .read)] ++
      if s.pending.isEmpty then [] else
        [(1, Step.corrupt <$> Gen.nat (.constant 0 40) <*>
          (UInt8.ofNat <$> Gen.nat (.constant 1 255)))])
  apply s
    | .write e => { s with pending := s.pending ++ [e] }
    | .read =>
      match s.pending with
      | [] => s
      | e :: rest => ⟨rest, s.position + e.bytes.length⟩
    | .corrupt offset mask =>
      match s.pending with
      | [] => s
      | e :: rest => { s with pending := corrupted e offset mask :: rest }
  preconditions s
    | .corrupt .. => s.pending.any fun e => !e.bytes.isEmpty
    | _ => true

/-- The name of the constructor of an error, from its `Repr`. -/
def constructor {ε : Type} [Repr ε] (e : ε) : String :=
  let text := (toString (repr e)).takeWhile fun c => !c.isWhitespace && c != '('
  (text.toString.splitOn ".").getLastD ""

/-- A codec under test: the command of its reference, and EthLib's reader as text.

The text of a frame ends with the count of bytes left after it, and a refusal starts with `error`.

`covers` lists the labels that every run must reach, each with its least share of the sequences. -/
structure Codec where
  command : String
  decode : List UInt8 → String
  covers : List (Nat × String)

/-- The stream machine of a codec.

The system under test is EthLib's reader, which keeps no state: the model holds the position. -/
def machine (oracle : Oracle) (codec : Codec) (genEntry : Gen Entry) (long : Bool := true) :
    StateMachine Wire Step Unit IO where
  toModel := model genEntry
  initSut _ := pure ()
  applySut _ before _ step := do
    match step with
    | .write e =>
      -- EthLib's encoder writes the bytes that the text of the format gives.
      if let some bytes := e.encoded then bytes === e.bytes
    | .corrupt .. => pure ()
    | .read =>
      -- The read starts where the model was before the transition.
      let unread := before.pending.flatMap (·.bytes)
      let reference ← oracle.ask [codec.command, hex (packed unread)]
      let got := codec.decode unread
      annotate s!"position {before.position}, unread {hex (packed unread)}"
      annotate s!"EthLib: {got}"
      annotate s!"reference: {reference}"
      verdict got === verdict reference
      let (name, mutated) := match before.pending with
        | [] => ("nothing", false)
        | e :: _ => (e.name, e.mutated)
      if let e :: _ := before.pending then
        if let some frame := e.expected then
          got === s!"{frame} {unread.length - e.bytes.length}"
      let faulty := before.pending.head?.any fun e => e.expected.isNone && !e.mutated
      let reached := if faulty && !refused reference then
          s!"{name}: faulty as generated and accepted by the reference"
        else s!"{name}: {kind mutated reference}"
      label reached
      -- A share of a few percent is asked of a long run only: a hundred cases may hold none.
      for (minimum, wanted) in codec.covers do
        if minimum ≤ 2 then coverLong long minimum wanted (reached == wanted)
        else cover minimum wanted (reached == wanted)
      if refused got then label s!"EthLib refuses: {got}"

/-! ## yamux -/

/-- A big-endian number of a width, written from the text. -/
def be (width n : Nat) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat (n / 256 ^ (width - 1 - i))

/-- The names of the four types of a yamux frame. -/
def yamuxName (kind : Nat) : String :=
  match kind with
  | 0 => "data"
  | 1 => "window update"
  | 2 => "ping"
  | 3 => "go away"
  | _ => "unknown type"

/-- EthLib's type of a number from 0 to 3. -/
def yamuxKind (kind : Nat) : Yamux.Kind :=
  match kind with
  | 0 => .data
  | 1 => .windowUpdate
  | 2 => .ping
  | _ => .goAway

/-- A yamux frame: every type, any flags, any stream, and the faults of a header.

The header is version, type, flags, stream ID and length, as "Framing" lays them out. -/
def genYamux : Gen Entry := do
  let version ← Gen.frequency [(14, pure 0), (1, Gen.nat (.constant 1 255))]
  let kind ← Gen.frequency [(14, Gen.nat (.constant 0 3)), (1, Gen.nat (.constant 4 255))]
  let flags ← Gen.frequency [(6, Gen.nat (.constant 0 15)), (2, Gen.nat (.constant 0 65535)),
    (1, Gen.element [0x10, 0x100, 0x8000, 0xffff])]
  let stream ← Gen.frequency [(4, Gen.nat (.constant 0 8)), (2, genNatBits 32)]
  let data ← if kind = 0 then genByteList (.linear 0 40) else pure []
  let length ← if kind = 0 then
      Gen.frequency [(10, pure data.length), (1, (data.length + ·) <$> Gen.nat (.linear 1 300)),
        (1, genNatBits 32)]
    else Gen.frequency [(1, Gen.element [0, 1, 2, 262144, 2 ^ 31, 2 ^ 32 - 1]), (2, genNatBits 32)]
  let bytes := [UInt8.ofNat version, UInt8.ofNat kind] ++ be 2 flags ++ be 4 stream ++
    be 4 length ++ data
  let valid := version = 0 ∧ kind ≤ 3 ∧ (kind = 0 → length = data.length)
  let frame : Yamux.Frame := ⟨yamuxKind kind, flags.toUInt16, stream.toUInt32, length.toUInt32,
    packed data⟩
  let name := if version ≠ 0 then "another version" else if kind = 0 ∧ length ≠ data.length
    then "data of another length" else yamuxName kind
  pure { name, bytes
         expected := if valid then some s!"{kind} {flags} {stream} {length} {hex (packed data)}"
           else none
         encoded := if valid then some (Yamux.encode frame) else none }

/-- EthLib's yamux reader, as the text of the oracle. -/
def yamuxDecode (bytes : List UInt8) : String :=
  match Yamux.decode bytes with
  | .ok (f, rest) =>
    s!"{f.kind.toUInt8} {f.flags} {f.streamId} {f.length} {hex f.data} {rest.length}"
  | .error e => s!"error {constructor e}"

/-- The yamux codec, with the kinds of read that a run must reach. -/
def yamux : Codec where
  command := "yamux"
  decode := yamuxDecode
  covers := [(14, "data: valid as generated"), (14, "window update: valid as generated"),
    (14, "ping: valid as generated"), (14, "go away: valid as generated"),
    (8, "unknown type: refused by the reference"),
    (8, "another version: refused by the reference"),
    (3, "data: mutated and still accepted by the reference"),
    (1, "data: refused by the reference"), (20, "nothing: refused by the reference")]

/-! ## mplex -/

/-- The unsigned varint of a number, with as many zero groups after it as asked.

Seven bits a byte, least significant first, the top bit set on every byte but the last. -/
def uvarint (n : Nat) (padding : Nat := 0) : List UInt8 :=
  let rec groups (fuel n : Nat) : List Nat :=
    match fuel with
    | 0 => [n % 128]
    | fuel + 1 => if n < 128 then [n] else n % 128 :: groups fuel (n / 128)
  let all := groups 20 n ++ List.replicate padding 0
  all.mapIdx fun i g => UInt8.ofNat (g + if i + 1 < all.length then 128 else 0)

/-- The names of the flags of an mplex frame. -/
def mplexName (flag : Nat) : String :=
  match flag with
  | 0 => "new stream"
  | 1 | 2 => "message"
  | 3 | 4 => "close"
  | 5 | 6 => "reset"
  | _ => "flag 7"

/-- EthLib's flag of a number from 0 to 6. -/
def mplexFlag (flag : Nat) : Mplex.Flag := (Mplex.Flag.ofNat? flag).getD .newStream

/-- An mplex frame: every flag, stream IDs to the bound and past it, and the faults of a frame.

The header is the stream ID shifted left by three, with the flag below it. -/
def genMplex : Gen Entry := do
  let stream ← Gen.frequency [(5, Gen.nat (.constant 0 20)), (2, genNatBits 60),
    (1, Gen.element [2 ^ 4 - 1, 2 ^ 4, 2 ^ 11, 2 ^ 53, 2 ^ 60 - 1, 2 ^ 60, 2 ^ 61, 2 ^ 64])]
  let flag ← Gen.frequency [(14, Gen.nat (.constant 0 6)), (1, pure 7)]
  let ends := 3 ≤ flag ∧ flag ≤ 6
  let data ← if ends then Gen.frequency [(8, pure []), (1, genByteList (.linear 1 10))]
    else genByteList (.linear 0 40)
  let length ← Gen.frequency [(12, pure data.length),
    (1, (data.length + ·) <$> Gen.nat (.linear 1 300)),
    (1, Gen.element [2 ^ 20, 2 ^ 20 + 1, 2 ^ 32, 2 ^ 63 - 1, 2 ^ 63])]
  let headerPadding ← Gen.frequency [(14, pure 0), (1, Gen.nat (.constant 1 3))]
  let lengthPadding ← Gen.frequency [(14, pure 0), (1, Gen.nat (.constant 1 3))]
  let bytes := uvarint (stream * 8 + flag) headerPadding ++ uvarint length lengthPadding ++ data
  let valid := stream < 2 ^ 60 ∧ flag ≤ 6 ∧ length = data.length ∧ headerPadding = 0 ∧
    lengthPadding = 0 ∧ (ends → data = [])
  let name := if headerPadding ≠ 0 ∨ lengthPadding ≠ 0 then "a padded varint"
    else if 2 ^ 60 ≤ stream then "a stream ID past the bound"
    else if length ≠ data.length then "another length"
    else if ends ∧ data ≠ [] then "data on a close or a reset"
    else mplexName flag
  pure { name, bytes
         expected := if valid then some s!"{stream} {flag} {hex (packed data)}" else none
         encoded := if valid then some (Mplex.encode ⟨stream, mplexFlag flag, packed data⟩)
           else none }

/-- EthLib's mplex reader, as the text of the oracle. -/
def mplexDecode (bytes : List UInt8) : String :=
  match Mplex.decode bytes with
  | .ok (f, rest) => s!"{f.streamId} {f.flag.toNat} {hex f.data} {rest.length}"
  | .error e => s!"error {constructor e}"

/-- The mplex codec, with the kinds of read that a run must reach. -/
def mplex : Codec where
  command := "mplex"
  decode := mplexDecode
  covers := [(8, "new stream: valid as generated"), (12, "message: valid as generated"),
    (12, "close: valid as generated"), (12, "reset: valid as generated"),
    (5, "flag 7: refused by the reference"),
    (11, "a padded varint: refused by the reference"),
    (5, "a stream ID past the bound: refused by the reference"),
    (6, "data on a close or a reset: refused by the reference"),
    (3, "message: mutated and still accepted by the reference"),
    (1, "message: refused by the reference")]

/-- A frame of exactly 1 MiB of data is read, and one byte more is refused.

"Writing to a stream" asks a sender to write at most 1 MiB.

EthLib documents that its reader refuses more. -/
def mplexLimit (oracle : Oracle) : Property IO := propertyM do
  let stream ← forAll (Gen.nat (.constant 0 1000))
  let flag ← forAll (Gen.nat (.constant 0 2))
  let fill ← forAll genByte
  let present ← forAll (Gen.frequency [(4, pure true), (1, pure false)])
  pure do
    for size in [2 ^ 20 - 1, 2 ^ 20, 2 ^ 20 + 1] do
      let data := if present then List.replicate size fill else []
      let bytes := uvarint (stream * 8 + flag) ++ uvarint size ++ data
      let reference ← oracle.ask ["mplex", hex (packed bytes)]
      let got := mplexDecode bytes
      verdict got === verdict reference
      if !refused reference then got === reference
      -- The bound itself, apart from the two readers: 1,048,576 bytes and no more.
      refused got === (decide (1048576 < size) || !present)
    classify "the data is there" present
    classify "the data is missing" !present

/-! ## multistream-select -/

/-- The protocol names of the consensus layer, and the two words of multistream-select. -/
def names : List String :=
  ["/multistream/1.0.0", "na", "ls", "/noise", "/yamux/1.0.0", "/mplex/6.7.0",
    "/eth2/beacon_chain/req/status/1/ssz_snappy", "/meshsub/1.1.0", ""]

/-- A multistream-select message: a name or any bytes, and the faults of its framing.

The length is a varint that counts the newline after the message. -/
def genMessage : Gen Entry := do
  let message ← Gen.frequency [(6, (·.toUTF8.data.toList) <$> Gen.element names),
    (3, genByteList (.linear 0 30)),
    (1, (List.replicate · 0x61) <$> Gen.element [126, 127, 128, 16382, 16383, 16384])]
  let last ← Gen.frequency [(12, pure 0x0a), (1, genByte)]
  let length ← Gen.frequency [(12, pure (message.length + 1)), (1, pure 0),
    (1, pure message.length), (1, (message.length + 1 + ·) <$> Gen.nat (.linear 1 300))]
  let padding ← Gen.frequency [(14, pure 0), (1, Gen.nat (.constant 1 3))]
  let bytes := uvarint length padding ++ message ++ [last]
  let valid := last = 0x0a ∧ length = message.length + 1 ∧ padding = 0
  let name := if padding ≠ 0 then "a padded varint" else if length = 0 then "a length of zero"
    else if length ≠ message.length + 1 then "another length"
    else if last ≠ 0x0a then "no newline"
    else if message.length ≥ 126 then "a long message" else "a message"
  pure { name, bytes
         expected := if valid then some (hex (packed message)) else none
         encoded := if valid then some (Multistream.encode (packed message)) else none }

/-- EthLib's multistream-select reader, as the text of the oracle. -/
def messageDecode (bytes : List UInt8) : String :=
  match Multistream.decode bytes with
  | .ok (message, rest) => s!"{hex message} {rest.length}"
  | .error e => s!"error {constructor e}"

/-- The multistream-select codec, with the kinds of read that a run must reach. -/
def multistream : Codec where
  command := "mss"
  decode := messageDecode
  covers := [(22, "a message: valid as generated"), (6, "a long message: valid as generated"),
    (7, "a padded varint: refused by the reference"),
    (8, "a length of zero: refused by the reference"),
    (8, "a message: mutated and still accepted by the reference"),
    (4, "a message: refused by the reference")]

/-- The numbers and the names that the texts fix, written here from the texts.

yamux: "Framing", "Flag Field", "Flow Control" and "Session termination".

mplex: "Flag Values" and "Writing to a stream"; its name is in the consensus specification. -/
def constants : Property IO := pureIO do
  Yamux.headerSize === 12
  (Yamux.syn, Yamux.ack, Yamux.fin, Yamux.rst) === (1, 2, 4, 8)
  Yamux.initialWindow === 256 * 1024
  (Yamux.goAwayNormal, Yamux.goAwayProtocolError, Yamux.goAwayInternalError) === (0, 1, 2)
  [Yamux.Kind.data, .windowUpdate, .ping, .goAway].map (·.toUInt8) === [0, 1, 2, 3]
  hex Yamux.protocolId === hex "/yamux/1.0.0".toUTF8
  hex Mplex.protocolId === hex "/mplex/6.7.0".toUTF8
  Mplex.maxData === 1024 * 1024
  [Mplex.Flag.newStream, .messageReceiver, .messageInitiator, .closeReceiver, .closeInitiator,
    .resetReceiver, .resetInitiator].map (·.toNat) === [0, 1, 2, 3, 4, 5, 6]
  hex Multistream.protocolId === hex "/multistream/1.0.0".toUTF8
  hex Multistream.notAvailable === hex "na".toUTF8
  Multistream.newline === 0x0a

/-- The properties of the byte codecs. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("yamux: a stream of frames is read back, one frame at a time (StateMachine)",
    ((machine oracle yamux genYamux (cases ≥ 1000)).property (.linear 1 60)).withTests cases),
  ("mplex: a stream of frames is read back, one frame at a time (StateMachine)",
    ((machine oracle mplex genMplex (cases ≥ 1000)).property (.linear 1 60)).withTests cases),
  ("mplex: a frame of 1 MiB is read, and one byte more is refused",
    (mplexLimit oracle).withTests (min cases 10)),
  ("yamux: the numbers and names of the texts, and those of mplex and multistream",
    constants.withTests 1),
  ("multistream: a stream of messages is read back, one at a time (StateMachine)",
    ((machine oracle multistream genMessage (cases ≥ 1000)).property (.linear 1 60)).withTests
      cases)]

end DecodersProperty.Libp2p.Frames

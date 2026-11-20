import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Networking.Quic.Frame
import EthLib.Networking.Quic.Keys
import EthLib.Networking.Quic.Packet
import EthLib.Networking.Quic.Protection
import EthLib.Networking.Quic.Varint

/-!
# QUIC frames, headers and integers, on generated inputs

A frame or a header is built here field by field, with the text that a reader must give for it.

EthLib reads the bytes, and so does a reader written from RFC 9000 in the oracle, over aioquic.

The three must agree: what was built, what EthLib reads, what the reference reads.

A payload of frames and a datagram of coalesced packets are read back one at a time.
-/

open Hedgehog Support EthLib
open EthLib.Networking.Quic

namespace DecodersProperty.Quic

open DecodersProperty

/-! ## Bytes of the wire, built apart from EthLib -/

/-- A number in `n` bytes, big-endian. -/
def be (n v : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (v / 256 ^ (n - 1 - i))

/-- The least width that holds a value: 0 to 3, for 1, 2, 4 and 8 bytes. -/
def minWidth (v : Nat) : Nat :=
  if v < 2 ^ 6 then 0 else if v < 2 ^ 14 then 1 else if v < 2 ^ 30 then 2 else 3

/-- A QUIC integer at a width: the width in the two high bits, then the value. -/
def qv (width v : Nat) : List UInt8 :=
  match be (2 ^ width) v with
  | [] => []
  | head :: tail => (head ||| UInt8.ofNat (width * 64)) :: tail

/-- An integer in its shortest form, or at times in a longer one, which section 16 permits. -/
def genQv (v : Nat) : Gen (List UInt8) :=
  (qv · v) <$> Gen.frequency [(4, pure (minWidth v)), (1, Gen.nat (.constant (minWidth v) 3))]

/-- A value of a QUIC integer: small, at the edge of a width, or any. -/
def genVar : Gen Nat :=
  Gen.frequency [(4, Gen.nat (.linear 0 63)),
    (2, Gen.element [63, 64, 16383, 16384, 2 ^ 30 - 1, 2 ^ 30, 2 ^ 62 - 1]), (2, genNatBits 62)]

/-- Bytes behind a mark, so that no bytes differ from no value. -/
def x (bytes : List UInt8) : String :=
  "x" ++ (if bytes.isEmpty then "" else hex (packed bytes))

/-- A flag. -/
def bit (flag : Bool) : String := if flag then "1" else "0"

/-- The largest value of a QUIC integer. -/
def maxVar : Nat := 2 ^ 62 - 1

/-! ## Frames -/

/-- A frame as bytes, with what a reader must say of it.

`pkts` holds the packets that may carry it, in the letters of RFC 9000, Table 3.

`text` is the frame as the oracle writes one, or `error:encoding` for a frame that breaks a rule.

A greedy frame is a STREAM frame without a length, which takes the rest of the payload. -/
structure Made where
  name : String
  pkts : String
  text : String
  bytes : List UInt8
  greedy : Bool := false
  /-- How many more bytes a greedy frame may take before its data ends past `2^62 - 1`. -/
  room : Nat := 0
  deriving Repr, BEq

/-- A frame of one type byte and integers after it. -/
def genSimple (name pkts word : String) (kind : UInt8) (count : Nat) : Gen Made := do
  let values ← Gen.list (.singleton count) genVar
  let fields ← values.mapM genQv
  pure { name, pkts, text := ":".intercalate (word :: values.map toString),
         bytes := kind :: fields.flatten }

/-- Additional ACK ranges that keep every packet number at zero or above.

`smallest` is the smallest number acknowledged so far.

A range often takes all the room that is left, so the bound is met exactly. -/
def genRanges : Nat → Nat → Gen (List (Nat × Nat))
  | 0, _ => pure []
  | n + 1, smallest =>
    if smallest < 2 then pure []
    else Gen.frequency [(1, pure []), (3, do
      let gap ← Gen.frequency [(2, pure 0), (1, pure (smallest - 2)),
        (2, Gen.nat (.constant 0 (smallest - 2)))]
      let room := smallest - 2 - gap
      let length ← Gen.frequency [(2, pure 0), (2, pure room), (2, Gen.nat (.constant 0 room))]
      pure ((gap, length) :: (← genRanges n (room - length))))]

/-- The bytes and the text of an ACK frame of given fields. -/
def ackOf (largest delay first : Nat) (ranges : List (Nat × Nat)) (ecn : Option (List Nat))
    (count : Nat) : Gen (String × List UInt8) := do
  let head ← [largest, delay, count, first].mapM genQv
  let body ← ranges.mapM fun (gap, length) => do pure ((← genQv gap) ++ (← genQv length))
  let tail ← (ecn.getD []).mapM genQv
  let shown := ",".intercalate (ranges.map fun (gap, length) => s!"{gap}-{length}")
  let counts := match ecn with
    | none => "-"
    | some values => "/".intercalate (values.map toString)
  pure (s!"ack:{largest}:{delay}:{first}:[{shown}]:{counts}",
    (if ecn.isSome then 3 else 2) :: (head ++ body ++ tail).flatten)

/-- An ACK frame with valid ranges, with or without the ECN counts. -/
def genAck (ecn : Bool) : Gen Made := do
  let largest ← genVar
  let delay ← genVar
  let first ← Gen.frequency [(2, pure 0), (1, pure largest), (3, Gen.nat (.constant 0 largest))]
  let ranges ← genRanges 3 (largest - first)
  let counts ← if ecn then some <$> Gen.list (.singleton 3) genVar else pure none
  let (text, bytes) ← ackOf largest delay first ranges counts ranges.length
  pure { name := if ecn then "ACK with ECN" else "ACK", pkts := "IH1", text, bytes }

/-- An offset that leaves room for `size` bytes below `2^62`, often none to spare. -/
def genOffset (size : Nat) : Gen Nat :=
  Gen.frequency [(3, (min · (maxVar - size)) <$> genVar), (1, pure (maxVar - size))]

/-- A CRYPTO frame. -/
def genCrypto : Gen Made := do
  let data ← genByteList (.linear 0 6)
  let offset ← genOffset data.length
  pure { name := "CRYPTO", pkts := "IH1", text := s!"crypto:{offset}:{x data}",
         bytes := [6] ++ (← genQv offset) ++ (← genQv data.length) ++ data }

/-- A NEW_TOKEN frame, whose token has a byte at least. -/
def genNewToken : Gen Made := do
  let token ← genByteList (.linear 1 6)
  pure { name := "NEW_TOKEN", pkts := "1", text := s!"new_token:{x token}",
         bytes := [7] ++ (← genQv token.length) ++ token }

/-- A STREAM frame with the given OFF, LEN and FIN bits. -/
def genStream (off len fin : Bool) : Gen Made := do
  let id ← genVar
  let data ← genByteList (.linear 0 6)
  let offset ← genOffset data.length
  let offsetBytes ← genQv offset
  let lengthBytes ← genQv data.length
  let kind := 8 + (if off then 4 else 0) + (if len then 2 else 0) + (if fin then 1 else 0)
  pure { name := "STREAM", pkts := "01", greedy := !len,
         room := maxVar - (if off then offset else 0) - data.length,
         text := s!"stream:{id}:{if off then toString offset else "-"}:{bit len}:{bit fin}:" ++
           x data,
         bytes := [kind] ++ (← genQv id) ++ (if off then offsetBytes else []) ++
           (if len then lengthBytes else []) ++ data }

/-- A MAX_STREAMS or STREAMS_BLOCKED frame, with a count of `2^60` at most. -/
def genStreams (blocked uni : Bool) : Gen Made := do
  let limit ← Gen.frequency [(3, (min · (2 ^ 60)) <$> genVar), (1, pure (2 ^ 60))]
  let word := if blocked then "streams_blocked" else "max_streams"
  pure { name := if blocked then "STREAMS_BLOCKED" else "MAX_STREAMS", pkts := "01",
         text := s!"{word}:{bit uni}:{limit}",
         bytes := [(if blocked then 0x16 else 0x12) + (if uni then 1 else 0)] ++ (← genQv limit) }

/-- A NEW_CONNECTION_ID frame: an ID of 1 to 20 bytes, and Retire Prior To at most the sequence. -/
def genNewConnectionId : Gen Made := do
  let sequence ← genVar
  let retire ← Gen.frequency [(2, pure 0), (2, pure sequence), (2, Gen.nat (.constant 0 sequence))]
  let cid ← Gen.frequency [(3, genByteList (.linear 1 20)), (1, genByteList (.singleton 20)),
    (1, genByteList (.singleton 1))]
  let token ← genByteList (.singleton 16)
  pure { name := "NEW_CONNECTION_ID", pkts := "01",
         text := s!"new_connection_id:{sequence}:{retire}:{x cid}:{x token}",
         bytes := [0x18] ++ (← genQv sequence) ++ (← genQv retire) ++
           [UInt8.ofNat cid.length] ++ cid ++ token }

/-- A PATH_CHALLENGE or PATH_RESPONSE frame. -/
def genPath (response : Bool) : Gen Made := do
  let data ← genByteList (.singleton 8)
  pure { name := if response then "PATH_RESPONSE" else "PATH_CHALLENGE",
         pkts := if response then "1" else "01",
         text := (if response then "path_response:" else "path_challenge:") ++ x data,
         bytes := (if response then 0x1b else 0x1a) :: data }

/-- A CONNECTION_CLOSE frame of the transport (0x1c) or of the application (0x1d). -/
def genClose (transport : Bool) : Gen Made := do
  let code ← genVar
  let frame ← genVar
  let reason ← genByteList (.linear 0 6)
  let frameBytes ← genQv frame
  pure { name := if transport then "CONNECTION_CLOSE 0x1c" else "CONNECTION_CLOSE 0x1d",
         pkts := if transport then "IH01" else "01",
         text := s!"connection_close:{code}:{if transport then toString frame else "-"}:{x reason}",
         bytes := [if transport then 0x1c else 0x1d] ++ (← genQv code) ++
           (if transport then frameBytes else []) ++ (← genQv reason.length) ++ reason }

/-- A frame with no fields. -/
def bare (name pkts text : String) (kind : UInt8) : Gen Made :=
  pure { name, pkts, text, bytes := [kind] }

/-- Every frame type of RFC 9000 section 19, each valid. -/
def genValid : Gen Made :=
  Gen.choice [
    bare "PADDING" "IH01" "padding" 0, bare "PING" "IH01" "ping" 1, genAck false, genAck true,
    genSimple "RESET_STREAM" "01" "reset_stream" 4 3,
    genSimple "STOP_SENDING" "01" "stop_sending" 5 2, genCrypto, genNewToken,
    do genStream (← Gen.bool) (← Gen.bool) (← Gen.bool),
    do genStream (← Gen.bool) true (← Gen.bool),
    do genStream (← Gen.bool) false (← Gen.bool),
    genSimple "MAX_DATA" "01" "max_data" 0x10 1,
    genSimple "MAX_STREAM_DATA" "01" "max_stream_data" 0x11 2,
    do genStreams false (← Gen.bool), genSimple "DATA_BLOCKED" "01" "data_blocked" 0x14 1,
    genSimple "STREAM_DATA_BLOCKED" "01" "stream_data_blocked" 0x15 2,
    do genStreams true (← Gen.bool), genNewConnectionId,
    genSimple "RETIRE_CONNECTION_ID" "01" "retire_connection_id" 0x19 1, genPath false,
    genPath true, genClose true, genClose false, bare "HANDSHAKE_DONE" "1" "handshake_done" 0x1e]

/-- The names of the frame types, for the coverage of a property. -/
def frameNames : List String :=
  ["PADDING", "PING", "ACK", "ACK with ECN", "RESET_STREAM", "STOP_SENDING", "CRYPTO",
    "NEW_TOKEN", "STREAM", "MAX_DATA", "MAX_STREAM_DATA", "MAX_STREAMS", "DATA_BLOCKED",
    "STREAM_DATA_BLOCKED", "STREAMS_BLOCKED", "NEW_CONNECTION_ID", "RETIRE_CONNECTION_ID",
    "PATH_CHALLENGE", "PATH_RESPONSE", "CONNECTION_CLOSE 0x1c", "CONNECTION_CLOSE 0x1d",
    "HANDSHAKE_DONE"]

/-- A frame that breaks one rule of its type, each by the least amount. -/
def genBroken : Gen Made := do
  let broken (name : String) (bytes : List UInt8) : Made :=
    { name, pkts := "IH01", text := "error:encoding", bytes }
  Gen.choice [
    -- A frame type in a longer form than it needs, section 12.4.
    do
      let valid ← genValid
      let width ← Gen.nat (.constant 1 3)
      pure (broken "a type in a longer form" (qv width (valid.bytes.headD 0).toNat ++
        valid.bytes.drop 1)),
    -- A frame type that version 1 does not have.
    do
      let kind ← Gen.frequency [(3, Gen.nat (.constant 0x1f 0x3f)),
        (1, (fun n => min maxVar (0x1f + n)) <$> genNatBits 62)]
      pure (broken "an unknown type" (qv (minWidth kind) kind ++ [0, 0, 0])),
    -- The first ACK range passes the largest number.
    do
      let largest ← (min · (maxVar - 1)) <$> genVar
      let (_, bytes) ← ackOf largest 0 (largest + 1) [] none 0
      pure (broken "an ACK range below zero" bytes),
    -- A later ACK range passes the smallest number by one.
    do
      let largest ← (· + 2) <$> Gen.nat (.linear 0 1000)
      let first ← Gen.nat (.constant 0 (largest - 2))
      let ranges ← genRanges 2 (largest - first)
      let left := ranges.foldl (fun left (gap, length) => left - gap - 2 - length) (largest - first)
      let last ← Gen.element [(left - 1, 0), (0, left - 1), (left, 0)]
      let (_, bytes) ← ackOf largest 0 first (ranges ++ [last]) none (ranges.length + 1)
      pure (broken "an ACK range below zero" bytes),
    -- More ACK ranges are announced than follow.
    do
      let (_, bytes) ← ackOf 100 0 0 [] none (← Gen.element [1, 2, 2 ^ 62 - 1])
      pure (broken "an ACK with ranges missing" bytes),
    -- CRYPTO and STREAM data that ends at `2^62`, one past the largest offset.
    do
      let data ← genByteList (.linear 1 6)
      let offset := 2 ^ 62 - data.length
      pure (broken "CRYPTO past 2^62 - 1" ([6] ++ qv 3 offset ++ qv 0 data.length ++ data)),
    do
      let data ← genByteList (.linear 1 6)
      let offset := 2 ^ 62 - data.length
      let len ← Gen.bool
      pure (broken "STREAM past 2^62 - 1" ([if len then 0x0e else 0x0c, 0] ++ qv 3 offset ++
        (if len then qv 0 data.length else []) ++ data)),
    -- A token of no bytes.
    pure (broken "an empty token" [7, 0]),
    -- A stream count above `2^60`.
    do
      let kind ← Gen.element [0x12, 0x13, 0x16, 0x17]
      let limit ← Gen.frequency [(2, pure (2 ^ 60 + 1)),
        (1, Gen.nat (.constant (2 ^ 60 + 1) maxVar))]
      pure (broken "a stream count above 2^60" (kind :: qv 3 limit)),
    -- A connection ID of no byte, or of more than 20.
    do
      let length ← Gen.frequency [(2, pure 0), (2, pure 21), (1, Gen.nat (.constant 21 255))]
      let cid ← genByteList (.singleton length)
      let token ← genByteList (.singleton 16)
      pure (broken "a connection ID of a bad length" ([0x18, 1, 0, UInt8.ofNat length] ++ cid ++
        token)),
    -- Retire Prior To above the sequence number.
    do
      let sequence ← (min · (maxVar - 1)) <$> genVar
      let token ← genByteList (.singleton 16)
      pure (broken "Retire Prior To above the sequence" ([0x18] ++ qv 3 sequence ++
        qv 3 (sequence + 1) ++ [1, 0xaa] ++ token)),
    -- A length that passes the end of the payload.
    do
      let kind ← Gen.element [6, 7, 0x0a, 0x1d]
      let data ← genByteList (.linear 0 4)
      let extra ← Gen.frequency [(2, pure 1), (1, Gen.nat (.linear 1 1000))]
      let head : List UInt8 := if kind = 7 then [] else [0]
      pure (broken "a length past the payload" ([kind] ++ head ++
        qv 1 (data.length + extra) ++ data))]

/-- A frame as text: the name of what was built, and its bytes. -/
def showMade (made : Made) : String := s!"{made.name} {hex (packed made.bytes)}"

/-- The four packets that carry frames, with the name and the letter of each. -/
def packets : List (Packet.PacketType × String × String) :=
  [(.initial, "initial", "I"), (.handshake, "handshake", "H"), (.zeroRtt, "zerortt", "0"),
    (.oneRtt, "onertt", "1")]

/-- A frame as the oracle writes one. -/
def showFrame : Frame.Frame → String
  | .padding => "padding"
  | .ping => "ping"
  | .ack a =>
    let ranges := ",".intercalate (a.ranges.map fun (gap, length) => s!"{gap.val}-{length.val}")
    let counts := match a.ecn with
      | none => "-"
      | some (ect0, ect1, ce) => s!"{ect0.val}/{ect1.val}/{ce.val}"
    s!"ack:{a.largest.val}:{a.delay.val}:{a.firstRange.val}:[{ranges}]:{counts}"
  | .resetStream id code size => s!"reset_stream:{id.val}:{code.val}:{size.val}"
  | .stopSending id code => s!"stop_sending:{id.val}:{code.val}"
  | .crypto offset data => s!"crypto:{offset.val}:{x data.toList}"
  | .newToken token => s!"new_token:{x token.toList}"
  | .stream id offset len fin data =>
    let shown := match offset with
      | none => "-"
      | some o => toString o.val
    s!"stream:{id.val}:{shown}:{bit len}:{bit fin}:{x data.toList}"
  | .maxData n => s!"max_data:{n.val}"
  | .maxStreamData id n => s!"max_stream_data:{id.val}:{n.val}"
  | .maxStreams uni n => s!"max_streams:{bit uni}:{n.val}"
  | .dataBlocked n => s!"data_blocked:{n.val}"
  | .streamDataBlocked id n => s!"stream_data_blocked:{id.val}:{n.val}"
  | .streamsBlocked uni n => s!"streams_blocked:{bit uni}:{n.val}"
  | .newConnectionId sequence retire cid token =>
    s!"new_connection_id:{sequence.val}:{retire.val}:{x cid.toList}:{x token.toList}"
  | .retireConnectionId n => s!"retire_connection_id:{n.val}"
  | .pathChallenge data => s!"path_challenge:{x data.toList}"
  | .pathResponse data => s!"path_response:{x data.toList}"
  | .connectionClose code frame reason =>
    let shown := match frame with
      | none => "-"
      | some f => toString f.val
    s!"connection_close:{code.val}:{shown}:{x reason.toList}"
  | .handshakeDone => "handshake_done"

/-- What EthLib reads at the start of a payload: the frame and the bytes after it, or the error. -/
def readFrame (packet : Packet.PacketType) (bytes : List UInt8) : String :=
  match Frame.decode packet (packed bytes) with
  | .ok (frame, rest) => s!"{showFrame frame} {hex rest}"
  | .error (.protocolViolation _) => "error:violation"
  | .error _ => "error:encoding"

/-- What a reader must give for a built frame in a packet, with `rest` after it.

The form of a frame is checked before its packet, so a frame that breaks both is malformed. -/
def expected (made : Made) (letter : String) (rest : List UInt8) : String :=
  if refused made.text then made.text
  -- The bytes after a frame without a length are its data, which may not pass `2^62 - 1`.
  else if made.greedy && rest.length > made.room then "error:encoding"
  else if !(made.pkts.splitOn letter).length > 1 then "error:violation"
  else if made.greedy then
    made.text ++ (if rest.isEmpty then "" else hex (packed rest)) ++ " -"
  else s!"{made.text} {hex (packed rest)}"

/-- An answer of the oracle, which must not say that its two readers disagree. -/
def ask (oracle : Oracle) (command : List String) : TestT IO String := do
  let answer ← oracle.ask command
  ensure (!answer.startsWith "error DisagreeError") answer
  pure answer

/-- A frame reads as RFC 9000 section 19 says, in each of the four packets.

What was built, what EthLib reads and what the reference reads are the same.

A frame that EthLib reads, it writes back in bytes that read as the same frame. -/
def frameDecode (oracle : Oracle) (long : Bool) : Property IO := propertyM do
  let shape ← forAll (Gen.frequency [(5, pure "valid"), (3, pure "broken"), (2, pure "mutated")])
  let made ← forAllWith showMade (if shape == "broken" then genBroken else genValid)
  let (packet, word, letter) ← forAllWith (·.2.1) (Gen.element packets)
  let rest ← forAllWith (fun b => hex (packed b))
    (if shape == "broken" then pure [] else Gen.frequency [(2, pure []),
      (1, genByteList (.linear 1 4))])
  let bytes ← forAllWith (fun b => hex (packed b))
    (if shape == "mutated" then genMutation made.bytes else pure made.bytes)
  pure do
    let input := bytes ++ rest
    let reference ← ask oracle ["quic_frame", word, hex (packed input)]
    let got := readFrame packet input
    frameNames.forM fun name => coverLong long 1 name (made.name == name && shape != "broken")
    cover 12 "valid as generated" (shape == "valid" && !refused reference)
    coverLong long 1 "mutated and still accepted by the reference"
      (shape == "mutated" && !refused reference)
    cover 12 "refused by the reference for its encoding" (reference == "error:encoding")
    cover 5 "refused by the reference for its packet" (reference == "error:violation")
    if shape == "broken" then label made.name
    classify "a STREAM frame without a length" (made.greedy && shape == "valid")
    classify "bytes after the frame" (!rest.isEmpty)
    got === reference
    if shape != "mutated" then reference === expected made letter rest
    -- The writer: what EthLib read, it writes in bytes that read as the same frame.
    if let .ok (frame, after) := Frame.decode packet (packed input) then
      match Frame.encode frame with
      | .error e => failWith s!"EthLib does not write the frame it read: {repr e}"
      | .ok written =>
        ensure (written.size + after.size ≤ input.length) "the written frame is longer"
        readFrame packet (written.toList ++ after.toList) === got
        (← ask oracle ["quic_frame", word, hex (written ++ after)]) === got

/-! ### A payload of frames, read back one at a time -/

/-- A payload: the frames written so far, and how many of them were read.

`stuck` says that a frame was refused, so the reader stays before it.

`spoiled` says that an unread byte was changed, so only the reference knows what follows. -/
structure Payload where
  packet : Nat
  frames : List Made := []
  read : Nat := 0
  stuck : Bool := false
  spoiled : Bool := false
  deriving Repr

/-- A step on a payload. -/
inductive PayloadStep where
  | write (made : Made)
  | read
  | spoil (at_ : Nat) (mask : UInt8)

instance : Repr PayloadStep where
  reprPrec
    | .write made, _ => s!"WRITE({showMade made})"
    | .read, _ => "READ"
    | .spoil at_ mask, _ => s!"SPOIL({at_}, {mask})"

/-- The packet of a payload: its type, its name and its letter. -/
def Payload.kind (p : Payload) : Packet.PacketType × String × String :=
  packets.getD p.packet (.oneRtt, "onertt", "1")

/-- Whether the packet of a payload may carry a frame. -/
def Payload.allows (p : Payload) (made : Made) : Bool :=
  (made.pkts.splitOn p.kind.2.2).length > 1

/-- The bytes of the frames that were not read. -/
def Payload.unread (p : Payload) : List UInt8 :=
  ((p.frames.drop p.read).map (·.bytes)).flatten

/-- The bytes of the frames after the one that the next read meets. -/
def Payload.following (p : Payload) : List UInt8 :=
  ((p.frames.drop (p.read + 1)).map (·.bytes)).flatten

/-- The model: a frame is read where the last one ended, and a greedy frame takes all the rest. -/
def payloadModel : Model Payload PayloadStep where
  initState := do pure { packet := ← Gen.nat (.constant 0 3) }
  transitions s :=
    -- Mostly frames that the packet may carry, so that a sequence is not stuck at once.
    let allowed := genValid.filter s.allows
    Gen.frequency [(5, .write <$> allowed), (1, .write <$> genValid), (5, pure .read),
      (1, do pure (.spoil (← Gen.nat (.linear 0 40)) (← Gen.element [1, 2, 0x40, 0x80, 0xff])))]
  apply s
    | .write made => { s with frames := s.frames ++ [made] }
    | .read =>
      if s.spoiled || s.stuck then s
      else match s.frames[s.read]? with
        | none => s
        | some made =>
          if refused (expected made s.kind.2.2 s.following) then { s with stuck := true }
          else if made.greedy then { s with read := s.frames.length }
          else { s with read := s.read + 1 }
    | .spoil .. => if s.unread.isEmpty then s else { s with spoiled := true }

/-- The machine: EthLib's reader holds the unread bytes of the payload.

Before a byte is changed, each frame must read as it was built, and leave the bytes of the rest.

After one is changed, each read must be what the reference reads from the same bytes. -/
def payloadMachine (oracle : Oracle) : StateMachine Payload PayloadStep (List UInt8) IO where
  toModel := payloadModel
  initSut _ := pure []
  applySut unread before after step := do
    let (packet, word, letter) := before.kind
    match step with
    | .write made => pure (unread ++ made.bytes)
    | .spoil at_ mask =>
      if unread.isEmpty then pure unread
      else
        let i := at_ % unread.length
        pure (unread.set i ((unread.getD i 0) ^^^ mask))
    | .read =>
      let got := readFrame packet unread
      let rest := match Frame.decode packet (packed unread) with
        | .ok (_, rest) => rest.toList
        | .error _ => unread
      if before.spoiled then
        label "a read after a changed byte"
        got === (← ask oracle ["quic_frame", word, hex (packed unread)])
      else match before.frames[before.read]? with
        | none =>
          label "a read at the end of the payload"
          unread === []
          got === "error:encoding"
        | some made =>
          -- The state before the read says where it started, and so what follows the frame.
          got === expected made letter before.following
          if before.stuck then label "a read again at a refused frame"
          else if after.stuck then label "a read of a frame that is refused"
          else
            label (if made.greedy then "a read of a frame without a length"
              else "a read of a frame")
            rest === after.unread
      pure rest

/-! ## Headers -/

/-- A header as bytes, with the text that a reader must give for it, or `error`. -/
structure MadeHeader where
  name : String
  text : String
  bytes : List UInt8
  /-- The length of the connection ID of a short header, which the connection knows. -/
  cidLength : Nat := 0
  /-- The bytes of the payload that the Length field announces after the packet number. -/
  payload : Nat := 0
  deriving Repr, BEq

/-- A connection ID of version 1: often none, eight or twenty bytes. -/
def genCid : Gen (List UInt8) :=
  Gen.frequency [(1, pure []), (2, genByteList (.singleton 8)), (1, genByteList (.singleton 20)),
    (3, genByteList (.linear 0 20))]

/-- The first bytes of a long header: the first byte, the version, the two connection IDs. -/
def longPrefix (first : Nat) (version : Nat) (dcid scid : List UInt8) : List UInt8 :=
  [UInt8.ofNat first] ++ be 4 version ++ [UInt8.ofNat dcid.length] ++ dcid ++
    [UInt8.ofNat scid.length] ++ scid

/-- A packet number of a width, with the bytes that hold it. -/
def genNumber (width : Nat) : Gen Nat :=
  Gen.frequency [(2, Gen.nat (.linear 0 255)), (1, pure (256 ^ (width + 1) - 1)),
    (2, Gen.nat (.constant 0 (256 ^ (width + 1) - 1)))]

/-- An Initial, 0-RTT or Handshake header, through its packet number. -/
def genLong (kind : Nat) : Gen MadeHeader := do
  let dcid ← genCid
  let scid ← genCid
  let token ← genByteList (.linear 0 6)
  let width ← Gen.nat (.constant 0 3)
  let payload ← Gen.frequency [(2, pure 0), (3, Gen.nat (.linear 0 40)), (1, genVar)]
  let length := min (width + 1 + payload) maxVar
  let number ← genNumber width
  let tokenBytes ← genQv token.length
  let name := ["initial", "zerortt", "handshake"].getD kind ""
  let shownToken := if kind = 0 then s!":{x token}" else ""
  pure { name, payload := length - (width + 1),
         text := s!"{name}:{x dcid}:{x scid}{shownToken}:{width}:{length}:{number}",
         bytes := longPrefix (0xc0 + kind * 16 + width) 1 dcid scid ++
           (if kind = 0 then tokenBytes ++ token else []) ++ (← genQv length) ++
           be (width + 1) number }

/-- A short header: the spin bit, the key phase, a connection ID of a known length. -/
def genShort : Gen MadeHeader := do
  let dcid ← genCid
  let spin ← Gen.bool
  let phase ← Gen.bool
  let width ← Gen.nat (.constant 0 3)
  let number ← genNumber width
  pure { name := "onertt", cidLength := dcid.length,
         text := s!"onertt:{x dcid}:{bit spin}:{bit phase}:{width}:{number}",
         bytes := [UInt8.ofNat (0x40 + (if spin then 0x20 else 0) + (if phase then 4 else 0) +
           width)] ++ dcid ++ be (width + 1) number }

/-- A Retry packet: a token of a byte at least, and the sixteen bytes of the tag. -/
def genRetry : Gen MadeHeader := do
  let dcid ← genCid
  let scid ← genCid
  let token ← genByteList (.linear 1 8)
  let tag ← genByteList (.singleton 16)
  let unused ← Gen.nat (.constant 0 15)
  pure { name := "retry", text := s!"retry:{x dcid}:{x scid}:{x token}:{x tag}:{unused}",
         bytes := longPrefix (0xf0 + unused) 1 dcid scid ++ token ++ tag }

/-- A Version Negotiation packet: connection IDs of 255 bytes at most, and any versions. -/
def genNegotiation : Gen MadeHeader := do
  let cid := Gen.frequency [(4, genCid), (1, genByteList (.constant 21 255)),
    (1, genByteList (.singleton 255))]
  let dcid ← cid
  let scid ← cid
  let unused ← Gen.nat (.constant 0 127)
  let versions ← Gen.list (.linear 0 4) (Gen.frequency [(1, Gen.element [0, 1, 0x6b3343cf]),
    (1, genNatBits 32)])
  let shown := ",".intercalate (versions.map toString)
  pure { name := "vn", text := s!"vn:{x dcid}:{x scid}:{unused}:[{shown}]",
         bytes := longPrefix (0x80 + unused) 0 dcid scid ++ (versions.map (be 4)).flatten }

/-- Every header of RFC 9000 section 17, each valid. -/
def genValidHeader : Gen MadeHeader :=
  Gen.choice [genLong 0, genLong 1, genLong 2, genShort, genRetry, genNegotiation]

/-- A header that breaks one rule of its form. -/
def genBrokenHeader : Gen MadeHeader := do
  let broken (name : String) (bytes : List UInt8) (cidLength : Nat := 0) : MadeHeader :=
    { name, text := "error", bytes, cidLength }
  let clear (mask : UInt8) (bytes : List UInt8) : List UInt8 :=
    match bytes with
    | [] => []
    | head :: tail => (head &&& ~~~mask) :: tail
  let set (mask : UInt8) (bytes : List UInt8) : List UInt8 :=
    match bytes with
    | [] => []
    | head :: tail => (head ||| mask) :: tail
  Gen.choice [
    -- The fixed bit is 0, in a short header and in a long one of version 1.
    do
      let h ← Gen.choice [genLong 0, genLong 1, genLong 2, genShort, genRetry]
      pure (broken "the fixed bit is 0" (clear 0x40 h.bytes) h.cidLength),
    -- A reserved bit is set.
    do
      let h ← genShort
      pure (broken "a reserved bit is set" (set (← Gen.element [0x08, 0x10, 0x18]) h.bytes)
        h.cidLength),
    do
      let h ← Gen.choice [genLong 0, genLong 1, genLong 2]
      pure (broken "a reserved bit is set" (set (← Gen.element [0x04, 0x08, 0x0c]) h.bytes)),
    -- A connection ID of more than 20 bytes in version 1.
    do
      let long ← Gen.frequency [(2, genByteList (.singleton 21)),
        (1, genByteList (.constant 21 255))]
      let other ← genCid
      let first ← Gen.element [0xc0, 0xd1, 0xe2, 0xf3]
      let (dcid, scid) ← Gen.element [(long, other), (other, long)]
      pure (broken "a connection ID of more than 20 bytes"
        (longPrefix first 1 dcid scid ++ [0, 1, 0] ++ List.replicate 20 0)),
    do
      let h ← genShort
      pure (broken "a connection ID of more than 20 bytes" (h.bytes ++ List.replicate 300 0)
        (← Gen.nat (.constant 21 40))),
    -- A version that is neither 0 nor 1.
    do
      let version ← Gen.frequency [(2, Gen.element [2, 0x6b3343cf, 0xff00001d, 2 ^ 32 - 1]),
        (1, Gen.nat (.constant 2 (2 ^ 32 - 1)))]
      let dcid ← genCid
      let first ← Gen.element [0xc0, 0xd1, 0xe2, 0xf3]
      pure (broken "another version" (longPrefix first version dcid [] ++ [0, 1, 0] ++
        List.replicate 20 0)),
    -- A Length that does not hold the packet number.
    do
      let width ← Gen.nat (.constant 1 3)
      let length ← Gen.nat (.constant 0 width)
      let kind ← Gen.element [1, 2]
      pure (broken "a Length below the packet number" (longPrefix (0xc0 + kind * 16 + width) 1
        [] [] ++ qv 0 length ++ be (width + 1) 0)),
    -- A Retry with no token: sixteen bytes or fewer after the connection IDs.
    do
      let rest ← genByteList (.constant 0 16)
      pure (broken "a Retry with no token" (longPrefix 0xf0 1 [1] [2] ++ rest)),
    -- A Version Negotiation packet whose versions do not fill four bytes each.
    do
      let rest ← genByteList (← Gen.element [.singleton 1, .singleton 2, .singleton 3,
        .singleton 5, .singleton 7])
      pure (broken "a version cut short" (longPrefix 0x80 0 [] [] ++ rest))]

/-- A header as text: the name of what was built, and its bytes. -/
def showMadeHeader (made : MadeHeader) : String :=
  s!"{made.name} {made.cidLength} {hex (packed made.bytes)}"

/-- A header as the oracle writes one. -/
def showHeader : Packet.Header → String
  | .initial d s t w l n =>
    s!"initial:{x d.toList}:{x s.toList}:{x t.toList}:{w.val}:{l.val}:{n}"
  | .zeroRtt d s w l n => s!"zerortt:{x d.toList}:{x s.toList}:{w.val}:{l.val}:{n}"
  | .handshake d s w l n => s!"handshake:{x d.toList}:{x s.toList}:{w.val}:{l.val}:{n}"
  | .oneRtt d spin phase w n => s!"onertt:{x d.toList}:{bit spin}:{bit phase}:{w.val}:{n}"
  | .retry d s t tag unused =>
    s!"retry:{x d.toList}:{x s.toList}:{x t.toList}:{x tag.toList}:{unused.val}"
  | .versionNegotiation d s unused versions =>
    let shown := ",".intercalate (versions.map (toString ·.toNat))
    s!"vn:{x d.toList}:{x s.toList}:{unused.val}:[{shown}]"

/-- What EthLib reads at the start of a datagram: the header and the bytes after it, or `error`. -/
def readHeader (cidLength : Nat) (bytes : List UInt8) : String :=
  match Packet.decode cidLength (packed bytes) with
  | .ok (header, rest) => s!"{showHeader header} {hex rest}"
  | .error _ => "error"

/-- The names of the header forms, for the coverage of a property. -/
def headerNames : List String := ["initial", "zerortt", "handshake", "onertt", "retry", "vn"]

/-- A header reads as RFC 9000 section 17 says.

What was built, what EthLib reads and what the reference reads are the same.

A header that EthLib reads, it writes back in bytes that read as the same header. -/
def headerDecode (oracle : Oracle) (long : Bool) : Property IO := propertyM do
  let shape ← forAll (Gen.frequency [(5, pure "valid"), (3, pure "broken"), (2, pure "mutated")])
  let made ← forAllWith showMadeHeader (if shape == "broken" then genBrokenHeader
    else genValidHeader)
  let whole := made.name == "retry" || made.name == "vn"
  let rest ← forAllWith (fun b => hex (packed b))
    (if shape == "broken" || whole then pure [] else genByteList (.linear 0 4))
  let bytes ← forAllWith (fun b => hex (packed b))
    (if shape == "mutated" then genMutation made.bytes else pure made.bytes)
  pure do
    let input := bytes ++ rest
    let reference ← ask oracle ["quic_header", toString made.cidLength, hex (packed input)]
    let got := readHeader made.cidLength input
    headerNames.forM fun name => cover 3 name (made.name == name)
    cover 20 "valid as generated" (shape == "valid" && !refused reference)
    coverLong long 2 "mutated and still accepted by the reference"
      (shape == "mutated" && !refused reference)
    cover 10 "refused by the reference" (refused reference)
    if shape == "broken" then label made.name
    got === reference
    if shape == "valid" then reference === s!"{made.text} {hex (packed rest)}"
    if shape == "broken" then reference === "error"
    if let .ok (header, after) := Packet.decode made.cidLength (packed input) then
      match Packet.encode header with
      | .error e => failWith s!"EthLib does not write the header it read: {repr e}"
      | .ok written =>
        ensure (written.size + after.size ≤ input.length) "the written header is longer"
        readHeader made.cidLength (written.toList ++ after.toList) === got
        (← ask oracle ["quic_header", toString made.cidLength, hex (written ++ after)]) === got

/-- A header of fields that may break a bound, as a value of EthLib. -/
def genHeaderValue : Gen (Packet.Header × Bool) := do
  let cid := Gen.frequency [(6, genCid), (1, genByteList (.constant 21 30))]
  let d ← cid
  let s ← cid
  let token ← genByteList (.linear 0 4)
  let width ← Gen.nat (.constant 0 3)
  let w : Packet.PacketNumberLength := Fin.ofNat 4 width
  let number ← Gen.frequency [(6, genNumber width), (1, pure (256 ^ (width + 1))),
    (1, (256 ^ (width + 1) + ·) <$> genNatBits 40)]
  let length ← Gen.frequency [(6, (width + 1 + ·) <$> Gen.nat (.linear 0 40)),
    (1, Gen.nat (.constant 0 width))]
  let l : Varint := Fin.ofNat _ length
  let cids := d.length ≤ 20 && s.length ≤ 20
  let fits := number < 256 ^ (width + 1)
  let long := cids && fits && width + 1 ≤ length
  let big ← Gen.frequency [(4, genCid), (1, genByteList (.constant 21 255)),
    (1, genByteList (.constant 256 260))]
  let tag ← genVector 16
  let versions ← Gen.list (.linear 0 3) (UInt32.ofNat <$> genNatBits 32)
  Gen.element [
    (.initial (packed d) (packed s) (packed token) w l number, long),
    (.zeroRtt (packed d) (packed s) w l number, long),
    (.handshake (packed d) (packed s) w l number, long),
    (.oneRtt (packed d) (width % 2 == 0) (number % 2 == 0) w number, d.length ≤ 20 && fits),
    (.retry (packed d) (packed s) (packed token) tag (Fin.ofNat 16 number),
      cids && !token.isEmpty),
    (.versionNegotiation (packed big) (packed s) (Fin.ofNat 128 number) versions,
      big.length ≤ 255)]

/-- The writer refuses a header that breaks a bound of section 17, and no other.

What it writes, the reference reads as the same header. -/
def headerEncode (oracle : Oracle) : Property IO := propertyM do
  let (header, valid) ← forAllWith (fun (h, v) => s!"{showHeader h} {v}") genHeaderValue
  pure do
    cover 20 "a header within its bounds" valid
    cover 10 "a header that breaks a bound" (!valid)
    match Packet.encode header with
    | .error _ => ensure (!valid) "EthLib refuses a header within its bounds"
    | .ok bytes =>
      ensure valid "EthLib writes a header that breaks a bound"
      let cidLength := match header with
        | .oneRtt d .. => d.size
        | _ => 0
      (← ask oracle ["quic_header", toString cidLength, hex bytes]) === s!"{showHeader header} -"

/-! ### A datagram of coalesced packets, read back one at a time -/

/-- A datagram: the packets written so far, each a header and its payload, and how many were read.

A short header has no Length, so its packet ends the datagram. -/
structure Datagram where
  cidLength : Nat
  packets : List MadeHeader := []
  read : Nat := 0
  closed : Bool := false
  deriving Repr

/-- A step on a datagram. -/
inductive DatagramStep where
  | write (made : MadeHeader)
  | read

instance : Repr DatagramStep where
  reprPrec
    | .write made, _ => s!"WRITE({showMadeHeader made}, payload {made.payload})"
    | .read, _ => "READ"

/-- The bytes of a packet: its header, then a payload of the announced length. -/
def MadeHeader.packet (made : MadeHeader) : List UInt8 :=
  made.bytes ++ List.replicate made.payload 0xa5

/-- A long header with a payload that fits a datagram. -/
def genCoalesced : Gen MadeHeader := do
  let made ← Gen.choice [genLong 0, genLong 1, genLong 2]
  if made.payload ≤ 1200 then pure made else Gen.discard

/-- The model: a packet is read where the last one ended. -/
def datagramModel : Model Datagram DatagramStep where
  initState := do pure { cidLength := ← Gen.element [0, 4, 8, 20] }
  transitions s :=
    let short := (genShort.filter (·.cidLength == s.cidLength)).map DatagramStep.write
    Gen.frequency [(5, .write <$> genCoalesced), (1, short), (5, pure .read)]
  preconditions s
    | .write _ => !s.closed
    | .read => true
  apply s
    | .write made => { s with packets := s.packets ++ [made], closed := made.name == "onertt" }
    | .read => if s.read < s.packets.length then { s with read := s.read + 1 } else s

/-- The machine: EthLib's reader holds the unread bytes of the datagram.

It reads a header, and the Length of the header says where the next packet starts.

aioquic walks the same bytes and must find each packet at the same place. -/
def datagramMachine (oracle : Oracle) : StateMachine Datagram DatagramStep (List UInt8) IO where
  toModel := datagramModel
  initSut _ := pure []
  applySut unread before after step := do
    match step with
    | .write made => pure (unread ++ made.packet)
    | .read =>
      match before.packets[before.read]? with
      | none =>
        label "a read at the end of the datagram"
        unread === []
        readHeader before.cidLength unread === "error"
        pure unread
      | some made =>
        label s!"a read of {made.name}"
        let following := ((before.packets.drop (before.read + 1)).map (·.packet)).flatten
        match Packet.decode before.cidLength (packed unread) with
        | .error e => failWith s!"EthLib refuses a header that was built valid: {repr e}"
        | .ok (header, rest) =>
          showHeader header === made.text
          let payload := match header with
            | .initial _ _ _ w l _ | .zeroRtt _ _ w l _ | .handshake _ _ w l _ =>
              l.val - Packet.numberLength w
            | _ => rest.size
          let next := rest.toList.drop payload
          next === following
          next === ((after.packets.drop after.read).map (·.packet)).flatten
          -- aioquic finds the packet of the same length at this place.
          let lengths ← ask oracle ["quic_split", toString before.cidLength, hex (packed unread)]
          (lengths.splitOn ",").headD "" === toString (unread.length - next.length)
          pure next

/-! ## Integers, the Retry tag and the width of a packet number -/

/-- An integer at each of the four widths, as aioquic reads and writes it.

The reader takes the bytes of the integer and leaves the rest; a short input is refused. -/
def varintWidths (oracle : Oracle) : Property IO := propertyM do
  let width ← forAll (Gen.nat (.constant 0 3))
  let capacity := 64 * 256 ^ (2 ^ width - 1)
  let value ← forAll (Gen.frequency [(2, Gen.nat (.linear 0 63)), (1, pure (capacity - 1)),
    (1, pure (capacity / 256)), (3, Gen.nat (.constant 0 (capacity - 1)))])
  let tail ← forAll (genByteList (.linear 0 3))
  let cut ← forAll (Gen.nat (.constant 0 (2 ^ width)))
  pure do
    let w : Varint.Width := Fin.ofNat 4 width
    let v : Varint := Fin.ofNat _ value
    cover 8 "one byte" (width == 0)
    cover 8 "two bytes" (width == 1)
    cover 8 "four bytes" (width == 2)
    cover 8 "eight bytes" (width == 3)
    classify "the largest value of its width" (value + 1 == capacity)
    classify "a longer form than the value needs" (minWidth value < width)
    if h : v.val < Varint.capacity w then
      let bytes := Varint.encodeWith w v h
      bytes.toList === qv width value
      let answer ← ask oracle ["quic_var", hex (bytes ++ packed tail)]
      answer === s!"{value} {2 ^ width}"
      match Varint.decode (bytes ++ packed tail) with
      | .ok (got, rest) => do got.val === value; rest.toList === tail
      | .error e => failWith s!"EthLib refuses the integer: {repr e}"
      -- A short input is refused, with the count of bytes that the first byte asks for.
      if cut < 2 ^ width then
        match Varint.decode (bytes.extract 0 cut) with
        | .ok _ => failWith "EthLib reads an integer that was cut"
        | .error (.truncated needed available) =>
          needed === (if cut == 0 then 1 else 2 ^ width)
          available === cut
      -- The shortest form is aioquic's, and has the least width.
      (Varint.minWidth v).val === minWidth value
      hex (Varint.encode v) === (← ask oracle ["quic_var_enc", toString value])
    else failWith "the value does not fit its width"

/-- The Retry packet and its integrity tag are aioquic's, for every length of connection ID.

An original connection ID of more than 20 bytes is refused. -/
def retryTag (oracle : Oracle) : Property IO := propertyM do
  let odcid ← forAllWith (fun b => hex (packed b)) (Gen.frequency [(6, genCid),
    (1, genByteList (.constant 21 30))])
  let dcid ← forAllWith (fun b => hex (packed b)) genCid
  let scid ← forAllWith (fun b => hex (packed b)) genCid
  let token ← forAllWith (fun b => hex (packed b)) (genByteList (.linear 1 40))
  let unused ← forAll (Gen.nat (.constant 0 15))
  pure do
    cover 5 "an original connection ID of more than 20 bytes" (odcid.length > 20)
    classify "an original connection ID of no bytes" odcid.isEmpty
    classify "an original connection ID of 20 bytes" (odcid.length == 20)
    let blank : Vector UInt8 16 := Vector.replicate 16 0
    let header := Packet.Header.retry (packed dcid) (packed scid) (packed token) blank
      (Fin.ofNat 16 unused)
    match Packet.encode header with
    | .error e => failWith s!"EthLib does not write the Retry header: {repr e}"
    | .ok bytes =>
      let untagged := bytes.extract 0 (bytes.size - 16)
      match Protection.retryTag (packed odcid) untagged with
      | .error _ => ensure (odcid.length > 20) "EthLib refuses a valid original connection ID"
      | .ok tag =>
        ensure (odcid.length ≤ 20) "EthLib takes an original connection ID of more than 20 bytes"
        let want ← ask oracle ["quic_retry", hex (packed odcid), hex (packed dcid),
          hex (packed scid), hex (packed token), toString unused]
        hex (untagged ++ tag) === want

/-- A packet to seal: its header as bytes, the offset of its packet number, and what is wrong.

`fault` names the one rule that the header breaks, or says `none`. -/
structure Sealed where
  chacha : Bool
  header : List UInt8
  offset : Nat
  number : Nat
  payload : List UInt8
  fault : String
  deriving Repr

/-- A packet of each protected type, valid or with one fault in its clear header. -/
def genSealed : Gen Sealed := do
  let kind ← Gen.nat (.constant 0 3)
  let fault ← Gen.frequency ([(6, pure "none"), (3, pure "a reserved bit is set"),
    (1, pure "a Length one short"), (1, pure "a Length one long"), (1, pure "the fixed bit is 0"),
    (2, pure "a byte changed after sealing")] ++
    if kind == 0 then [(2, pure "an Initial packet under ChaCha20")] else [])
  let chacha ← if kind == 0 then pure (fault == "an Initial packet under ChaCha20") else Gen.bool
  let dcid ← genCid
  let scid ← genCid
  let token ← genByteList (.linear 0 5)
  let width ← Gen.nat (.constant 0 3)
  let number ← genNatBits 62
  -- The sample of header protection needs four bytes from the start of the packet number.
  let payload ← genByteList (.linear (3 - width) 40)
  let reserved ← if fault != "a reserved bit is set" then pure 0
    else if kind == 3 then Gen.element [0x08, 0x10, 0x18] else Gen.element [0x04, 0x08, 0x0c]
  let fixed := if fault == "the fixed bit is 0" then 0 else 0x40
  let length := width + 1 + payload.length + 16
  let length := if fault == "a Length one short" then length - 1
    else if fault == "a Length one long" then length + 1 else length
  let lengthBytes ← genQv length
  let tokenBytes ← genQv token.length
  let spin ← Gen.element [0, 0x20]
  let phase ← Gen.element [0, 4]
  let truncated := be (width + 1) (number % 256 ^ (width + 1))
  let clear := if kind == 3 then [UInt8.ofNat (fixed + spin + reserved + phase + width)] ++ dcid
    else longPrefix (0x80 + fixed + kind * 16 + reserved + width) 1 dcid scid ++
      (if kind == 0 then tokenBytes ++ token else []) ++ lengthBytes
  -- A short header has no Length, so those faults do not apply to it.
  let fault := if kind == 3 && (fault == "a Length one short" || fault == "a Length one long")
    then "none" else fault
  pure { chacha, header := clear ++ truncated, offset := clear.length, number, payload, fault }

/-- A packet that aioquic sealed opens as RFC 9001 section 5 and RFC 9000 section 17 say.

A valid one gives its header and its payload, as aioquic's own reader does.

A reserved bit that is set is reported as such, and only after the payload authenticated.

A wrong Length, a fixed bit of 0, and ChaCha20 on an Initial packet are refused. -/
def openSealed (oracle : Oracle) : Property IO := propertyM do
  let p ← forAll genSealed
  let secret ← forAllWith hexv (genVector 32)
  let flip ← forAll (Gen.nat (.linear 0 200))
  let behind ← forAll (Gen.nat (.linear 0 100))
  pure do
    let suite := if p.chacha then CipherSuite.chacha20Poly1305Sha256 else .aes128GcmSha256
    let name := if p.chacha then "chacha" else "aes"
    let .ok keys := packetKeys suite secret | failWith "EthLib gives no packet keys"
    let sealed ← ask oracle ["quic_seal", name, hexv secret, toString p.number,
      hex (packed p.header), hex (packed p.payload)]
    let some packet := unhex? sealed | failWith s!"the oracle answered {sealed}"
    let packet := if p.fault == "a byte changed after sealing" then
        let i := flip % packet.size
        packet.set! i (packet[i]! ^^^ 0x01)
      else packet
    -- The receiver expects the number, or one a little before it.
    let expected := p.number - behind
    let got := Protection.unprotect suite keys expected p.offset packet
    cover 20 "a valid packet" (p.fault == "none")
    label p.fault
    classify "ChaCha20-Poly1305" p.chacha
    match p.fault with
    | "none" =>
      match got with
      | .error e => failWith s!"EthLib refuses a valid packet: {repr e}"
      | .ok (header, payload) =>
        header.toList === p.header
        payload.toList === p.payload
        (← ask oracle ["quic_open", name, hexv secret, toString p.offset, toString expected,
          hex packet]) === s!"{hex header} {hex payload} {p.number}"
    | "a reserved bit is set" => got === .error .reservedBits
    | "a byte changed after sealing" =>
      ensure got.toOption.isNone "a packet with a changed byte opens"
    | _ => got === .error .header
    -- The sender: a header with a fault is not sealed, and a valid one is sealed as aioquic does.
    let number : Varint := Fin.ofNat _ p.number
    match Protection.protect suite keys number p.offset (packed p.header) (packed p.payload) with
    | .ok written =>
      ensure (p.fault == "none" || p.fault == "a byte changed after sealing")
        "EthLib seals a header with a fault"
      hex written === sealed
    | .error _ =>
      ensure (p.fault != "none" && p.fault != "a byte changed after sealing")
        "EthLib does not seal a valid packet"

/-- The width of a packet number is the least that section 17.1 permits.

With that width, a receiver whose next expected number is any that the sender allows for reads

the number back by Appendix A.3. -/
def numberWidth : Property IO := pureIO do
  let number ← forAll (Gen.frequency [(2, Gen.nat (.linear 0 300)), (2, genNatBits 62),
    (1, Gen.element [255, 256, 65535, 65536, 2 ^ 24 - 1, 2 ^ 24, 2 ^ 32 - 1, 2 ^ 32])])
  let gap ← forAll (Gen.frequency [(1, pure none), (3, some <$> Gen.frequency [
    (2, Gen.nat (.linear 0 300)), (1, pure 0),
    (1, Gen.element [127, 128, 129, 32767, 32768, 2 ^ 23 - 1, 2 ^ 23, 2 ^ 31 - 1, 2 ^ 31,
      2 ^ 31 + 1]), (1, genNatBits 33)])])
  let behind ← forAll (Gen.nat (.linear 0 100))
  -- The largest acknowledged number, when there is one: the number less the gap.
  let acked := gap.map (number - ·)
  let range := match acked with
    | none => number
    | some a => 2 * (number - a)
  let n : Varint := Fin.ofNat _ number
  let result := Packet.packetNumberWidth n (acked.map (Fin.ofNat _))
  classify "no acknowledgement yet" acked.isNone
  classify "the acknowledged number is not earlier" (acked == some number)
  classify "more than four bytes are needed" (range ≥ 256 ^ 4)
  match result with
  | .error _ => ensure (acked == some number || range ≥ 256 ^ 4) "a width was due"
  | .ok w =>
    collect (w.val + 1)
    ensure (acked != some number) "the acknowledged number is not earlier"
    -- More than twice the range, or the whole number: the least width that holds it.
    ensure (range < 256 ^ (w.val + 1)) "the width is too small"
    ensure (w.val == 0 || range ≥ 256 ^ w.val) "the width is not the least"
    -- A receiver has seen the acknowledged number at least, and the one before this at most.
    let seen := match acked with
      | none => 0
      | some a => min (number - 1) (a + behind)
    let expected := if acked.isNone then min number behind else seen + 1
    if acked.isSome || number < 256 ^ (w.val + 1) / 2 then
      Packet.decodePacketNumber w (number % 256 ^ (w.val + 1)) expected === .ok number

/-- The properties that must pass. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("quic: a frame of each type, RFC 9000 section 19",
    (frameDecode oracle (cases ≥ 1000)).withTests cases),
  ("quic: a payload of frames read back one at a time (`StateMachine`)",
    ((payloadMachine oracle).property (.linear 1 60)).withTests cases),
  ("quic: a header of each form, RFC 9000 section 17",
    (headerDecode oracle (cases ≥ 1000)).withTests cases),
  ("quic: the writer of headers and its bounds", (headerEncode oracle).withTests cases),
  ("quic: coalesced packets read back one at a time (`StateMachine`)",
    ((datagramMachine oracle).property (.linear 1 30)).withTests cases),
  ("quic: an integer at each of its four widths", (varintWidths oracle).withTests cases),
  ("quic: the Retry packet and its tag", (retryTag oracle).withTests (min cases 300)),
  ("quic: a sealed packet and the bits of its header", (openSealed oracle).withTests cases),
  ("quic: the width of a packet number", numberWidth.withTests cases)]

/-- The properties that fail by design: each is a finding. -/
def findings (_oracle : Oracle) (_cases : Nat) : List (String × Property IO) := []

end DecodersProperty.Quic

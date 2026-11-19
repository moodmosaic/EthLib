import Hedgehog
import Support
import Property.Networking.Common
import Property.Networking.Wire
import EthLib.Networking.Libp2p.MplexSession
import EthLib.Networking.Libp2p.YamuxSession

/-!
# Sessions as state machines: yamux, mplex and RLPx frames

These are the `StateMachine` tests of the layer.

The transitions are fixed by a specification, so they are one type.

A model written from the specification runs beside EthLib.

A yamux or mplex connection has two ends, and EthLib keeps the table of one end.

So the system under test is two tables, and every frame is sent by one and received by the other.

The model is one table of the connection, written from the source, which knows nothing of ends.
-/

open Hedgehog Support EthLib EthLib.Networking NetworkingProperty
open EthLib.Networking.Libp2p

namespace NetworkingProperty.Streams

/-! ## yamux -/

/-- A yamux stream of the connection: who opened it, and what each end has sent. -/
structure YStream where
  id : Nat
  clientOpened : Bool
  acked : Bool := false
  finClient : Bool := false
  finServer : Bool := false
  rstClient : Bool := false
  rstServer : Bool := false
  /-- The bytes that the client may still send. -/
  windowClient : Nat := 262144
  /-- The bytes that the server may still send. -/
  windowServer : Nat := 262144
  deriving Repr, BEq

/-- A frame on the connection, from one end. -/
structure YFrame where
  fromClient : Bool
  /-- 0 data, 1 window update, 2 ping, 3 go away. -/
  kind : Nat
  syn : Bool
  ack : Bool
  fin : Bool
  rst : Bool
  id : Nat
  length : Nat
  deriving Repr, BEq

/-- The model: the streams of the connection. -/
structure YModel where
  streams : List YStream := []
  deriving Repr

/-- The stream of an ID. -/
def YModel.find (m : YModel) (id : Nat) : Option YStream := m.streams.find? (·.id == id)

/-- The stream after a frame that its writer may send, or none for one it may not send.

Written from "Message Flow", "Flow Control" and "StreamID Field" of the yamux specification. -/
def yStep (m : YModel) (f : YFrame) : Option YStream := do
  if f.id = 0 then none
  let s ← if f.syn then
      -- A new stream takes a new ID of its opener's parity: odd for the client.
      if (m.find f.id).isSome || (f.id % 2 == 1) != f.fromClient then none
      else some ({ id := f.id, clientOpened := f.fromClient } : YStream)
    else m.find f.id
  -- Nothing follows a reset of either end.
  if s.rstClient || s.rstServer then none
  let opener := s.clientOpened == f.fromClient
  -- The end that did not open the stream answers with ACK or RST before anything else.
  if !s.acked && !opener && !f.ack && !f.rst then none
  if f.ack && (s.acked || opener) then none
  let s := if f.ack then { s with acked := true } else s
  let finSent := if f.fromClient then s.finClient else s.finServer
  let s ← if f.kind = 0 then
      -- Data: none after FIN, and no more than the window.
      let window := if f.fromClient then s.windowClient else s.windowServer
      if (finSent && f.length > 0) || window < f.length then none
      else some (if f.fromClient then { s with windowClient := window - f.length }
        else { s with windowServer := window - f.length })
    else
      -- A window update lets the other end send more.
      some (if f.fromClient then { s with windowServer := s.windowServer + f.length }
        else { s with windowClient := s.windowClient + f.length })
  if f.fin && finSent then none
  let s := if f.fin then
      (if f.fromClient then { s with finClient := true } else { s with finServer := true })
    else s
  pure (if f.rst then
      (if f.fromClient then { s with rstClient := true } else { s with rstServer := true })
    else s)

/-- The model after a frame: a frame that may not be sent changes nothing. -/
def yApply (m : YModel) (f : YFrame) : YModel :=
  if f.kind ≥ 2 then m
  else match yStep m f with
    | none => m
    | some s =>
      if (m.find s.id).isSome then ⟨m.streams.map fun t => if t.id == s.id then s else t⟩
      else ⟨m.streams ++ [s]⟩

/-- A frame for a state: mostly on a stream that exists or that may open, near its limits. -/
def genYFrame (m : YModel) : Gen YFrame := do
  let fromClient ← Gen.bool
  let known := m.streams.map (·.id)
  let fresh := (List.range 9).filter fun i => i ∉ known
  let id ← Gen.frequency ([(1, Gen.element [0, 1, 2, 2 ^ 32 - 1]),
    (3, Gen.nat (.constant 1 8))] ++
    (if known.isEmpty then [] else [(8, Gen.element known)]) ++
    (if fresh.isEmpty then [] else [(3, Gen.element fresh)]))
  let exists_ := id ∈ known
  let kind ← Gen.frequency [(5, pure 0), (3, pure 1), (1, pure 2), (1, pure 3)]
  let syn ← Gen.frequency [(if exists_ then 9 else 1, pure false),
    (if exists_ then 1 else 9, pure true)]
  let ack ← Gen.frequency [(2, pure false), (1, pure true)]
  let fin ← Gen.frequency [(6, pure false), (1, pure true)]
  let rst ← Gen.frequency [(12, pure false), (1, pure true)]
  let window := match m.find id with
    | some s => if fromClient then s.windowClient else s.windowServer
    | none => 262144
  let length ← Gen.frequency [(4, Gen.nat (.linear 0 1000)), (1, pure 0),
    (2, (window + 1 - ·) <$> Gen.nat (.constant 0 2)), (1, Gen.nat (.linear 0 300000))]
  pure ⟨fromClient, kind, syn, ack, fin, rst, id, length % 2 ^ 32⟩

/-- The frame as EthLib takes it. -/
def YFrame.frame (f : YFrame) : Yamux.Frame where
  kind := match f.kind with | 0 => .data | 1 => .windowUpdate | 2 => .ping | _ => .goAway
  flags := (if f.syn then 1 else 0) ||| (if f.ack then 2 else 0) ||| (if f.fin then 4 else 0) |||
    (if f.rst then 8 else 0)
  streamId := UInt32.ofNat f.id
  length := UInt32.ofNat f.length
  data := .empty

/-- One end's view of a model stream: the fields of EthLib's `Stream`. -/
def YStream.view (s : YStream) (client : Bool) : Yamux.Stream where
  localOpened := s.clientOpened == client
  acked := s.acked
  localClosed := if client then s.finClient else s.finServer
  remoteClosed := if client then s.finServer else s.finClient
  localReset := if client then s.rstClient else s.rstServer
  remoteReset := if client then s.rstServer else s.rstClient
  sendWindow := if client then s.windowClient else s.windowServer
  recvWindow := if client then s.windowServer else s.windowClient

/-- The yamux machine: the two ends of a connection against the model of the connection. -/
def yamux : StateMachine YModel YFrame (Yamux.Session × Yamux.Session) IO where
  initState := pure {}
  transitions := genYFrame
  apply := yApply
  initSut _ := pure ({ isClient := true }, { isClient := false })
  applySut sut _ f := do
    let (client, server) := sut
    let frame := f.frame
    let (sender, receiver) := if f.fromClient then (client, server) else (server, client)
    let sent := Yamux.send sender frame
    let received := Yamux.receive receiver frame
    if f.kind ≥ 2 then
      -- A ping or a go-away is always taken, and only a ping with SYN is answered.
      let .ok sender' := sent | failWith "a ping or go-away is refused by its sender"
      let .ok (receiver', replies) := received | failWith "a ping or go-away is refused"
      replies.length === (if f.kind = 2 && f.syn then 1 else 0)
      ensure (receiver'.goneAway == (receiver.goneAway || f.kind = 3)) "goneAway"
      ensure (sender'.streams == sender.streams && receiver'.streams == receiver.streams) "streams"
      pure (if f.fromClient then (sender', receiver') else (receiver', sender'))
    else
      match sent, received with
      | .ok sender', .ok (receiver', _) =>
        pure (if f.fromClient then (sender', receiver') else (receiver', sender'))
      | .error _, .error _ => pure sut
      | .ok _, .error e => failWith s!"the receiver refuses a frame its sender may send: {repr e}"
      | .error e, .ok _ =>
        -- Frames that crossed a reset of the receiver are taken and dropped; no others.
        ensure (((receiver.find? frame.streamId).map (·.localReset)).getD false && !f.syn)
          s!"the receiver takes a frame its sender may not send: {repr e}"
        pure sut
  invariants sut m := do
    let (client, server) := sut
    -- Each end's table is its view of the model's streams, in the order they opened.
    for (session, isClient) in [(client, true), (server, false)] do
      let want := m.streams.map fun s => (UInt32.ofNat s.id, s.view isClient)
      ensure (session.streams == want)
        (s!"the {if isClient then "client" else "server"} holds {repr session.streams}, " ++
          s!"the model {repr want}")

/-! ## mplex -/

/-- An mplex stream of the connection: its ID, its opener, and what each end has done. -/
structure MStream where
  id : Nat
  clientOpened : Bool
  closedClient : Bool := false
  closedServer : Bool := false
  resetClient : Bool := false
  resetServer : Bool := false
  deriving Repr, BEq

/-- A frame on the connection: its writer, what it does, its stream, and its stream's opener. -/
structure MFrame where
  fromClient : Bool
  /-- 0 new stream, 1 message, 2 close, 3 reset. -/
  action : Nat
  id : Nat
  /-- Whether the frame names a stream that its writer opened. -/
  initiator : Bool
  deriving Repr, BEq

/-- The model of an mplex connection. -/
structure MModel where
  streams : List MStream := []
  deriving Repr

/-- The stream of a frame: by its ID and by who opened it. -/
def MModel.find (m : MModel) (f : MFrame) : Option MStream :=
  m.streams.find? fun s => s.id == f.id && s.clientOpened == (f.initiator == f.fromClient)

/-- The stream after a frame that its writer may send, by "Protocol" of the mplex specification.

A writer writes nothing after its close, nor after a reset of either end.

The exception is that it may reset a stream it has closed. -/
def mStep (m : MModel) (f : MFrame) : Option MStream :=
  match f.action, m.find f with
  | 0, none => some { id := f.id, clientOpened := f.fromClient }
  | 0, some _ => none
  | _, none => none
  | action, some s =>
    let closed := if f.fromClient then s.closedClient else s.closedServer
    let reset := s.resetClient || s.resetServer
    if action = 1 then (if closed || reset then none else some s)
    else if action = 2 then
      if closed || reset then none
      else some (if f.fromClient then { s with closedClient := true }
        else { s with closedServer := true })
    else
      if reset then none
      else some (if f.fromClient then { s with resetClient := true }
        else { s with resetServer := true })

/-- The model after a frame. -/
def mApply (m : MModel) (f : MFrame) : MModel :=
  match mStep m f with
  | none => m
  | some s =>
    if (m.find f).isSome then
      ⟨m.streams.map fun t => if t.id == s.id && t.clientOpened == s.clientOpened then s else t⟩
    else ⟨m.streams ++ [s]⟩

/-- The frame as EthLib takes it; a new stream is always its writer's. -/
def MFrame.frame (f : MFrame) : Mplex.Frame where
  streamId := f.id
  flag := match f.action, f.initiator with
    | 0, _ => .newStream
    | 1, true => .messageInitiator
    | 1, false => .messageReceiver
    | 2, true => .closeInitiator
    | 2, false => .closeReceiver
    | _, true => .resetInitiator
    | _, false => .resetReceiver
  data := .empty

/-- A frame: on a few IDs, so that streams are used again and both ends open the same ID. -/
def genMFrame (_ : MModel) : Gen MFrame := do
  let action ← Gen.frequency [(3, pure 0), (5, pure 1), (2, pure 2), (1, pure 3)]
  let initiator ← if action = 0 then pure true else Gen.bool
  pure ⟨← Gen.bool, action, ← Gen.nat (.constant 0 4), initiator⟩

/-- One end's view of a model stream. -/
def MStream.view (s : MStream) (client : Bool) : Mplex.StreamKey × Mplex.StreamState :=
  ((s.id, s.clientOpened == client),
    { localClosed := if client then s.closedClient else s.closedServer
      remoteClosed := if client then s.closedServer else s.closedClient
      localReset := if client then s.resetClient else s.resetServer
      remoteReset := if client then s.resetServer else s.resetClient })

/-- The mplex machine: the two ends of a connection against the model of the connection. -/
def mplex : StateMachine MModel MFrame (Mplex.Streams × Mplex.Streams) IO where
  initState := pure {}
  transitions := genMFrame
  apply := mApply
  initSut _ := pure ([], [])
  applySut sut _ f := do
    let (client, server) := sut
    let (sender, receiver) := if f.fromClient then (client, server) else (server, client)
    match Mplex.send sender f.frame, Mplex.receive receiver f.frame with
    | .ok sender', .ok receiver' =>
      pure (if f.fromClient then (sender', receiver') else (receiver', sender'))
    | .error _, .error _ => pure sut
    | .ok _, .error e => failWith s!"the receiver refuses a frame its sender may send: {repr e}"
    | .error e, .ok _ =>
      -- Frames that crossed a reset of the receiver are taken and dropped; no others.
      let key := Mplex.streamKey true f.frame
      ensure (((Mplex.Streams.find? receiver key).map (·.localReset)).getD false && f.action ≠ 0)
        s!"the receiver takes a frame its sender may not send: {repr e}"
      pure sut
  invariants sut m := do
    for (streams, isClient) in [(sut.1, true), (sut.2, false)] do
      let want := m.streams.map (·.view isClient)
      ensure (streams == want)
        (s!"the {if isClient then "client" else "server"} holds {repr streams}, " ++
          s!"the model {repr want}")

/-! ## RLPx frames -/

/-- What one end of an RLPx session does next. -/
inductive FrameStep where
  /-- The initiator, or the recipient, sends a frame with this data. -/
  | send (initiator : Bool) (data : ByteArray)
  /-- A frame with one byte changed arrives: it must be refused. -/
  | corrupt (initiator : Bool) (data : ByteArray) (at_ : Nat)
  /-- A frame cut short arrives: it must be refused. -/
  | cut (initiator : Bool) (data : ByteArray) (by_ : Nat)
  deriving Repr

/-- The model of a session: what each end has sent, which the other must have read. -/
structure FrameModel where
  session : Wire.Session
  fromInitiator : List ByteArray := []
  fromRecipient : List ByteArray := []
  deriving Repr

/-- The four directions of a session: egress and ingress of both ends, and what was read. -/
structure FrameSut where
  initiatorOut : Rlpx.FrameState
  recipientIn : Rlpx.FrameState
  recipientOut : Rlpx.FrameState
  initiatorIn : Rlpx.FrameState
  readByRecipient : List ByteArray := []
  readByInitiator : List ByteArray := []

/-- A direction as text: its counter and its MAC. -/
def showState (s : Rlpx.FrameState) : String :=
  s!"{hexv s.counter} {hex (Rlpx.macBytes s.mac)}"

/-- The RLPx machine: frames written by one end are read by the other, in order.

A changed or cut frame is refused and leaves the reader where it was. -/
def rlpxFrames : StateMachine FrameModel FrameStep FrameSut IO where
  initState := (fun s => { session := s }) <$> Wire.genSession
  transitions _ := Gen.frequency [
    (6, Gen.zipWith FrameStep.send Gen.bool Wire.genFrameData),
    (2, do pure (.corrupt (← Gen.bool) (← Wire.genFrameData) (← Gen.nat (.linear 0 200)))),
    (1, do pure (.cut (← Gen.bool) (← Wire.genFrameData) (← Gen.nat (.linear 1 40))))]
  apply m
    | .send true data => { m with fromInitiator := m.fromInitiator ++ [data] }
    | .send false data => { m with fromRecipient := m.fromRecipient ++ [data] }
    | _ => m
  initSut m :=
    let a := { m.session with initiator := true }.secrets
    let b := { m.session with initiator := false }.secrets
    pure ⟨a.egress, b.ingress, b.egress, a.ingress, [], []⟩
  applySut sut _ step := do
    let (initiator, data) := match step with
      | .send i d | .corrupt i d _ | .cut i d _ => (i, d)
    let (out, in_) := if initiator then (sut.initiatorOut, sut.recipientIn)
      else (sut.recipientOut, sut.initiatorIn)
    let .ok (frame, out') := Rlpx.writeFrame out data | failWith "writeFrame"
    match step with
    | .send .. =>
      -- A second frame follows, so the reader must stop at the end of the first.
      let .ok (got, in', rest) := Rlpx.readFrame in_ (frame ++ ⟨#[1, 2, 3]⟩)
        | failWith "the reader refuses a frame of the writer"
      hex got === hex data
      hex rest === "010203"
      showState in' === showState out'
      pure (if initiator then
        { sut with initiatorOut := out', recipientIn := in',
                   readByRecipient := sut.readByRecipient ++ [got] }
        else { sut with recipientOut := out', initiatorIn := in',
                        readByInitiator := sut.readByInitiator ++ [got] })
    | .corrupt _ _ at_ =>
      let i := at_ % frame.size
      ensure (Rlpx.readFrame in_ (frame.set! i (frame[i]! ^^^ 0x40))).toOption.isNone
        s!"a frame with byte {i} changed is read"
      pure sut
    | .cut _ _ by_ =>
      let short := frame.extract 0 (frame.size - by_ % frame.size - 1)
      ensure (Rlpx.readFrame in_ short).toOption.isNone
        "a cut frame is read"
      pure sut
  invariants sut m := do
    ensure (sut.readByRecipient == m.fromInitiator) "the recipient read other frames"
    ensure (sut.readByInitiator == m.fromRecipient) "the initiator read other frames"

/-- The state machines of this module. -/
def passing (cases : Nat) : List (String × Property IO) :=
  [("yamux: two ends of a connection against a model (StateMachine)",
      (yamux.property (.linear 1 80)).withTests cases),
   ("mplex: two ends of a connection against a model (StateMachine)",
      (mplex.property (.linear 1 60)).withTests cases),
   ("rlpx: frames of a session, both directions (StateMachine)",
      (rlpxFrames.property (.linear 1 20)).withTests (min cases 300))]

end NetworkingProperty.Streams

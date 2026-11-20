import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Networking.Libp2p.Multistream
import EthLib.Networking.Libp2p.Upgrade

/-!
# A negotiation of multistream-select, and the upgrade of a connection

A dialer and a listener exchange messages over two wires of bytes, read in any order.

A model beside them is written from "Protocol" of multistream-select.

Where the text fixes no reaction, the model follows what the module documents.
-/

open Hedgehog Support EthLib EthLib.Networking EthLib.Networking.Libp2p

namespace DecodersProperty.Libp2p.Negotiation

open DecodersProperty

/-- The header that both peers send first. -/
def header : ByteArray := "/multistream/1.0.0".toUTF8

/-- The answer to a protocol that the listener does not support. -/
def na : ByteArray := "na".toUTF8

/-- The protocols that a peer may name, few enough that two lists often share one. -/
def protocols : List String :=
  ["/noise", "/yamux/1.0.0", "/mplex/6.7.0", "/tls/1.0.0", "/meshsub/1.1.0", "ls"]

/-- A list of protocols, in an order, with a repeat now and then. -/
def genProtocols (most : Nat) : Gen (List ByteArray) := do
  let count ← Gen.frequency [(1, pure 0), (8, Gen.nat (.constant 1 most))]
  (·.map String.toUTF8) <$> Gen.list (.singleton count) (Gen.element protocols)

/-- The model of the dialer, by the index of the proposal it waits on. -/
inductive DialerModel where
  | awaitHeader (index : Nat)
  | awaitAnswer (index : Nat)
  | agreed (index : Nat)
  | failed
  | unexpected (reply : ByteArray)
  | aborted
  deriving DecidableEq

/-- The model of the listener. -/
inductive ListenerModel where
  | awaitHeader
  | awaitProposal
  | agreed (protocol : ByteArray)
  | aborted
  deriving DecidableEq

/-- Two peers, the bytes in flight between them, and the model of each. -/
structure Session where
  proposals : List ByteArray
  supported : List ByteArray
  dialer : Multistream.Dialer
  listener : Multistream.Listener
  /-- The bytes on the wire to the listener, and the messages they hold. -/
  toListener : List UInt8
  toListenerModel : List ByteArray
  /-- The bytes on the wire to the dialer, and the messages they hold. -/
  toDialer : List UInt8
  toDialerModel : List ByteArray
  dialerModel : DialerModel
  listenerModel : ListenerModel
  /-- Whether a message was put on a wire that neither peer sent. -/
  faulted : Bool
  /-- The messages each peer sent, for the counts. -/
  dialerSent : Nat
  listenerSent : Nat

/-- The bytes of messages on a wire, by an encoder written from the text. -/
def frame (message : ByteArray) : List UInt8 :=
  let size := message.size + 1
  -- Every message here is shorter than 127 bytes, so its length is one byte.
  [UInt8.ofNat size] ++ message.data.toList ++ [0x0a]

/-- Whether EthLib's dialer is in the state of the model. -/
def dialerAgrees (s : Session) : Bool :=
  match s.dialer, s.dialerModel with
  | .awaitHeader proposed rest, .awaitHeader i =>
    s.proposals[i]? == some proposed && rest == s.proposals.drop (i + 1)
  | .awaitAnswer proposed rest, .awaitAnswer i =>
    s.proposals[i]? == some proposed && rest == s.proposals.drop (i + 1)
  | .agreed protocol, .agreed i => s.proposals[i]? == some protocol
  | .failed, .failed => true
  | .unexpected reply, .unexpected expected => reply == expected
  | .aborted, .aborted => true
  | _, _ => false

/-- Whether EthLib's listener is in the state of the model. -/
def listenerAgrees (s : Session) : Bool :=
  match s.listener, s.listenerModel with
  | .awaitHeader supported, .awaitHeader => supported == s.supported
  | .awaitProposal supported, .awaitProposal => supported == s.supported
  | .agreed protocol, .agreed expected => protocol == expected
  | .aborted, .aborted => true
  | _, _ => false

/-- The start of a session: each peer has sent its header, and the dialer its first proposal. -/
def start (proposals supported : List ByteArray) : Session :=
  let (dialer, fromDialer) := Multistream.Dialer.start proposals
  let (listener, fromListener) := Multistream.Listener.start supported
  -- The model: both send the header, and the dialer its first proposal without waiting.
  let dialerFirst := match proposals with
    | [] => []
    | first :: _ => [header, first]
  { proposals, supported, dialer, listener
    toListener := fromDialer.flatMap Multistream.encode
    toListenerModel := dialerFirst
    toDialer := fromListener.flatMap Multistream.encode
    toDialerModel := [header]
    dialerModel := if proposals.isEmpty then .failed else .awaitHeader 0
    listenerModel := .awaitHeader
    faulted := false
    dialerSent := fromDialer.length
    listenerSent := fromListener.length }

/-- A session of generated peers. -/
def genSession : Gen Session :=
  Gen.zipWith start (genProtocols 4) (genProtocols 4)

/-- A session whose listener sent another first message than its header, now and then. -/
def genSessionWithStrays : Gen Session := do
  let s ← genSession
  let first ← Gen.frequency [(5, pure none), (1, some <$> Gen.element ["na", "/noise", ""])]
  pure (match first with
    | none => s
    | some text =>
      { s with toDialer := Multistream.encode text.toUTF8, toDialerModel := [text.toUTF8]
               faulted := true })

/-- What both peers must hold after every command. -/
def invariants (s : Session) : TestT IO Unit := do
  ensure (dialerAgrees s) "the dialer is not in the state of the model"
  ensure (listenerAgrees s) "the listener is not in the state of the model"
  -- The wires hold the messages of the model, in the framing of the text.
  s.toListener === s.toListenerModel.flatMap frame
  s.toDialer === s.toDialerModel.flatMap frame
  -- A listener agrees only on a protocol it supports.
  if let .agreed protocol := s.listener then
    ensure (s.supported.contains protocol) "the listener agreed on a protocol it does not support"
  -- A dialer agrees only on a protocol it proposed.
  if let .agreed protocol := s.dialer then
    ensure (s.proposals.contains protocol) "the dialer agreed on a protocol it did not propose"

/-- The listener reads the next message on its wire. -/
def listenerReads (s : Session) : TestT IO Session := do
  let expected :: restModel := s.toListenerModel | failWith "nothing to read"
  let .ok (message, rest) := Multistream.decode s.toListener
    | failWith "the listener cannot read its wire"
  message === expected
  let (listener, sent) := Multistream.listen s.listener message
  -- The model, from "Protocol": the header first, then an echo or `na` for each proposal.
  let (listenerModel, modelSent) := match s.listenerModel with
    | .awaitHeader => if message == header then (ListenerModel.awaitProposal, [])
      else (.aborted, [])
    | .awaitProposal => if s.supported.contains message then (.agreed message, [message])
      else (.awaitProposal, [na])
    | state => (state, [])
  sent === modelSent
  let s := { s with listener, listenerModel, toListener := rest, toListenerModel := restModel
                    toDialer := s.toDialer ++ sent.flatMap Multistream.encode
                    toDialerModel := s.toDialerModel ++ modelSent
                    listenerSent := s.listenerSent + sent.length }
  invariants s
  pure s

/-- The dialer reads the next message on its wire. -/
def dialerReads (s : Session) : TestT IO Session := do
  let expected :: restModel := s.toDialerModel | failWith "nothing to read"
  let .ok (message, rest) := Multistream.decode s.toDialer
    | failWith "the dialer cannot read its wire"
  message === expected
  let (dialer, sent) := Multistream.dial s.dialer message
  -- The model: the header, then an echo agrees and `na` moves to the next proposal.
  let (dialerModel, modelSent) := match s.dialerModel with
    | .awaitHeader i => if message == header then (DialerModel.awaitAnswer i, [])
      else (.aborted, [])
    | .awaitAnswer i =>
      if s.proposals[i]? == some message then (.agreed i, [])
      else if message == na then
        match s.proposals[i + 1]? with
        | some next => (.awaitAnswer (i + 1), [next])
        | none => (.failed, [])
      else (.unexpected message, [])
    | state => (state, [])
  sent === modelSent
  let s := { s with dialer, dialerModel, toDialer := rest, toDialerModel := restModel
                    toListener := s.toListener ++ sent.flatMap Multistream.encode
                    toListenerModel := s.toListenerModel ++ modelSent
                    dialerSent := s.dialerSent + sent.length }
  invariants s
  pure s

/-- The listener reads one message. -/
structure ListenerReads where

instance : Command ListenerReads Session Bool IO where
  check _ _ s := !s.toListenerModel.isEmpty
  label _ := "LISTENER_READS"
  build _ := pure {}
  apply _ _ s := listenerReads s

/-- The dialer reads one message. -/
structure DialerReads where

instance : Command DialerReads Session Bool IO where
  check _ _ s := !s.toDialerModel.isEmpty
  label _ := "DIALER_READS"
  build _ := pure {}
  apply _ _ s := dialerReads s

/-- Both peers read until the wires are empty, one of them first whenever both can. -/
structure Drain where
  dialerFirst : Bool
  deriving Repr

/-- Read until quiet; each read takes a unit of fuel. -/
def drain (dialerFirst : Bool) : Nat → Session → TestT IO Session
  | 0, s => pure s
  | fuel + 1, s =>
    let dialer := !s.toDialerModel.isEmpty
    let listener := !s.toListenerModel.isEmpty
    if dialer && (dialerFirst || !listener) then do drain dialerFirst fuel (← dialerReads s)
    else if listener then do drain dialerFirst fuel (← listenerReads s)
    else pure s

instance : Command Drain Session Bool IO where
  label c := s!"DRAIN(dialer first: {c.dialerFirst})"
  build _ := Drain.mk <$> Gen.bool
  apply _ c s := drain c.dialerFirst 40 s

/-- A message on a wire that the other peer did not send. -/
structure Stray where
  toDialer : Bool
  message : String
  deriving Repr

instance : Command Stray Session Bool IO where
  label c := s!"STRAY({repr c})"
  build _ := Stray.mk <$> Gen.bool <*>
    Gen.element (protocols ++ ["na", "/multistream/1.0.0", "", "/unknown"])
  apply _ c s := do
    let message := c.message.toUTF8
    let s := if c.toDialer then
        { s with toDialer := s.toDialer ++ Multistream.encode message
                 toDialerModel := s.toDialerModel ++ [message], faulted := true }
      else
        { s with toListener := s.toListener ++ Multistream.encode message
                 toListenerModel := s.toListenerModel ++ [message], faulted := true }
    invariants s
    pure s

/-- Both wires are empty: the negotiation is over, and its outcome is that of the text. -/
structure Settled where

instance : Command Settled Session Bool IO where
  check _ _ s := s.toListenerModel.isEmpty && s.toDialerModel.isEmpty
  label _ := "SETTLED"
  build _ := pure {}
  apply strays _ s := do
    -- A scenario with stray messages settles in other ways, so it asks for no share of these.
    let reach (minimum : Nat) (name : String) (reached : Bool) : TestT IO Unit :=
      if strays then classify name reached else cover minimum name reached
    let plain := !s.faulted && !s.proposals.contains na
    classify "settled with no stray message" plain
    classify "settled after a stray message" s.faulted
    if plain then
      -- The dialer agrees on its first proposal that the listener supports, and so does it.
      let common := s.proposals.find? s.supported.contains
      let tried := match s.proposals.findIdx? s.supported.contains with
        | some i => i + 1
        | none => s.proposals.length
      match common with
      | some protocol =>
        ensure (s.dialer == .agreed protocol) "the dialer did not agree on the first common one"
        ensure (s.listener == .agreed protocol) "the listener did not agree on it"
        reach 6 "agreed on the first proposal" (tried == 1)
        reach 3 "agreed after an answer of na" (tried > 1)
      | none =>
        ensure (s.dialer == .failed) "the dialer did not fail with nothing in common"
        reach 3 "failed: no proposal" s.proposals.isEmpty
        reach 8 "failed: nothing in common" !s.proposals.isEmpty
        if !s.proposals.isEmpty then
          ensure (s.listener == .awaitProposal s.supported) "the listener is not waiting"
      -- The dialer sends its header and one message for each proposal it tried.
      s.dialerSent === (if s.proposals.isEmpty then 0 else tried + 1)
      -- The listener sends its header and one answer for each proposal it read.
      s.listenerSent === (if s.proposals.isEmpty then 1 else tried + 1)
      -- The driver of the module reaches the same end.
      Multistream.negotiate s.proposals s.supported === common
    else
      classify "the dialer stopped on an unexpected answer"
        (match s.dialer with | .unexpected _ => true | _ => false)
      classify "the dialer aborted" (s.dialer == .aborted)
      classify "the listener aborted" (s.listener == .aborted)
      classify "both agreed after a stray message" (match s.dialer, s.listener with
        | .agreed a, .agreed b => a == b
        | _, _ => false)
    pure s

/-- A negotiation with its messages read in any order. -/
def negotiation (strays : Bool) : Property IO :=
  scenarioFrom (if strays then genSessionWithStrays else genSession) .madhouse strays
    ([Command.gen ListenerReads, Command.gen ListenerReads, Command.gen DialerReads,
      Command.gen DialerReads, Command.gen Drain, Command.gen Settled, Command.gen Settled] ++
      if strays then [Command.gen Stray] else [])
    (.linear 1 60) fun s => do
      annotate s!"proposals {repr (s.proposals.map hex)}, supported {repr (s.supported.map hex)}"
      invariants s
      pure s

/-- The driver of the module gives the outcome of the text, for any two lists.

The dialer agrees on its first proposal that the listener supports, or on nothing. -/
def outcome : Property IO := pureIO do
  let proposals ← forAllWith (fun l => toString (repr (l.map hex))) (genProtocols 5)
  let supported ← forAllWith (fun l => toString (repr (l.map hex))) (genProtocols 4)
  let common := proposals.find? supported.contains
  cover 30 "a protocol in common" common.isSome
  cover 10 "nothing in common" (common.isNone && !proposals.isEmpty)
  cover 3 "no proposal" proposals.isEmpty
  cover 10 "the first proposal is refused" (match proposals with
    | first :: _ => !supported.contains first && common.isSome
    | [] => false)
  Multistream.negotiate proposals supported === common
  let (dialer, listener) := Multistream.run proposals supported
  match common with
  | some protocol =>
    ensure (dialer == .agreed protocol && listener == .agreed protocol) "the peers disagree"
  | none => ensure (dialer == .failed) "the dialer did not fail"
  -- The answer to one proposal is its echo or `na`.
  for proposal in proposals do
    Multistream.respond supported proposal ===
      (if supported.contains proposal then proposal else na)
    Multistream.supports supported proposal === supported.contains proposal

/-- The upgrade of a TCP connection: Noise, then yamux when both peers support it, else mplex.

The consensus layer requires mplex and lets a node put yamux before it. -/
def upgrade : Property IO := pureIO do
  let dialer ← forAll Gen.bool
  let listener ← forAll Gen.bool
  classify "both support yamux" (dialer && listener)
  classify "one supports yamux" (dialer != listener)
  classify "neither supports yamux" (!dialer && !listener)
  let muxer := if dialer && listener then "/yamux/1.0.0" else "/mplex/6.7.0"
  Upgrade.upgrade ⟨dialer⟩ ⟨listener⟩ === some ("/noise".toUTF8, muxer.toUTF8)
  -- The first bytes of a dialer on the raw connection, from the text of each protocol.
  let first := (Multistream.Dialer.start Upgrade.securityProposals).2.flatMap Multistream.encode
  hex (packed first) === hex ("\x13/multistream/1.0.0\n\x07/noise\n".toUTF8)

/-- The properties of the negotiation. -/
def passing (cases : Nat) : List (String × Property IO) := [
  ("multistream: a negotiation, its messages read in any order (Command, madhouse)",
    (negotiation false).withTests cases),
  ("multistream: a negotiation with stray messages (Command, madhouse)",
    (negotiation true).withTests cases),
  ("multistream: the outcome is the first proposal that the listener supports",
    outcome.withTests cases),
  ("upgrade: Noise, then yamux when both support it", upgrade.withTests (min cases 100))]

end DecodersProperty.Libp2p.Negotiation

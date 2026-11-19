import Hedgehog
import Support
import Property.Networking.Common
import EthLib.Networking.Gossip.Router

/-!
# The gossipsub router, as commands in madhouse mode

These are the `Command` tests of the layer: each event that a router sees is a type of its own
with a `Command` instance, and a scenario draws random sequences of them.

The state holds EthLib's router and a model beside it.
The model is written from gossipsub v1.0 and v1.1: what was seen and when, what the message
cache holds and how old it is, every backoff, the subscriptions of the peers, and the fanout.
Each command says what the specification asks of the router's answer, and then every
invariant is checked: no explicit peer and no peer within a backoff is in a mesh, the caches
answer as the model does, the backoffs are the model's.

Where the specification lets the router choose (which peers to graft, to keep, to gossip to),
the commands check the bounds on the choice and that it could not have taken more.

The parameters are small, so that a few peers cross every bound: D = 3, D_low = 2, D_high = 4.
-/

open Hedgehog Support EthLib EthLib.Networking EthLib.Networking.Gossip NetworkingProperty

namespace NetworkingProperty.Router

/-! ## The world: fixed parameters, peers and scores -/

def params : GossipsubParameters :=
  { D := 3, D_low := 2, D_high := 4, D_lazy := 1, heartbeat_interval_ms := 700, fanout_ttl := 3,
    mcache_len := 3, mcache_gossip := 2, seen_ttl := 2 }

def choices (flood : Bool) : ClientChoices :=
  { dScore := 1, dOut := 1, gossipFactor := (1, 4), gossipRoundUp := true, floodPublish := flood,
    pruneBackoffS := 2, unsubscribeBackoffS := 1 }

/-- The extension of a backoff by a GRAFT within it, and the backoff of a bare PRUNE, in ms. -/
def graftPenaltyMs : Nat := 1500
def bareBackoffMs : Nat := 2500

/-- The peers are numbered 0 to 11, and a peer ID is its number in one byte. -/
def peer (i : Nat) : PeerId := ⟨#[UInt8.ofNat i]⟩
def index (p : PeerId) : Nat := (p.data.getD 0 0).toNat
def peerCount : Nat := 12

/-- Peers 6 and 7 are explicit; 0, 1, 2 and 8 are on outbound connections. -/
def explicitPeers : List Nat := [6, 7]
def outboundPeers : List Nat := [0, 1, 2, 8]

/-- The scores: 8 is negative, 9 is below the gossip threshold too, 10 below the publish
threshold too, and 11 is graylisted. -/
def standing (p : PeerId) : Standing :=
  let i := index p
  { negative := 8 ≤ i, belowGossip := 9 ≤ i, belowPublish := 10 ≤ i, belowGraylist := 11 ≤ i }

/-- A message is two bytes: the first is its ID, the second says how it validates. -/
def message (topic : String) (key verdict : UInt8) : Message := { data := ⟨#[key, verdict]⟩, topic }
def keyOf (m : Message) : UInt8 := m.data.data.getD 0 0
def idOf (key : UInt8) : MessageId := Vector.replicate 20 key
def msgId (m : Message) : MessageId := idOf (keyOf m)
def validate (m : Message) : ValidationResult :=
  match m.data.data.getD 1 0 with
  | 1 => .reject "second byte 1"
  | 2 => .ignore "second byte 2"
  | _ => .accept

/-- A better peer has a smaller number. -/
def rank (a b : PeerId) : Bool := index a ≤ index b

def topicNames : List String := ["a", "b", "c"]
def keyCount : Nat := 6

/-- EthLib's router beside the model. -/
structure World where
  router : RouterState := { explicit := explicitPeers.map peer, outbound := outboundPeers.map peer }
  /-- The time in milliseconds. -/
  now : Nat := 10000
  /-- Whether this node floods what it publishes. -/
  flood : Bool := false
  /-- The topics this node joined. -/
  joined : List String := []
  /-- The subscriptions that peers announced. -/
  subs : List (Nat × String) := []
  /-- When each message ID was first seen. -/
  seen : List (UInt8 × Nat) := []
  /-- The cached messages, newest first, each with the heartbeats since it arrived. -/
  cache : List (UInt8 × Message × Nat) := []
  /-- The end of each backoff. -/
  backoff : List ((String × Nat) × Nat) := []
  /-- The time of the last publish to each topic of the fanout. -/
  fanout : List (String × Nat) := []
  /-- The messages delivered to the application, for the report. -/
  delivered : Nat := 0

instance : Inhabited World := ⟨{}⟩

namespace World

def backoffEnd (w : World) (t : String) (i : Nat) : Nat := (w.backoff.lookup (t, i)).getD 0
def setBackoff (w : World) (t : String) (i ends : Nat) : World :=
  { w with backoff := ((t, i), ends) :: w.backoff.filter (·.1 != (t, i)) }
def raiseBackoff (w : World) (t : String) (i ends : Nat) : World :=
  w.setBackoff t i (max (w.backoffEnd t i) ends)
def isSeen (w : World) (key : UInt8) : Bool :=
  w.seen.any fun (k, t) => k == key && w.now < t + params.seen_ttl * 1000
def cached (w : World) (key : UInt8) : Option Message :=
  (w.cache.find? (·.1 == key)).map (·.2.1)
def subscribed (w : World) (t : String) : List Nat :=
  (List.range peerCount).filter fun i => w.subs.contains (i, t)
def mesh (w : World) (t : String) : List Nat := (peersOf w.router.mesh t).map index
def fanoutPeers (w : World) (t : String) : List Nat := (peersOf w.router.fanout t).map index
/-- Whether this node may GRAFT a peer on a topic, by v1.1: not explicit, score not negative,
no backoff. -/
def graftable (w : World) (t : String) (i : Nat) : Bool :=
  i ∉ explicitPeers && i < 8 && w.backoffEnd t i ≤ w.now

end World

/-- Whether two lists hold the same elements. -/
def sameSet {α : Type} [BEq α] (a b : List α) : Bool :=
  a.all b.contains && b.all a.contains

def hasDuplicates (l : List Nat) : Bool := l.eraseDups.length != l.length

/-- What must hold of the router after every command. -/
def invariants (w : World) : TestT IO Unit := do
  let r := w.router
  ensure (sameSet r.topics w.joined) s!"the router joined {r.topics}, the model {w.joined}"
  ensure (r.mesh.all fun e => w.joined.contains e.1) "a mesh of a topic that is not joined"
  for t in topicNames do
    let mesh := w.mesh t
    ensure (!hasDuplicates mesh) s!"a peer is twice in the mesh of {t}: {mesh}"
    for i in mesh do
      ensure (i ∉ explicitPeers) s!"the explicit peer {i} is in the mesh of {t}"
      ensure (w.backoffEnd t i ≤ w.now)
        s!"peer {i} is in the mesh of {t} within its backoff, which ends at {w.backoffEnd t i}"
    for i in List.range peerCount do
      Gossip.backoffEnd r.backoff t (peer i) === w.backoffEnd t i
    ensure (sameSet ((topicPeers r t).map index) (w.subscribed t))
      s!"the peers of {t} are {(topicPeers r t).map index}, the model's {w.subscribed t}"
    -- Gossip names the messages of the two newest windows.
    let gossip := (r.mcache.gossipIds params.mcache_gossip t).map fun id => id[0]
    let want := (w.cache.filter fun (_, m, age) =>
      m.topic == t && age < params.mcache_gossip).map (·.1)
    ensure (sameSet gossip want) s!"the gossip of {t} names {gossip}, the model {want}"
    let fanout := w.fanoutPeers t
    ensure (!hasDuplicates fanout && fanout.length ≤ params.D) s!"the fanout of {t} is {fanout}"
  ensure (sameSet (r.fanout.map (·.1)) (w.fanout.map (·.1)))
    s!"the fanout holds {r.fanout.map (·.1)}, the model {w.fanout.map (·.1)}"
  ensure (r.fanout.all fun e => !w.joined.contains e.1) "a joined topic is in the fanout"
  for k in List.range keyCount do
    let key := UInt8.ofNat k
    r.seen.contains w.now (params.seen_ttl * 1000) (idOf key) === w.isSeen key
    ensure (r.mcache.get (idOf key) == w.cached key) s!"the message cache differs at ID {k}"

/-- The control messages as text: the peer, the kind, the topic and the backoff or the IDs. -/
def showControl (cs : List (PeerId × Control)) : List String :=
  cs.flatMap fun (p, c) =>
    c.graft.map (fun g => s!"{index p} GRAFT {g.topicId}") ++
    c.prune.map (fun q => s!"{index p} PRUNE {q.topicId} {q.backoff}") ++
    c.ihave.map (fun h => s!"{index p} IHAVE {h.topicId} {h.messageIds.map (·.data.getD 0 0)}") ++
    c.iwant.map (fun x => s!"{index p} IWANT {x.messageIds.map (·.data.getD 0 0)}")

/-- An RPC from a peer, and what it gave. -/
def rpc (w : World) (i : Nat) (r : Rpc) : RouterState × Out :=
  receiveRpc params graftPenaltyMs bareBackoffMs standing msgId validate w.now (peer i) r w.router

/-- Nothing was sent or delivered. -/
def silent (out : Out) : TestT IO Unit := do
  ensure (out.forward.isEmpty && out.answers.isEmpty && out.delivered.isEmpty) "a message goes out"
  showControl out.control === []

/-- A graylisted peer is ignored: nothing changes and nothing is sent. -/
def ignored (w : World) (s : RouterState) (out : Out) : TestT IO World := do
  ensure (s == w.router) "the RPC of a graylisted peer changes the router"
  silent out
  pure w

def genPeer : Gen Nat := Gen.nat (.constant 0 (peerCount - 1))
def genTopic : Gen String := Gen.frequency [(5, Gen.element topicNames), (1, pure "unknown")]
def genKey : Gen UInt8 := UInt8.ofNat <$> Gen.nat (.constant 0 (keyCount - 1))

/-! ## The commands -/

/-- Time passes. -/
structure Tick where
  ms : Nat

instance : Command Tick World Unit IO where
  apply c w := do
    let w := { w with now := w.now + c.ms }
    invariants w
    pure w
  label c := s!"TICK({c.ms})"
  build _ := Tick.mk <$> Gen.element [1, 300, 700, 999, 1000, 1001, 1499, 1500, 2000, 2500, 3001]

/-- A peer announces or withdraws a subscription. -/
structure Subscribe where
  peer : Nat
  topic : String
  on : Bool

instance : Command Subscribe World Unit IO where
  apply c w := do
    let (s, out) := rpc w c.peer { subscriptions := [{ subscribe := c.on, topicId := c.topic }] }
    if c.peer = 11 then ignored w s out else
    silent out
    let subs := w.subs.filter (· != (c.peer, c.topic))
    let w := { w with router := s, subs := if c.on then (c.peer, c.topic) :: subs else subs }
    invariants w
    pure w
  label c := s!"SUBSCRIBE(peer {c.peer}, {c.topic}, {c.on})"
  build _ := do
    pure ⟨← genPeer, ← genTopic, ← Gen.frequency [(5, pure true), (1, pure false)]⟩

/-- A peer forwards a message. -/
structure Receive where
  peer : Nat
  topic : String
  key : UInt8
  verdict : UInt8

instance : Command Receive World Unit IO where
  apply c w := do
    let m := message c.topic c.key c.verdict
    let (s, out) := rpc w c.peer { publish := [m] }
    if c.peer = 11 then ignored w s out else
    showControl out.control === []
    ensure out.answers.isEmpty "an answer to no IWANT"
    -- A message is new on a joined topic when its ID was not seen within the lifetime.
    let fresh := w.joined.contains c.topic && !w.isSeen c.key
    let accepted := fresh && c.verdict != 1 && c.verdict != 2
    ensure (out.delivered == if accepted then [m] else [])
      s!"delivered {out.delivered.length} messages, the model {if accepted then 1 else 0}"
    -- An accepted message goes to the mesh of its topic and to the explicit peers.
    let targets := if accepted then w.mesh c.topic ++ explicitPeers else []
    out.forward.map (fun (p, x) => (index p, keyOf x)) === targets.map (·, c.key)
    let w := { w with
      router := s
      seen := if fresh then (c.key, w.now) :: w.seen else w.seen
      cache := if accepted then (c.key, m, 0) :: w.cache else w.cache
      delivered := w.delivered + out.delivered.length }
    invariants w
    pure w
  label c := s!"RECEIVE(peer {c.peer}, {c.topic}, id {c.key}, verdict {c.verdict})"
  build _ := do
    pure ⟨← genPeer, ← genTopic, ← genKey, ← Gen.frequency [(5, pure 0), (1, pure 1), (1, pure 2)]⟩

/-- A peer grafts this node. -/
structure Graft where
  peer : Nat
  topic : String

instance : Command Graft World Unit IO where
  apply c w := do
    let (s, out) := rpc w c.peer { control := { graft := [{ topicId := c.topic }] } }
    if c.peer = 11 then ignored w s out else
    ensure (out.forward.isEmpty && out.answers.isEmpty && out.delivered.isEmpty)
      "a message goes out"
    let mesh := w.mesh c.topic
    let ends := w.backoffEnd c.topic c.peer
    let after := (peersOf s.mesh c.topic).map index
    if c.peer ∈ explicitPeers then
      -- v1.1, explicit peering: such an attempt is rejected with a PRUNE.
      showControl out.control === [s!"{c.peer} PRUNE {c.topic} 0"]
      after === mesh
      let w := { w with router := s }
      invariants w
      pure w
    else if !w.joined.contains c.topic then
      -- v1.1, spam protection: a GRAFT for an unknown topic is ignored.
      showControl out.control === []
      ensure (s == w.router) "a GRAFT for an unknown topic changes the router"
      pure w
    else if w.now < ends then
      -- v1.1: a GRAFT within the backoff is pruned at once, and the backoff is extended.
      let extended := ends + graftPenaltyMs
      showControl out.control ===
        [s!"{c.peer} PRUNE {c.topic} {(extended - w.now + 999) / 1000}"]
      after === mesh.filter (· != c.peer)
      let w := { w with router := s }.setBackoff c.topic c.peer extended
      invariants w
      pure w
    else
      showControl out.control === []
      -- v1.1, outbound quotas: at D_high or above, only an outbound peer is accepted.
      let accepted := c.peer ∉ mesh && (mesh.length < params.D_high || c.peer ∈ outboundPeers)
      after === (if accepted then mesh ++ [c.peer] else mesh)
      let w := { w with router := s }
      invariants w
      pure w
  label c := s!"GRAFT(peer {c.peer}, {c.topic})"
  build _ := do pure ⟨← genPeer, ← genTopic⟩

/-- A peer prunes this node, with a backoff in seconds or none. -/
structure Prune where
  peer : Nat
  topic : String
  backoff : UInt64

instance : Command Prune World Unit IO where
  apply c w := do
    let (s, out) := rpc w c.peer
      { control := { prune := [{ topicId := c.topic, backoff := c.backoff }] } }
    if c.peer = 11 then ignored w s out else
    silent out
    if !w.joined.contains c.topic then
      ensure (s == w.router) "a PRUNE for a topic that is not joined changes the router"
      pure w
    else
      (peersOf s.mesh c.topic).map index === (w.mesh c.topic).filter (· != c.peer)
      let duration := if c.backoff = 0 then bareBackoffMs else c.backoff.toNat * 1000
      let w := { w with router := s }.raiseBackoff c.topic c.peer (w.now + duration)
      invariants w
      pure w
  label c := s!"PRUNE(peer {c.peer}, {c.topic}, backoff {c.backoff})"
  build _ := do pure ⟨← genPeer, ← genTopic, ← Gen.element [0, 1, 2, 5]⟩

/-- A peer tells of message IDs it has: some of 20 bytes, one that is not. -/
structure IHave where
  peer : Nat
  topic : String
  keys : List UInt8
  short : Bool

instance : Command IHave World Unit IO where
  apply c w := do
    let ids := c.keys.map (fun k => (idOf k).toBytes) ++ if c.short then [⟨#[1, 2, 3]⟩] else []
    let (s, out) := rpc w c.peer
      { control := { ihave := [{ topicId := c.topic, messageIds := ids }] } }
    if c.peer = 11 then ignored w s out else
    ensure (s == w.router) "an IHAVE changes the router"
    ensure (out.forward.isEmpty && out.answers.isEmpty && out.delivered.isEmpty)
      "a message goes out"
    -- v1.1: gossip from a peer below the gossip threshold is ignored.
    let heard := (c.peer < 9 || c.peer ∈ explicitPeers) && w.joined.contains c.topic
    let wanted := if heard then c.keys.filter (!w.isSeen ·) else []
    showControl out.control === (if wanted.isEmpty then [] else [s!"{c.peer} IWANT {wanted}"])
    pure w
  label c :=
    s!"IHAVE(peer {c.peer}, {c.topic}, ids {c.keys}{if c.short then " and a short one" else ""})"
  build _ := do
    pure ⟨← genPeer, ← genTopic, ← Gen.list (.linear 0 4) genKey,
      ← Gen.frequency [(4, pure false), (1, pure true)]⟩

/-- A peer asks for messages. -/
structure IWant where
  peer : Nat
  keys : List UInt8

instance : Command IWant World Unit IO where
  apply c w := do
    let ids := c.keys.map fun k => (idOf k).toBytes
    let (s, out) := rpc w c.peer { control := { iwant := [{ messageIds := ids ++ [⟨#[9]⟩] }] } }
    if c.peer = 11 then ignored w s out else
    ensure (s == w.router) "an IWANT changes the router"
    ensure (out.forward.isEmpty && out.delivered.isEmpty) "a message is forwarded or delivered"
    showControl out.control === []
    let heard := c.peer < 9 || c.peer ∈ explicitPeers
    let want := if heard then c.keys.filterMap w.cached else []
    ensure (out.answers == want.map (peer c.peer, ·))
      s!"{out.answers.length} answers, the model {want.length}"
    pure w
  label c := s!"IWANT(peer {c.peer}, ids {c.keys})"
  build _ := do pure ⟨← genPeer, ← Gen.list (.linear 1 4) genKey⟩

/-- This node joins a topic. -/
structure Join where
  topic : String

instance : Command Join World Unit IO where
  apply c w := do
    let (s, out) := join params Select.first standing w.now c.topic w.router
    if w.joined.contains c.topic then
      ensure (s == w.router) "joining a joined topic changes the router"
      silent out
      pure w
    else
      let mesh := (peersOf s.mesh c.topic).map index
      let fanout := w.fanoutPeers c.topic
      -- v1.0: the mesh takes the fanout peers, then peers of the topic, up to D.
      let candidates := (fanout ++ w.subscribed c.topic).eraseDups.filter (w.graftable c.topic)
      ensure (mesh.all candidates.contains) s!"the mesh {mesh} takes a peer outside {candidates}"
      mesh.length === min params.D candidates.length
      ensure ((fanout.filter (w.graftable c.topic)).take params.D |>.all mesh.contains)
        s!"the mesh {mesh} leaves out a peer of the fanout {fanout}"
      showControl out.control === mesh.map fun i => s!"{i} GRAFT {c.topic}"
      silent { out with control := [] }
      let w := { w with router := s, joined := c.topic :: w.joined,
                        fanout := w.fanout.filter (·.1 != c.topic) }
      invariants w
      pure w
  label c := s!"JOIN({c.topic})"
  build _ := Join.mk <$> Gen.element topicNames

/-- This node leaves a topic. -/
structure Leave where
  topic : String

instance : Command Leave World Unit IO where
  apply c w := do
    let (s, out) := leave (choices w.flood) w.now c.topic w.router
    if !w.joined.contains c.topic then
      ensure (s == w.router) "leaving a topic that is not joined changes the router"
      silent out
      pure w
    else
      let mesh := w.mesh c.topic
      -- v1.0: each mesh peer gets a PRUNE; v1.1: with the backoff, which this node keeps too.
      showControl out.control === mesh.map fun i => s!"{i} PRUNE {c.topic} 1"
      silent { out with control := [] }
      let w := mesh.foldl (fun w i => w.raiseBackoff c.topic i (w.now + 1000))
        { w with router := s, joined := w.joined.filter (· != c.topic) }
      invariants w
      pure w
  label c := s!"LEAVE({c.topic})"
  build _ := Leave.mk <$> Gen.element topicNames

/-- This node publishes a message. -/
structure Publish where
  topic : String
  key : UInt8

instance : Command Publish World Unit IO where
  apply c w := do
    let m := message c.topic c.key 0
    let (s, out) := publish params (choices w.flood) Select.first standing msgId w.now m w.router
    if w.isSeen c.key then
      ensure (s == w.router) "publishing a seen message changes the router"
      silent out
      pure w
    else
      showControl out.control === []
      ensure (out.answers.isEmpty && out.delivered.isEmpty) "an answer or a delivery"
      let ok (i : Nat) : Bool := i ∉ explicitPeers && i < 10
      let subscribed := (w.subscribed c.topic).filter ok
      let joined := w.joined.contains c.topic
      let before := w.fanoutPeers c.topic
      let after := (peersOf s.fanout c.topic).map index
      let sent := out.forward.map fun (p, x) => (index p, keyOf x)
      let targets := (sent.map (·.1)).take (sent.length - explicitPeers.length)
      -- v1.1: the message goes to every explicit peer, here after the others.
      (sent.drop targets.length) === explicitPeers.map (·, c.key)
      ensure (targets.all ok) s!"the message goes to {targets}, one explicit or below the threshold"
      if w.flood then
        -- v1.1, flood publishing: every peer of the topic above the publish threshold.
        ensure (sameSet targets ((w.mesh c.topic).filter ok ++ subscribed).eraseDups)
          s!"flooded to {targets}, the peers of the topic are {subscribed}"
      else if joined then
        targets === (w.mesh c.topic).filter ok
      else
        -- v1.0: the fanout of the topic, chosen among its peers when there is none.
        if before.isEmpty then
          ensure (after.all subscribed.contains) s!"the fanout {after} is outside {subscribed}"
          after.length === min params.D subscribed.length
        else after === before
        targets === after.filter ok
      let fanout := if joined || w.flood then w.fanout
        else (c.topic, w.now) :: w.fanout.filter (·.1 != c.topic)
      let w := { w with router := s, seen := (c.key, w.now) :: w.seen,
                        cache := (c.key, m, 0) :: w.cache, fanout }
      invariants w
      pure w
  label c := s!"PUBLISH({c.topic}, id {c.key})"
  build _ := do pure ⟨← Gen.element topicNames, ← genKey⟩

/-- The heartbeat. -/
structure Heartbeat where

instance : Command Heartbeat World Unit IO where
  apply _ w := do
    let cs := choices w.flood
    let (s, out) := heartbeat params cs Select.first rank standing w.now w.router
    ensure (out.forward.isEmpty && out.answers.isEmpty && out.delivered.isEmpty)
      "a message goes out"
    let mut w' := { w with router := s }
    let mut control : List String := []
    for t in w.joined.reverse do
      let old := w.mesh t
      let new := (peersOf s.mesh t).map index
      let kept := old.filter (· < 8)
      let outside (m : List Nat) := (w.subscribed t).filter fun i => w.graftable t i && i ∉ m
      -- v1.1: peers with a negative score leave; new peers may be grafted.
      ensure (new.all fun i => i < 8 && (old.contains i || (outside old).contains i))
        s!"the mesh of {t} goes from {old} to {new}"
      -- v1.0: below D_low, graft up to D; above D_high, prune down to D.
      if kept.length < params.D_low then
        -- The outbound quota may then add up to D_out peers.
        let filled := min params.D (kept.length + (outside kept).length)
        ensure (filled ≤ new.length && new.length ≤ filled + cs.dOut)
          s!"the mesh of {t} is filled from {kept} to {new}, with {outside kept} to take"
      else if params.D_high < kept.length then
        ensure (params.D ≤ new.length && new.length ≤ params.D + cs.dOut)
          s!"the mesh of {t} is pruned from {kept} to {new}"
        -- v1.1: the best D_score peers by score are kept.
        ensure (new.contains (kept.foldl min 99)) s!"the best peer of {kept} is pruned: {new}"
      else ensure (kept.all new.contains) s!"the mesh of {t} loses peers within its bounds: {new}"
      -- v1.1, outbound quota: with D_low peers or more, D_out of them are outbound if any can be.
      let outbound := new.filter outboundPeers.contains
      if params.D_low ≤ new.length && outbound.length < cs.dOut then
        ensure ((outside new).all (· ∉ outboundPeers) &&
            kept.all fun i => i ∉ outboundPeers || new.contains i)
          s!"the mesh of {t} is {new}, with an outbound peer left out"
      let removed := old.filter (!new.contains ·)
      control := control ++ (new.filter (!old.contains ·)).map fun i => s!"{i} GRAFT {t}"
      for i in removed do
        w' := w'.raiseBackoff t i (w.now + cs.pruneBackoffS.toNat * 1000)
    for t in w.joined.reverse do
      let new := (peersOf s.mesh t).map index
      control := control ++ ((w.mesh t).filter (!new.contains ·)).map fun i => s!"{i} PRUNE {t} 2"
    -- v1.0: a fanout topic leaves after its lifetime; the others are topped up to D.
    let fanout := w.fanout.filter fun (_, last) => !(last + params.fanout_ttl * 1000 < w.now)
    w' := { w' with fanout }
    for (t, _) in fanout do
      let peers := (peersOf s.fanout t).map index
      let ok (i : Nat) : Bool := i ∉ explicitPeers && i < 10
      let more := (w.subscribed t).filter fun i => ok i && !peers.contains i
      ensure (peers.all (· < 10)) s!"the fanout of {t} keeps a peer below the publish threshold"
      ensure (peers.length == params.D || more.isEmpty) s!"the fanout of {t} is {peers}, short of D"
    -- v1.0: gossip for the joined topics and the fanout, to peers outside both.
    let gossip := (showControl out.control).filter fun line => (line.splitOn " IHAVE ").length == 2
    let mut expected := 0
    for t in w.joined.reverse ++ fanout.map (·.1) do
      let ids := (w.cache.filter fun (_, m, age) =>
        m.topic == t && age < params.mcache_gossip).map (·.1)
      let mesh := (peersOf s.mesh t).map index ++ (peersOf s.fanout t).map index
      let candidates := (w.subscribed t).filter fun i => i ∉ mesh && i ∉ explicitPeers && i < 9
      let told := (out.control.filter fun (_, c) => c.ihave.any (·.topicId == t)).map
        fun (p, _) => index p
      if ids.isEmpty then ensure told.isEmpty s!"gossip for {t} with nothing to tell"
      else
        ensure (told.all candidates.contains && !hasDuplicates told)
          s!"gossip for {t} goes to {told}, outside {candidates}"
        told.length === min candidates.length (max params.D_lazy ((candidates.length + 3) / 4))
        for (_, c) in out.control do
          for h in c.ihave do
            if h.topicId == t then
              ensure (sameSet (h.messageIds.map (·.data.getD 0 0)) ids)
                s!"an IHAVE for {t} names other IDs than {ids}"
      expected := expected + told.length
    gossip.length === expected
    (showControl out.control).filter (fun line => (line.splitOn " IHAVE ").length != 2) === control
    -- The message cache shifts by one window.
    let aged := (w'.cache.map fun (k, m, age) => (k, m, age + 1)).filter
      fun e => e.2.2 < params.mcache_len
    w' := { w' with cache := aged }
    invariants w'
    pure w'
  label _ := "HEARTBEAT"
  build _ := pure {}

/-- The commands of a scenario. -/
def commands : List (Unit → World → Gen (CommandWrapper World IO)) := [
  Command.gen Subscribe, Command.gen Subscribe, Command.gen Subscribe, Command.gen Join,
  Command.gen Graft, Command.gen Graft, Command.gen Prune, Command.gen Receive, Command.gen Receive,
  Command.gen Publish, Command.gen IHave, Command.gen IWant, Command.gen Heartbeat,
  Command.gen Heartbeat, Command.gen Leave, Command.gen Tick, Command.gen Tick]

/-- A scripted start that fills meshes and caches, so that random commands meet a busy router. -/
def warmUp : List (Unit → World → Gen (CommandWrapper World IO)) :=
  ((List.range 10).flatMap fun i =>
    [Command.fixed (Subscribe.mk i "a" true), Command.fixed (Subscribe.mk i "b" true)]) ++
  [Command.fixed (Join.mk "a"), Command.fixed (Publish.mk "b" 0)] ++
  ((List.range 6).map fun i => Command.fixed (Graft.mk i "a")) ++
  [Command.fixed (Receive.mk 0 "a" 1 0), Command.fixed Heartbeat.mk]

/-- Long random sequences after the scripted start.

The script is drawn apart from the random commands, so a failure shrinks it too. -/
def long (flood : Bool) : Property IO := propertyM do
  let start : World := { flood }
  let script ← forAll (Gen.sequence (warmUp.map (· () start)))
  let random ← forAll (Gen.list (.linear 1 120) (Gen.choice (commands.map (· () start))))
  pure do
    let _ ← executeCommands (script ++ random) start
    pure ()

/-- The scenarios of this module. -/
def passing (cases : Nat) : List (String × Property IO) := [
  ("gossipsub: the router, scripted (Command, deterministic)",
    scenario .deterministic () (warmUp ++ commands)),
  ("gossipsub: the router, random commands (Command, madhouse)",
    (scenario .madhouse () commands).withTests cases),
  ("gossipsub: the router, long sequences (Command, madhouse)", (long false).withTests cases),
  ("gossipsub: the router with flood publishing (Command, madhouse)", (long true).withTests cases)]

end NetworkingProperty.Router

import Hedgehog
import Support
import EthLib.Consensus.ForkChoice.Handlers
import EthLib.Consensus.ForkChoice.ProposerHead
import EthLib.Consensus.Gossip.Message
import EthLib.Consensus.WeakSubjectivity
import EthLib.Consensus.HonestValidator
import EthLib.Consensus.LightClient.FullNode

/-!
# The fork choice store as a state machine, against the pyspec

The transitions are the handlers of `fork-choice.md`: a tick, a block, an attestation and an
attester slashing.
The oracle (`oracle/forkchoice_store.py`) builds each object with the pyspec, runs the handler of
the pyspec on it, and answers with the steps it ran and a view of its store.
The driver runs the same steps on EthLib's store and requires the same verdict of every step and
the same view after every command: the head, the checkpoints, the boost, the clock, the
equivocators, the latest messages and the weight of every block.

The model of the `StateMachine` is the shape of the run: the clock and the slot of every block
built so far.
It is what a generator needs to aim a command at an edge, and what a precondition needs to keep a
shrunk sequence meaningful.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ForkChoiceProperty

/-- The preset of every run. -/
abbrev P : Preset := Preset.minimal

/-- The minimal configuration with every fork up to the given one active from genesis.

The oracle sets the same epochs in the configuration of the pyspec. -/
def C (fork : Fork) : Consensus.Config :=
  let epoch (first : Fork) : Epoch := if first ≤ fork then 0 else FAR_FUTURE_EPOCH
  { Consensus.Config.minimal with
    ALTAIR_FORK_EPOCH := epoch .altair
    BELLATRIX_FORK_EPOCH := epoch .bellatrix
    CAPELLA_FORK_EPOCH := epoch .shapella
    DENEB_FORK_EPOCH := epoch .dencun
    ELECTRA_FORK_EPOCH := epoch .pectra
    FULU_FORK_EPOCH := epoch .fusaka
    GLOAS_FORK_EPOCH := epoch .glamsterdam }

/-- The duration of a slot of the minimal configuration, in milliseconds. -/
def slotMs : Nat := 6000

/-- The slots of an epoch of the minimal preset. -/
def epochSlots : Nat := 8

/-! ## The model: the shape of a run -/

/-- The clock and the blocks built so far. -/
structure Shape where
  /-- The name of the fork in the pyspec. -/
  forkName : String
  /-- The number of validators of the anchor state. -/
  validators : Nat
  /-- The variant of the anchor state: unequal balances, a slashed and an inactive validator. -/
  variant : Nat
  /-- Whether a vote may name a committee past those of its slot. -/
  loose : Bool
  /-- The time since genesis, in milliseconds. -/
  timeMs : Nat
  /-- The slot of each block, by index, the anchor first. -/
  slots : Array Nat
  deriving Repr

/-- The current slot of a shape. -/
def Shape.now (s : Shape) : Nat := s.timeMs / slotMs

/-- A command of the fork choice. -/
inductive Cmd where
  /-- Move the clock forward. -/
  | tick (deltaMs : Nat)
  /-- Set how far the clock of gossip runs ahead of the clock of the store. -/
  | ahead (aheadMs : Nat)
  /-- A block on a parent at a slot.

  Variants 1, 2 and 3 are not valid, and from Gloas variant 4 builds on the parent's payload. -/
  | block (parent slot variant lookback : Nat)
  /-- A block built before, once more. -/
  | again (index : Nat)
  /-- Blocks one after another from a parent, each in its slot with the votes before it. -/
  | chain (parent count gap lateMs : Nat)
  /-- A vote for a block, some slots after it, by part of a committee, perhaps mutated. -/
  | attest (block delta committee mask mutation : Nat)
  /-- A slashing of the votes for two blocks, perhaps mutated. -/
  | slash (first second mask mutation : Nat)
  /-- From Gloas: the envelope that reveals the payload of a block, perhaps mutated. -/
  | envelope (index mutation : Nat)
  /-- From Gloas: a vote of a member of the payload committee of a block.

  The flags are whether the payload is present and whether its data is available. -/
  | ptc (index member flags delta : Nat)
  deriving Repr

/-- The slot of the last block of a chain command. -/
def chainEnd (s : Shape) (parent count gap : Nat) : Nat :=
  max (s.slots[parent]?.getD 0) s.now + count * (1 + gap)

/-- The shape after a command. -/
def Shape.step (s : Shape) : Cmd → Shape
  | .tick delta => { s with timeMs := s.timeMs + delta }
  | .block _ slot _ _ => { s with slots := s.slots.push slot }
  | .again _ | .ahead _ => s
  | .chain parent count gap lateMs =>
    let first := max (s.slots[parent]?.getD 0) s.now
    { s with
      timeMs := chainEnd s parent count gap * slotMs + lateMs
      slots := s.slots ++ (Array.range count).map fun i => first + (i + 1) * (1 + gap) }
  | .attest .. | .slash .. | .envelope .. | .ptc .. => s

/-- Whether a command names only blocks that exist. -/
def Shape.allows (s : Shape) : Cmd → Bool
  | .tick _ | .ahead _ => true
  | .block parent .. => parent < s.slots.size
  | .again index => index < s.slots.size
  | .chain parent count _ lateMs => parent < s.slots.size && 0 < count && lateMs < slotMs
  | .attest block .. => block < s.slots.size
  | .slash first second .. => first < s.slots.size && second < s.slots.size
  | .envelope index _ => index < s.slots.size
  | .ptc index .. => index < s.slots.size

/-- An index of a block: the last one more often than not, since a chain grows at its tip. -/
def genIndex (s : Shape) : Gen Nat :=
  Gen.frequency [(3, pure (s.slots.size - 1)), (2, Gen.nat (.constant 0 (s.slots.size - 1)))]

/-- A step of the clock: the deadlines of a slot, the ends of a slot and of an epoch. -/
def genDelta : Gen Nat :=
  Gen.frequency [
    (6, Gen.element [6000, 1, 1999, 2000, 2001, 3999, 4000, 5999, 6001, 0, 12000]),
    (2, Gen.element [48000, 47999, 42000, 96000]),
    (2, Gen.nat (.linear 0 20000))]

/-- A command, aimed at the current slot and at the tips of the tree. -/
def genCmd (s : Shape) : Gen Cmd :=
  let now := s.now
  Gen.frequency [
    (4, Cmd.tick <$> genDelta),
    -- The disparity that gossip allows is 500 ms: its edges, and the edges of a slot.
    (1, Cmd.ahead <$> Gen.element [0, 499, 500, 501, 4000, 5500, 6000, 48000]),
    (5, do
      let parent ← genIndex s
      let parentSlot := s.slots[parent]?.getD 0
      let slot ← Gen.frequency [(5, pure now), (2, pure (parentSlot + 1)), (1, pure (now + 1)),
        (1, Gen.nat (.constant 0 (now + 2)))]
      let variant ← Gen.frequency [(10, pure 0), (2, Gen.element [1, 2, 3, 4])]
      Cmd.block parent slot variant <$> Gen.element [0, 1, 2, 8]),
    (1, Cmd.again <$> genIndex s),
    (3, do
      let parent ← genIndex s
      let count ← Gen.nat (.linear 1 12)
      let gap ← Gen.frequency [(6, pure 0), (1, pure 1)]
      Cmd.chain parent count gap <$> Gen.element [0, 100, 1999, 2000, 4500]),
    (5, do
      let block ← genIndex s
      -- A vote counts from the slot after its own: aim at the slot before the current one.
      let due := now - 1 - s.slots[block]?.getD 0
      let delta ← Gen.frequency [(4, pure due), (3, Gen.element [0, 1, 2]),
        (1, Gen.element [7, 8, 9, 16])]
      let committee ← Gen.frequency [(8, pure 0), (1, Gen.element [1, 2, 4])]
      let mask ← Gen.frequency [(3, pure 0xffff), (2, Gen.nat (.constant 0 0xffff))]
      Cmd.attest block delta committee mask <$>
        Gen.frequency [(3, pure 0), (2, Gen.nat (.constant 1 14))]),
    -- The oracle skips these two before Gloas.
    (2, Cmd.envelope <$> genIndex s <*> Gen.frequency [(4, pure 0), (1, Gen.nat (.constant 1 5))]),
    (2, do
      let index ← genIndex s
      let member ← Gen.frequency [(4, Gen.nat (.constant 0 15)), (1, Gen.nat (.constant 100 164))]
      let flags ← Gen.frequency [(6, Gen.nat (.constant 0 3)), (1, pure 4)]
      Cmd.ptc index member flags <$> Gen.frequency [(5, pure 0), (1, pure 1)]),
    (2, do
      let first ← genIndex s
      let second ← Gen.frequency [(1, pure first), (2, pure (first - 1)), (2, genIndex s)]
      let mask ← Gen.frequency [(1, Gen.element [1, 0xfffff]), (3, Gen.nat (.constant 0 0xfffff))]
      Cmd.slash first second mask <$> Gen.frequency [(3, pure 0), (2, Gen.nat (.constant 1 8))])]

/-- The model of a run at a fork: an anchor state of some size and variant, then commands. -/
def model (forkName : String) (loose : Bool) : Model Shape Cmd where
  initState := do
    let validators ← Gen.element [32, 16, 64, 24]
    let variant ← Gen.nat (.constant 0 7)
    pure { forkName, validators, variant, loose, timeMs := 0, slots := #[0] }
  transitions := genCmd
  apply := Shape.step
  preconditions := Shape.allows

/-! ## The system: EthLib's store -/

/-- A setup of KZG that no run reads: every block has no blob, so no proof is checked. -/
def noSetup : Cryptography.Kzg.TrustedSetup :=
  ⟨Vector.replicate _ default, Vector.replicate _ default, Vector.replicate _ default⟩

/-- What a node asks outside the chain: every payload is valid, and no block has a blob. -/
def sources (fork : Fork) : BlockSources P fork where
  engine := .constant true
  powBlock _ := none
  blobsAndProofs _ := some (#[], #[])
  columns _ := some #[]
  setup := noSetup
  inclusionListSatisfied _ _ := true

/-- A root in hexadecimal. -/
def rootHex (root : Root) : String := hex ⟨root.toArray⟩

/-- The first four bytes of a root in hexadecimal. -/
def rootHex8 (root : Root) : String := String.ofList ((rootHex root).toList.take 8)

/-- A checkpoint as the oracle writes it. -/
def checkpointText (c : Checkpoint) : String := s!"{c.epoch}:{rootHex c.root}"

/-- The view of a store that the oracle writes of its own. -/
def view {fork : Fork} (store : Store P fork) : String :=
  let head := match store.getHead (C fork) with
    | .ok node => rootHex node.root
    | .error _ => "error"
  let headStatus := match store.getHead (C fork) with
    | .ok node => toString node.payloadStatus.code
    | .error _ => "error"
  let flag (test : Except ForkChoiceError Bool) : String :=
    match test with
    | .ok true => "t"
    | .ok false => "f"
    | .error _ => "e"
  let proposerHead := match (do
      let node ← store.getHead (C fork)
      store.getProposerHead (C fork) node (← store.getCurrentSlot (C fork))) with
    | .ok node => s!"{rootHex8 node.root}.{node.payloadStatus.code}"
    | .error _ => "error"
  let slot := (store.getCurrentSlot (C fork)).toOption.getD 0
  let tests := match store.getHead (C fork) with
    | .ok node =>
      let parent := match store.blocks[node.root]? with
        | some known => known.parentRoot
        | none => Vector.replicate 32 0
      String.join [flag (store.isHeadLate node.root),
        flag (store.isFfgCompetitive node.root parent), flag (store.isFinalizationOk (C fork) slot),
        flag (store.isProposingOnTime (C fork)), flag (store.isHeadWeak (C fork) node.root),
        flag (store.isParentStrong (C fork) node.root),
        flag (store.isProposerEquivocation node.root)]
    | .error _ => "eeeeeee"
  let headState := (store.getHead (C fork)).toOption.bind fun node => store.blockStates[node.root]?
  let period := match headState with
    | some state =>
      match computeWeakSubjectivityPeriod (C fork) state with
      | .ok epochs => toString epochs
      | .error _ => "error"
    | none => "error"
  let assignment (epochsAhead : Nat) (validator : Nat) : String :=
    match headState with
    | some state =>
      match getCommitteeAssignment state (getCurrentEpoch state + UInt64.ofNat epochsAhead)
          (UInt64.ofNat validator) with
      | .ok (some (committee, index, slot)) => s!"{committee.size}/{index}/{slot}"
      | .ok none => "none"
      | .error _ => "error"
    | none => "error"
  let duties := ",".intercalate [assignment 0 0, assignment 1 1, assignment 2 2,
    assignment 0 (store.blocks.size % 16), assignment 1 1000]
  let bootstrap := match (do
      let node ← (store.getHead (C fork)).toOption
      let state ← store.blockStates[node.root]?
      let block ← store.blocks[node.root]?
      let made ← (createLightClientBootstrap (C fork) state
        (⟨block, Vector.replicate 96 0⟩ : SignedBeaconBlock P fork)).toOption
      let trusted ← (SszType.hashTreeRoot block).toOption
      -- A store starts from the bootstrap that a full node makes for its head.
      let _ ← (initializeLightClientStore (C fork) trusted made).toOption
      (SszType.hashTreeRoot made).toOption) with
    | some root => rootHex8 root
    | none => "error"
  let tally := store.justifiedTally
  let roots := (store.blocks.toList.map (·.1)).toArray.qsort (fun a b => rootHex a < rootHex b)
  -- The pending node of each block, and from Gloas its empty and its full node.
  let statuses : List PayloadStatus :=
    if .glamsterdam ≤ fork then [.pending, .empty, .full] else [.pending]
  let weights := roots.toList.flatMap fun root => statuses.map fun status =>
    match store.getWeight (C fork) tally ⟨root, status⟩ with
    | .ok weight => s!"{rootHex8 root}.{status.code}:{weight}"
    | .error _ => s!"{rootHex8 root}.{status.code}:error"
  let messages := store.latestMessages.toList.map fun (index, message) =>
    let present := if gloas : .glamsterdam ≤ fork then message.payloadPresent gloas else false
    s!"{index}:{message.rank}:{rootHex8 message.root}:{if present then 1 else 0}"
  let equivocators := store.equivocatingIndices.toArray.qsort (· < ·)
  " ".intercalate [
    s!"h={head}",
    s!"hs={headStatus}",
    s!"j={checkpointText store.justifiedCheckpoint}",
    s!"f={checkpointText store.finalizedCheckpoint}",
    s!"uj={checkpointText store.unrealizedJustifiedCheckpoint}",
    s!"uf={checkpointText store.unrealizedFinalizedCheckpoint}",
    s!"b={rootHex8 store.proposerBoostRoot}",
    s!"ph={proposerHead}",
    s!"pt={tests}",
    s!"ws={period}",
    s!"ca={duties}",
    s!"lc={bootstrap}",
    s!"t={store.timeMs}",
    s!"n={store.blocks.size}",
    "eq=" ++ ",".intercalate (equivocators.toList.map toString),
    "lm=" ++ ",".intercalate messages,
    "w=" ++ ",".intercalate weights]

/-- The words of a line of the oracle. -/
def askWords (oracle : Oracle) (words : List String) : IO (List String) := do
  oracle.stdin.putStrLn ("\t".intercalate words)
  oracle.stdin.flush
  let line ← oracle.stdout.getLine
  if line.isEmpty then throw (IO.userError "the oracle gave no answer")
  pure ((String.ofList (line.toList.filter (· ≠ '\n'))).splitOn "\t")

/-- A value from its SSZ bytes in hexadecimal. -/
def decodeHex (α : Type) [SszType α] (text : String) : Except String α := do
  let some bytes := unhex? text | throw "not hexadecimal"
  (SszType.deserialize α bytes).mapError fun e => s!"SSZ: {reprStr e}"

/-- EthLib's store and the gossip messages it has seen. -/
structure Sut (fork : Fork) where
  /-- The store. -/
  store : Store P fork
  /-- The keys of the valid gossip messages so far. -/
  seen : Seen := {}
  /-- The oracle that holds the store of the pyspec. -/
  oracle : Oracle

/-- The store from the anchor that the oracle builds for a shape. -/
def initSut (fork : Fork) (oracle : Oracle) (s : Shape) : IO (Sut fork) := do
  let words ← askWords oracle ["fc_init", s.forkName, toString s.validators, toString s.variant,
    if s.loose then "1" else "0"]
  let [stateHex, blockHex, expected] := words
    | throw (IO.userError s!"fc_init: {words.take 1}")
  let state ← IO.ofExcept ((decodeHex (BeaconState P fork) stateHex).mapError IO.userError)
  let block ← IO.ofExcept ((decodeHex (BeaconBlock P fork) blockHex).mapError IO.userError)
  match getForkchoiceStore (C fork) state block with
  | .error e => throw (IO.userError s!"the anchor is refused: {e}")
  | .ok store =>
    if view store ≠ expected then
      throw (IO.userError s!"the anchor stores differ:\n{view store}\n{expected}")
    pure { store, oracle }

/-- One step of the oracle on EthLib's store: the store after it, or the error that refuses it. -/
def runStep {fork : Fork} (store : Store P fork) (kind argument : String) :
    Except String (Store P fork) :=
  let checks := SignatureChecks.acceptAll
  match kind with
  | "t" => (store.onTick (C fork) argument.toNat!.toUInt64).mapError toString
  | "b" => do
    let signed ← decodeHex (SignedBeaconBlock P fork) argument
    (store.onBlock (C fork) checks (sources fork) signed).mapError toString
  | "a" | "A" => do
    let attestation ← decodeHex (Attestation P fork) argument
    (store.onAttestation (C fork) checks attestation (kind == "A")).mapError toString
  | "s" => do
    let slashing ← decodeHex (AttesterSlashing P fork) argument
    (store.onAttesterSlashing (C fork) checks slashing).mapError toString
  | "e" =>
    if gloas : .glamsterdam ≤ fork then do
      let signed ← decodeHex (SignedExecutionPayloadEnvelope P fork) argument
      (store.onExecutionPayloadEnvelope (C fork) checks (sources fork) gloas signed).mapError
        toString
    else .error "an envelope before Gloas"
  | "p" =>
    if gloas : .glamsterdam ≤ fork then do
      let message ← decodeHex PayloadAttestationMessage argument
      (store.onPayloadAttestationMessage (C fork) checks gloas message false).mapError toString
    else .error "a payload vote before Gloas"
  | _ => .error s!"unknown step {kind}"

/-- The gossip message of a step of the oracle, by its kind. -/
def gossipMessage (fork : Fork) (kind hexText subnet : String) :
    Except String (GossipMessage P fork) :=
  match kind with
  | "gb" => .beaconBlock <$> decodeHex (SignedBeaconBlock P fork) hexText
  | "ga" =>
    if electra : .pectra ≤ fork then
      (.singleAttestation electra · subnet.toNat!.toUInt64) <$> decodeHex SingleAttestation hexText
    else
      (.beaconAttestation (Nat.lt_of_not_le electra) · subnet.toNat!.toUInt64) <$>
        decodeHex (Attestation P fork) hexText
  | "gg" => .aggregateAndProof <$> decodeHex (SignedAggregateAndProof P fork) hexText
  | "gs" => .attesterSlashing <$> decodeHex (AttesterSlashing P fork) hexText
  | "ge" =>
    if gloas : .glamsterdam ≤ fork then
      .executionPayloadEnvelope gloas <$> decodeHex (SignedExecutionPayloadEnvelope P fork) hexText
    else .error "an envelope before Gloas"
  | "gp" =>
    if gloas : .glamsterdam ≤ fork then
      .payloadAttestationMessage gloas <$> decodeHex PayloadAttestationMessage hexText
    else .error "a payload vote before Gloas"
  | _ => .error s!"unknown gossip step {kind}"

/-- The verdict of EthLib on a gossip step, as the oracle writes one, and the keys after it. -/
def runGossip {fork : Fork} (store : Store P fork) (seen : Seen)
    (kind hexText subnet time : String) : String × Seen :=
  match gossipMessage fork kind hexText subnet with
  | .error e => (s!"undecoded ({e})", seen)
  | .ok message =>
    let timeMs := time.toNat!.toUInt64
    match validateGossipMessage (C fork) .acceptAll noSetup seen store ∅ timeMs message with
    | .ok (.accept, next) => ("accept", next)
    | .ok (.ignore reason, next) => (s!"ignore ({reason})", next)
    | .ok (.reject reason, next) => (s!"reject ({reason})", next)
    | .error e => (s!"error ({e})", seen)

/-- The words that a command sends to the oracle, given the shape after it. -/
def Cmd.words (after : Shape) : Cmd → List String
  | .tick _ => ["fc_tick", toString after.timeMs]
  | .ahead aheadMs => ["fc_ahead", toString aheadMs]
  | .block parent slot variant lookback =>
    ["fc_block", toString parent, toString slot, toString variant, toString lookback]
  | .again index => ["fc_again", toString index]
  | .chain parent count gap lateMs =>
    ["fc_chain", toString parent, toString (after.slots[parent]?.getD 0), toString count,
      toString gap, toString lateMs]
  | .attest target delta committee mask mutation =>
    ["fc_attest", toString target, toString delta, toString committee, toString mask,
      toString mutation]
  | .slash first second mask mutation =>
    ["fc_slash", toString first, toString second, toString mask, toString mutation]
  | .envelope index mutation => ["fc_envelope", toString index, toString mutation]
  | .ptc index member flags delta =>
    ["fc_ptc", toString index, toString member, toString flags, toString delta]

/-- What must hold of EthLib's store after every command, whatever the oracle says. -/
def storeInvariants {fork : Fork} (before after : Store P fork) : TestT IO Unit := do
  ensure (before.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch)
    "the finalized checkpoint regressed"
  ensure (before.justifiedCheckpoint.epoch ≤ after.justifiedCheckpoint.epoch)
    "the justified checkpoint regressed"
  ensure (after.finalizedCheckpoint.epoch ≤ after.justifiedCheckpoint.epoch)
    "the finalized checkpoint is after the justified one"
  ensure (before.timeMs ≤ after.timeMs) "the clock went back"
  match after.getHead (C fork) with
  | .error e => failWith s!"no head: {e}"
  | .ok head =>
    match after.isAncestor head ⟨after.justifiedCheckpoint.root, .pending⟩ with
    | .ok true => pure ()
    | .ok false => failWith "the head does not descend from the justified block"
    | .error e => failWith s!"the head has no ancestor at the justified slot: {e}"
  let boosted := after.proposerBoostRoot ≠ Vector.replicate 32 0
  if boosted then
    match after.blocks[after.proposerBoostRoot]?, after.getCurrentSlot (C fork) with
    | some boostedBlock, .ok slot =>
      ensure (boostedBlock.slot == slot) "the boost outlived its slot"
    | _, _ => failWith "the boosted block is unknown"
  for index in after.equivocatingIndices do
    ensure (before.equivocatingIndices.contains index || !before.latestMessages.contains index ||
      after.latestMessages.contains index) "an equivocator lost its latest message"

/-- Run a command on both stores, and compare the verdict of each step and the views. -/
def applySut {fork : Fork} (sut : Sut fork) (after : Shape) (cmd : Cmd) :
    TestT IO (Sut fork) := do
  let words ← evalIO (askWords sut.oracle (cmd.words after))
  let expected := words.getLast?.getD ""
  let mut store := sut.store
  let mut seen := sut.seen
  for step in words.dropLast do
    if step == "skip" then continue
    if let [kind, hexText, subnet, time, verdict] := step.splitOn ":" then
      let (got, next) := runGossip store seen kind hexText subnet time
      annotate s!"{kind} at {time} ms on subnet {subnet}: EthLib says {got}, the pyspec {verdict}"
      -- An exception of the pyspec that is no verdict leaves the message undefined there:
      -- EthLib may then say anything but accept.
      let mine := (got.splitOn " ").head!
      ensure (mine == verdict || (verdict == "error" && mine != "accept"))
        s!"the verdicts on a `{kind}` message differ"
      if verdict == "error" then
        if (← evalIO (IO.getEnv "FC_DEBUG")).isSome then
          evalIO (IO.eprintln s!"{kind}: pyspec raises, EthLib says {got}")
      seen := next
      continue
    let [kind, argument, verdict] := step.splitOn ":" | failWith s!"a malformed step: {step}"
    match runStep store kind argument with
    | .ok next =>
      ensure (verdict == "ok") s!"EthLib accepts a `{kind}` step that the pyspec refuses"
      store := next
    | .error e =>
      ensure (verdict == "error") s!"EthLib refuses a `{kind}` step that the pyspec accepts: {e}"
  view store === expected
  storeInvariants sut.store store
  pure { sut with store, seen }

/-- The fork choice of EthLib agrees with the pyspec on every sequence of commands. -/
def machine (fork : Fork) (forkName : String) (oracle : Oracle) (loose : Bool := false) :
    StateMachine Shape Cmd (Sut fork) IO where
  toModel := model forkName loose
  initSut := initSut fork oracle
  applySut := applySut

end ForkChoiceProperty

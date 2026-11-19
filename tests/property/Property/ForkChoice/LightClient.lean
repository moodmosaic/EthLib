import Hedgehog
import Support
import Property.ForkChoice.Store
import EthLib.Consensus.LightClient.Sync

/-!
# The light client store as a scenario of commands, against the pyspec

The commands are those of `sync-protocol.md`: process an update, and force the best update.
Each is a type of its own with a `Command` instance, and the scenario runs in madhouse mode.

The oracle (`oracle/forkchoice_lightclient.py`) builds each update with true Merkle branches from
one template state, processes it on the store of the pyspec, and answers with the bytes of the
update, its verdict and a digest of its store.
The driver processes the same bytes on EthLib's store and requires the same verdict and digest.

`Command.build` reads no state, so a command draws its slots blind, around the period edges of the
minimal preset, and the store is made on the first command that runs.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace LightClientProperty

open ForkChoiceProperty (P C rootHex rootHex8 askWords decodeHex)

/-- The slot of the header that every store starts from. -/
def startSlot : Nat := 10

/-- EthLib's store, the chain it follows and its clock; no store before the first command. -/
structure World (fork : Fork) where
  store : Option (LightClientStore P fork) := none
  genesisValidatorsRoot : Root := Vector.replicate 32 0
  now : Nat := startSlot
  deriving Inhabited

/-- The first four bytes of the root of a value. -/
def root8 {α : Type} [SszType α] (value : α) : String :=
  match SszType.hashTreeRoot value with
  | .ok root => rootHex8 root
  | .error _ => "error"

/-- The digest of a store that the oracle writes of its own. -/
def digest {fork : Fork} (store : LightClientStore P fork) : String :=
  " ".intercalate [
    s!"f={store.finalizedHeader.beacon.slot}:{root8 store.finalizedHeader}",
    s!"o={store.optimisticHeader.beacon.slot}:{root8 store.optimisticHeader}",
    s!"c={root8 store.currentSyncCommittee}",
    s!"n={root8 store.nextSyncCommittee}",
    s!"b={(store.bestValidUpdate.map root8).getD "none"}",
    s!"p={store.previousMaxActiveParticipants}",
    s!"a={store.currentMaxActiveParticipants}"]

/-- The world with a store: the one it has, or a new one from the bootstrap of the oracle. -/
def ready {fork : Fork} (forkName : String) (oracle : Oracle) (world : World fork) :
    TestT IO (LightClientStore P fork × World fork) := do
  if let some store := world.store then return (store, world)
  let words ← evalIO (askWords oracle ["lc_init", forkName, toString startSlot])
  let [bootstrapHex, trustedHex, rootHex, expected] := words
    | failWith s!"lc_init: {words.take 1}"
  let some trusted := (unhex? trustedHex).bind fun b =>
      if h : b.size = 32 then some (⟨b.data, h⟩ : Root) else none
    | failWith "the trusted root is not 32 bytes"
  let some genesisValidatorsRoot := (unhex? rootHex).bind fun b =>
      if h : b.size = 32 then some (⟨b.data, h⟩ : Root) else none
    | failWith "the genesis validators root is not 32 bytes"
  match decodeHex (LightClientBootstrap P fork) bootstrapHex with
  | .error e => failWith s!"the bootstrap does not decode: {e}"
  | .ok bootstrap =>
    match initializeLightClientStore (C fork) trusted bootstrap with
    | .error e => failWith s!"EthLib refuses the bootstrap of the pyspec: {e}"
    | .ok store =>
      digest store === expected
      -- Another trusted root refuses the same bootstrap.
      ensure (initializeLightClientStore (C fork) (Vector.replicate 32 1) bootstrap).toOption.isNone
        "a bootstrap is accepted for a block it is not of"
      return (store, { world with store := some store, genesisValidatorsRoot })

/-- What every step keeps: the finalized and optimistic slots never go back. -/
def monotone {fork : Fork} (before after : LightClientStore P fork) : TestT IO Unit := do
  ensure (before.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot)
    "the finalized header went back"
  ensure (before.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot)
    "the optimistic header went back"
  ensure (after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot)
    "the finalized header is after the optimistic one"

/-- What `Command.build` gets: the name of the fork in the pyspec, and the oracle.

`Command.apply` gets no context, so each command carries the oracle that it asks. -/
abbrev Context := String × Oracle

/-- Process an update: its slots, whether it proves a committee, its signers, a mutation. -/
structure Update (fork : Fork) where
  context : Context
  attested : Nat
  signatureDelay : Nat
  /-- The finalized slot as a distance below the attested slot, or none without finality. -/
  finalizedBelow : Option Nat
  /-- No committee, the committee of the template state, or another one. -/
  committee : Nat
  signers : Nat
  mutation : Nat
  /-- Whether the clock stays where it is, perhaps before the signature slot. -/
  early : Bool

/-- A slot at the edges of the periods of the minimal preset, 64 slots each. -/
def genSlot : Gen Nat :=
  Gen.frequency [(4, Gen.element [11, 12, 20, 40, 62, 63]), (3, Gen.element [64, 65, 100, 127]),
    (2, Gen.element [128, 129, 191, 192]), (1, Gen.nat (.linear 0 260))]

instance {fork : Fork} : Command (Update fork) (World fork) Context IO where
  label u :=
    let finalized := match u.finalizedBelow with
      | some below => toString (u.attested - below)
      | none => "none"
    s!"UPDATE(attested {u.attested}, signature +{u.signatureDelay}, finalized {finalized}, " ++
      s!"committee {u.committee}, signers {u.signers}, mutation {u.mutation}, early {u.early})"
  build context := do
    let attested ← genSlot
    let signatureDelay ← Gen.frequency [(5, pure 1), (2, Gen.element [0, 2, 53, 64, 65, 128])]
    let finalizedBelow ← Gen.frequency [(2, pure none),
      (3, some <$> Gen.element [1, 2, 8, 16, 64, 65]), (1, pure (some attested)),
      (1, pure (some 0))]
    let committee ← Gen.frequency [(3, pure 1), (2, pure 0), (1, pure 2)]
    let signers ← Gen.frequency [(5, Gen.element [22, 21, 32, 20, 1, 0, 11, 16, 17]),
      (1, Gen.nat (.constant 0 32))]
    let mutation ← Gen.frequency [(5, pure 0), (2, Gen.nat (.constant 1 7))]
    let early ← Gen.frequency [(7, pure false), (1, pure true)]
    pure { context, attested, signatureDelay, finalizedBelow, committee, signers, mutation, early }
  apply u world := do
    let (store, world) ← ready u.context.1 u.context.2 world
    -- The clock reaches the signature slot, unless the update comes early.
    let world := if u.early then world
      else { world with now := max world.now (u.attested + u.signatureDelay) }
    let finalized : Int := match u.finalizedBelow with
      | some below => ((u.attested - below : Nat) : Int)
      | none => -1
    let words ← evalIO (askWords u.context.2 ["lc_update", toString u.attested,
      toString (u.attested + u.signatureDelay), toString finalized, toString u.committee,
      toString u.signers, toString u.mutation, toString world.now])
    let [updateHex, verdict, expected] := words
      | (if words == ["skip"] then pure world else failWith s!"lc_update: {words.take 1}")
    match decodeHex (LightClientUpdate P fork) updateHex with
    | .error e => failWith s!"the update does not decode: {e}"
    | .ok update =>
      match processLightClientUpdate (C fork) .acceptAll store update (UInt64.ofNat world.now)
          world.genesisValidatorsRoot with
      | .ok next =>
        ensure (verdict == "ok") "EthLib accepts an update that the pyspec refuses"
        digest next === expected
        monotone store next
        pure { world with store := some next }
      | .error e =>
        annotate s!"EthLib: {e}"
        ensure (verdict == "error") "EthLib refuses an update that the pyspec accepts"
        digest store === expected
        pure world

/-- Move the clock, then force the best update if its time has come. -/
structure Force (fork : Fork) where
  context : Context
  slots : Nat

instance {fork : Fork} : Command (Force fork) (World fork) Context IO where
  label f := s!"FORCE(after {f.slots} slots)"
  build context := do
    -- The timeout of an update is one period, 64 slots: its edges, and a short step.
    let slots ← Gen.frequency [(3, Gen.element [0, 1, 8]),
      (3, Gen.element [53, 54, 55, 63, 64, 65]),
      (1, Gen.nat (.linear 0 200))]
    pure { context, slots }
  apply f world := do
    let (store, world) ← ready f.context.1 f.context.2 world
    let world := { world with now := world.now + f.slots }
    let words ← evalIO (askWords f.context.2 ["lc_force", toString world.now])
    let [verdict, expected] := words | failWith s!"lc_force: {words.take 1}"
    match processLightClientStoreForceUpdate store (UInt64.ofNat world.now) with
    | .ok next =>
      ensure (verdict == "ok") "EthLib forces an update that the pyspec refuses"
      digest next === expected
      monotone store next
      pure { world with store := some next }
    | .error e =>
      annotate s!"EthLib: {e}"
      ensure (verdict == "error") "EthLib refuses a forced update that the pyspec makes"
      digest store === expected
      pure world

/-- EthLib's light client store follows the pyspec on every sequence of updates. -/
def madhouse (fork : Fork) (forkName : String) (oracle : Oracle) : Property IO :=
  scenario (σ := World fork) .madhouse (forkName, oracle) [Command.gen (Update fork),
    Command.gen (Update fork), Command.gen (Update fork), Command.gen (Force fork)]

end LightClientProperty

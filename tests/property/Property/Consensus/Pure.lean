import Hedgehog
import Support
import EthLib.Consensus.Shuffle
import EthLib.Consensus.Signing
import EthLib.Consensus.ForkDigest
import EthLib.Consensus.Time

/-!
# Helpers that need no state

The shuffle, the committees, the fork schedule with its digest, and the arithmetic of time.

Each runs against consensus-specs, and against itself where the source states a law.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ConsensusProperty

/-- A preset by its name in consensus-specs. -/
def genPreset : Gen (String × Preset) :=
  Gen.element [("minimal", Preset.minimal), ("mainnet", Preset.mainnet)]

/-- A 32-byte seed. -/
def genSeed : Gen Bytes32 := (fun bytes => Vector.ofFn fun i => bytes[i.val]!) <$> genBytesN 32

/-- A list of numbers in the text form of the oracle. -/
def showNats (xs : List Nat) : String := "[" ++ ",".intercalate (xs.map toString) ++ "]"

/-- The shuffled position of every index is that of consensus-specs.

The whole-list shuffle gives the same positions, which form a permutation. -/
def shuffle (oracle : Oracle) : Property IO := propertyM do
  let (presetName, preset) ← forAllWith (·.1) genPreset
  let count ← forAll (Gen.frequency [(6, Gen.nat (.linear 0 70)),
    (2, Gen.element [1, 2, 3, 255, 256, 257, 511, 512, 513])])
  let seed ← forAllWith (fun s => hex ⟨s.toArray⟩) genSeed
  pure do
    let single := (List.range count).map fun i =>
      match computeShuffledIndex preset (UInt64.ofNat i) (UInt64.ofNat count) seed with
      | .ok position => position.toNat
      | .error _ => count
    match computeShuffledPermutation preset (UInt64.ofNat count) seed with
    | .error _ => failWith "the whole-list shuffle is refused"
    | .ok whole => whole.toList.map (·.toNat) === single
    ensure ((single.mergeSort (· ≤ ·)) == List.range count) "the shuffle is no permutation"
    showNats single === (← oracle.ask ["pure", "shuffle", presetName, toString count,
      hex ⟨seed.toArray⟩])

/-- An index at or past the count has no shuffled position, as the source asserts. -/
def shuffleRange : Property IO := pureIO do
  let count ← forAll (Gen.nat (.linear 0 50))
  let past ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 3)),
    (1, Gen.nat (.exponential 0 (2 ^ 63)))])
  let seed ← forAllWith (fun s => hex ⟨s.toArray⟩) genSeed
  ensure (computeShuffledIndex Preset.minimal (UInt64.ofNat (count + past)) (UInt64.ofNat count)
    seed).toOption.isNone "an index past the count is shuffled"

/-- A committee of a list of indices is that of consensus-specs, or refused as there. -/
def committee (oracle : Oracle) : Property IO := propertyM do
  let (presetName, preset) ← forAllWith (·.1) genPreset
  let indices ← forAll (Gen.list (.linear 0 40) (Gen.nat (.linear 0 1000)))
  let count ← forAll (Gen.frequency [(6, Gen.nat (.linear 1 12)), (1, pure 0),
    (1, Gen.nat (.linear 0 64))])
  let index ← forAll (Gen.frequency [(6, Gen.nat (.linear 0 (count - 1))),
    (2, Gen.nat (.linear 0 (count + 2))),
    (1, Gen.element [2 ^ 64 - 1, 2 ^ 63, 2 ^ 32])])
  let seed ← forAllWith (fun s => hex ⟨s.toArray⟩) genSeed
  pure do
    let expected ← oracle.ask (["pure", "committee", presetName, hex ⟨seed.toArray⟩,
      toString index, toString count] ++ indices.map toString)
    match computeCommittee preset (indices.map UInt64.ofNat).toArray seed (UInt64.ofNat index)
      (UInt64.ofNat count) with
    | .ok members => showNats (members.toList.map (·.toNat)) === expected
    | .error e =>
      ensure (expected.startsWith "error") s!"EthLib refuses ({repr e}), the reference: {expected}"

/-- Fork epochs: mostly in order, each fork at or after the one before, sometimes not. -/
def genForkEpochs : Gen (List Nat) := do
  let steps ← Gen.list (.singleton 8) (Gen.frequency [(3, pure 0), (4, Gen.nat (.linear 0 50)),
    (1, pure (2 ^ 64 - 1))])
  let ordered := (steps.foldl (fun (acc : List Nat × Nat) step =>
    let next := min (acc.2 + step) (2 ^ 64 - 1)
    (acc.1 ++ [next], next)) ([], 0)).1
  Gen.frequency [(5, pure ordered), (1, Gen.shuffle ordered)]

/-- A blob schedule: a few entries, in any order, with epochs that may repeat. -/
def genBlobSchedule : Gen (List (Nat × Nat)) :=
  Gen.list (.linear 0 5) (Gen.zip
    (Gen.frequency [(5, Gen.nat (.linear 0 200)), (1, pure (2 ^ 64 - 1))])
    (Gen.nat (.linear 0 72)))

/-- The mainnet configuration with other fork epochs and another blob schedule. -/
def scheduleConfig (epochs : List Nat) (blobs : List (Nat × Nat)) : Consensus.Config :=
  let at_ (i : Nat) : Epoch := UInt64.ofNat (epochs.getD i 0)
  { Consensus.Config.mainnet with
    ALTAIR_FORK_EPOCH := at_ 0, BELLATRIX_FORK_EPOCH := at_ 1, CAPELLA_FORK_EPOCH := at_ 2,
    DENEB_FORK_EPOCH := at_ 3, ELECTRA_FORK_EPOCH := at_ 4, FULU_FORK_EPOCH := at_ 5,
    GLOAS_FORK_EPOCH := at_ 6, HEZE_FORK_EPOCH := at_ 7,
    BLOB_SCHEDULE := blobs.map fun (epoch, limit) => ⟨UInt64.ofNat epoch, UInt64.ofNat limit⟩ }

/-- At an epoch, the fork version, the blob parameters and the fork digest match consensus-specs.

This holds under any fork schedule and blob schedule. -/
def schedule (oracle : Oracle) : Property IO := propertyM do
  let epochs ← forAll genForkEpochs
  let blobs ← forAll genBlobSchedule
  -- An epoch at an edge of the schedule, or anywhere.
  let edges := epochs ++ blobs.map (·.1)
  let epoch ← forAll (Gen.frequency [
    (6, do
      let edge ← Gen.element (0 :: edges)
      let nudge ← Gen.element [0, 1, 2]
      pure (min (edge + nudge - 1) (2 ^ 64 - 1))),
    (2, Gen.nat (.linear 0 300)),
    (1, pure (2 ^ 64 - 1))])
  let root ← forAllWith (fun s => hex ⟨s.toArray⟩) genSeed
  pure do
    let config := scheduleConfig epochs blobs
    let ask (what : String) := oracle.ask ["pure", "schedule", what,
      ",".intercalate (epochs.map toString),
      if blobs.isEmpty then "-" else ";".intercalate (blobs.map fun (e, m) => s!"{e}:{m}"),
      toString epoch, hex ⟨root.toArray⟩]
    let at_ := UInt64.ofNat epoch
    hex ⟨(config.computeForkVersion at_).toArray⟩ === (← ask "version")
    let parameters := config.getBlobParameters at_
    s!"{parameters.epoch.toNat}:{parameters.maxBlobsPerBlock.toNat}" === (← ask "blobs")
    match computeForkDigest config root at_ with
    | .ok digest => hex ⟨digest.toArray⟩ === (← ask "digest")
    | .error _ => failWith "EthLib computes no digest"

/-- The arithmetic of slots, epochs and time is that of consensus-specs, overflow included. -/
def time (oracle : Oracle) : Property IO := propertyM do
  let a ← forAll genUInt64
  let b ← forAll (Gen.choice [genUInt64, UInt64.ofNat <$> Gen.nat (.linear 0 100000)])
  pure do
    let preset := Preset.minimal
    let config := Consensus.Config.minimal
    let shown {ε : Type} (result : Except ε UInt64) : String :=
      match result with
      | .ok n => toString n.toNat
      | .error _ => "error"
    let agree (name : String) (got : String) (arguments : List UInt64) : TestT IO Unit := do
      let expected ←
        oracle.ask (["pure", "time", name] ++ arguments.map fun n => toString n.toNat)
      annotate name
      got === (if expected.startsWith "error" then "error" else expected)
    agree "compute_epoch_at_slot" (toString (computeEpochAtSlot preset a).toNat) [a]
    agree "compute_start_slot_at_epoch" (shown (computeStartSlotAtEpoch preset a)) [a]
    agree "compute_activation_exit_epoch" (shown (computeActivationExitEpoch preset a)) [a]
    agree "compute_sync_committee_period" (toString (computeSyncCommitteePeriod preset a).toNat) [a]
    agree "compute_time_at_slot" (shown (computeTimeAtSlot config a b)) [a, b]
    agree "compute_slot_at_time" (shown (computeSlotAtTime config a b)) [a, b]
    agree "compute_time_at_slot_ms" (shown (computeTimeAtSlotMs config a b)) [a, b]
    agree "compute_slot_at_time_ms" (shown (computeSlotAtTimeMs config a b)) [a, b]
    agree "seconds_to_milliseconds" (toString (secondsToMilliseconds a).toNat) [a]

/-- Every value of a preset and of a configuration that consensus-specs names is its value there.

The values are read from the derived `Repr`, so a new field is compared without a change here. -/
def constantsAgree (oracle : Oracle) : Property IO := propertyM do
  let (name, text) ← forAllWith (·.1) (Gen.element [
    ("minimal", toString (repr Preset.minimal) ++ toString (repr Consensus.Config.minimal)),
    ("mainnet", toString (repr Preset.mainnet) ++ toString (repr Consensus.Config.mainnet))])
  pure do
    let answer ← oracle.ask ["pure", "constants", name, hex text.toUTF8]
    annotate answer
    ensure (answer.startsWith "ok:") "a constant differs from consensus-specs"

/-- The properties of the helpers that need no state. -/
def pureProperties (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("the shuffle of every index, and of the whole list", (shuffle oracle).withTests cases),
  ("no shuffled position past the count", shuffleRange.withTests cases),
  ("a committee of a list of indices", (committee oracle).withTests cases),
  ("the fork version, blob parameters and digest of a schedule", (schedule oracle).withTests cases),
  ("slots, epochs and time", (time oracle).withTests cases),
  ("the presets and configurations", (constantsAgree oracle).withTests 8)]

end ConsensusProperty

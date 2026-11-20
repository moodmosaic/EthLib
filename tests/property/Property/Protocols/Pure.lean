import Property.Protocols.World
import EthLib.Consensus.Shuffle
import EthLib.Consensus.Time
import EthLib.Consensus.HonestProposer

/-!
# Helpers that need no state, at every value of the constants they read

The shuffle takes the number of its rounds from the preset, and a count of up to `2^40` indices.

The earlier driver ran it at 10 and 90 rounds, on counts of at most 513.

A position is hashed in buckets of 256, whose number is written in four bytes.

So a count above `2^8`, `2^16` or `2^24` reaches bytes of that number that a small count leaves 0.

The arithmetic of slots, epochs and time reads three values of the preset and one of the config.

The earlier driver ran it at the minimal ones alone.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus

namespace ProtocolsProperty

/-- A count of indices: small, or around a power of two up to the limit of the registry. -/
def genIndexCount : Gen Nat :=
  Gen.frequency [
    (3, Gen.nat (.linear 0 600)),
    (4, do
      let power ← Gen.element [8, 9, 16, 17, 24, 25, 31, 32, 33, 39, 40]
      let nudge ← Gen.nat (.linear 0 3)
      let below ← Gen.bool
      pure (if below then 2 ^ power - nudge else min (2 ^ power + nudge) (2 ^ 40))),
    (2, Gen.nat (.exponential 1 (2 ^ 40))),
    (1, Gen.element [2 ^ 40 + 1, 2 ^ 63, 2 ^ 64 - 1])]

/-- The shuffled position of an index is that of consensus-specs, at any count and round count. -/
def shuffleAnywhere (oracle : Oracle) : Property IO := propertyM do
  let rounds ← forAll (Gen.frequency [(3, Gen.element [0, 1, 2, 9, 10, 11, 89, 90, 91, 254, 255]),
    (2, Gen.nat (.linear 0 255))])
  let count ← forAll genIndexCount
  let inside ← forAll (Gen.list (.linear 1 12) (Gen.frequency [
    (3, Gen.nat (.linear 0 (count - 1))),
    (3, (count - 1 - ·) <$> Gen.nat (.linear 0 (min (count - 1) 600))),
    (3, Gen.nat (.exponential 0 (count - 1)))]))
  -- One case of eight has an index at or past the count, which has no position.
  let outside ← forAll (Gen.frequency [(7, pure []),
    (1, (fun n => [count + n]) <$> Gen.nat (.linear 0 2))])
  let indices := inside ++ outside
  let seed ← forAllWith bytesHex (Gen.bytes (.singleton 32))
  pure do
    let preset := { Preset.minimal with SHUFFLE_ROUND_COUNT := UInt64.ofNat rounds }
    let seedVector : Bytes32 := Vector.ofFn fun i => seed[i.val]!
    let positions := indices.mapM fun index =>
      computeShuffledIndex preset (UInt64.ofNat index) (UInt64.ofNat count) seedVector
    let got := match positions with
      | .ok found => if found.isEmpty then "-" else ",".intercalate (found.map toString)
      | .error _ => "error"
    classify "refused" (got == "error")
    classify "a count above 2^16" (count > 2 ^ 16)
    classify "a count above 2^24" (count > 2 ^ 24)
    classify "a count above 2^32" (count > 2 ^ 32)
    classify "no round" (rounds == 0)
    -- EthLib refuses a count above `2^40`, where the reference has no bound of its own.
    if count > 2 ^ 40 then got === "error"
    else
      got === (← oracle.ask ["pp_shuffle", toString rounds, toString count, hex seed,
        ",".intercalate (indices.map toString)])

/-- The shuffle of a whole list gives the position of each index, at any round count. -/
def shuffleWhole : Property IO := pureIO do
  let rounds ← forAll (Gen.nat (.linear 0 255))
  let count ← forAll (Gen.frequency [(4, Gen.nat (.linear 0 300)),
    (1, Gen.element [255, 256, 257, 511, 512, 513, 1024, 1025, 3000])])
  let seed ← forAllWith bytesHex (Gen.bytes (.singleton 32))
  let preset := { Preset.minimal with SHUFFLE_ROUND_COUNT := UInt64.ofNat rounds }
  let seedVector : Bytes32 := Vector.ofFn fun i => seed[i.val]!
  let single := (List.range count).map fun i =>
    (computeShuffledIndex preset (UInt64.ofNat i) (UInt64.ofNat count) seedVector).toOption
  match computeShuffledPermutation preset (UInt64.ofNat count) seedVector with
  | .error _ => failWith "the whole-list shuffle is refused"
  | .ok whole => whole.toList.map some === single

/-- The arithmetic of slots, epochs and time is that of consensus-specs, at any constants. -/
def timeAnywhere (oracle : Oracle) : Property IO := propertyM do
  let slots ← forAll (Gen.element [1, 2, 3, 6, 8, 12, 32, 33, 1000])
  let lookahead ← forAll (Gen.element [0, 1, 4, 5, 255])
  let period ← forAll (Gen.element [1, 2, 3, 8, 256, 257])
  let duration ← forAll (Gen.element [1, 999, 1000, 1001, 6000, 12000, 12345])
  let a ← forAll genUInt64
  let b ← forAll (Gen.choice [genUInt64, UInt64.ofNat <$> Gen.nat (.linear 0 100000)])
  pure do
    let preset := { Preset.minimal with
      SLOTS_PER_EPOCH := UInt64.ofNat slots, MAX_SEED_LOOKAHEAD := UInt64.ofNat lookahead,
      EPOCHS_PER_SYNC_COMMITTEE_PERIOD := UInt64.ofNat period }
    let config := { Config.minimal with SLOT_DURATION_MS := UInt64.ofNat duration }
    let shown {ε : Type} (result : Except ε UInt64) : String :=
      match result with
      | .ok n => toString n.toNat
      | .error _ => "error"
    let agree (name : String) (got : String) : TestT IO Unit := do
      let expected ← oracle.ask ["pp_time", toString slots, toString lookahead, toString period,
        toString duration, name, toString a.toNat, toString b.toNat]
      annotate name
      got === expected
    agree "compute_epoch_at_slot" (toString (computeEpochAtSlot preset a).toNat)
    agree "compute_start_slot_at_epoch" (shown (computeStartSlotAtEpoch preset a))
    agree "compute_activation_exit_epoch" (shown (computeActivationExitEpoch preset a))
    agree "compute_sync_committee_period" (toString (computeSyncCommitteePeriod preset a).toNat)
    agree "compute_time_at_slot" (shown (computeTimeAtSlot config a b))
    agree "compute_slot_at_time" (shown (computeSlotAtTime config a b))
    agree "compute_time_at_slot_ms" (shown (computeTimeAtSlotMs config a b))
    agree "compute_slot_at_time_ms" (shown (computeSlotAtTimeMs config a b))
    agree "get_slot_component_duration_ms" (shown (getSlotComponentDurationMs config a))

/-- One entry of a list of typed requests: a type byte, then the bytes of that many requests.

Any bytes of a whole number of requests decode, since a request has no variable part. -/
def genRequestEntry : Gen ByteArray := do
  let type ← Gen.frequency [(10, Gen.nat (.constant 0 4)), (1, Gen.element [5, 6, 255])]
  let size := [192, 76, 116, 184, 68].getD type 40
  let count ← Gen.frequency [(1, pure 0), (6, Gen.nat (.linear 1 3)), (1, Gen.element [4, 6, 17])]
  let nudge ← Gen.frequency [(9, pure 0), (1, Gen.element [1, size - 1])]
  let data ← Gen.bytes (.singleton (count * size + nudge))
  pure (⟨#[UInt8.ofNat type]⟩ ++ data)

/-- The entries of a list of typed requests: mostly in the order of their types, each once. -/
def genRequestList : Gen (List ByteArray) := do
  let entries ← Gen.list (.linear 0 5) genRequestEntry
  let sorted := (entries.toArray.qsort fun a b => a[0]! < b[0]!).toList
  let once := sorted.eraseDupsBy fun a b => a[0]! == b[0]!
  Gen.frequency [(5, pure once), (1, pure sorted), (1, pure entries),
    (1, pure (ByteArray.empty :: once))]

/-- The requests that a list of typed requests decodes to are those of consensus-specs.

A list out of order, with a type twice, an unknown type or an entry without data is refused. -/
def requestsDecode (oracle : Oracle) : Property IO := propertyM do
  let presetKey ← forAllWith id (Gen.element ["minimal", oddLimits, "mainnet"])
  let (forkName, fork) ← forAllWith (·.1) (Gen.element [("electra", Fork.pectra),
    ("fulu", .fusaka), ("gloas", .glamsterdam), ("heze", .hegota)])
  let entries ← forAllWith (fun es => " ".intercalate (es.map hex)) genRequestList
  pure do
    let preset := (World.ofKeys presetKey "-").preset
    let got := match getExecutionRequests (preset := preset) (fork := fork) entries with
      | .error _ => "error"
      | .ok requests =>
        match Serialization.Ssz.SszType.hashTreeRoot requests with
        | .ok root => hex ⟨root.toArray⟩
        | .error _ => "unhashable"
    classify "refused" (got == "error")
    classify "some requests" (got != "error" && !entries.isEmpty)
    got === (← oracle.ask (["pp_requests", forkName, presetKey] ++ entries.map hex))

/-- The properties of the helpers that need no state. -/
def pureProperties (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("the shuffled position of an index, at any count and round count",
    (shuffleAnywhere oracle).withTests cases),
  ("the shuffle of a whole list, at any round count", shuffleWhole.withTests (max (cases / 10) 5)),
  ("slots, epochs and time, at any constants", (timeAnywhere oracle).withTests cases),
  ("the requests of a list of typed requests", (requestsDecode oracle).withTests cases)]

end ProtocolsProperty

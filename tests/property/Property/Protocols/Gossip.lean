import Property.Protocols.Light
import EthLib.Consensus.Gossip.Message

/-!
# Gossip rules of operations and sync committee messages

The earlier rounds checked the gossip of blocks, attestations, aggregates and attester slashings.

Here the rules of voluntary exits, proposer slashings and changes of BLS credentials run too.

So does the rule of a sync committee message, with its subnets.

The state of a case is the anchor of a fork choice store on both sides, so it is the head state.

A message is checked twice: the second check meets what the first one recorded as seen.

The signatures are the stand-in ones, so a wrong domain or key is rejected without a pairing.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ProtocolsProperty

/-- A setup of KZG that no rule here reads. -/
def unusedSetup : Cryptography.Kzg.TrustedSetup :=
  ⟨Vector.replicate _ default, Vector.replicate _ default, Vector.replicate _ default⟩

/-- A verdict as the oracle writes it. -/
def verdictText : Except ForkChoiceError (Networking.Gossip.ValidationResult × Seen) → String
  | .ok (.accept, _) => "accept"
  | .ok (.ignore _, _) => "ignore"
  | .ok (.reject _, _) => "reject"
  | .error _ => "error"

/-- The message of a kind from its bytes, with the subnet it travels on. -/
def gossipOf (preset : Preset) (fork : Fork) (kind subnet : UInt64) (bytes : ByteArray) :
    Except String (GossipMessage preset fork) :=
  let read (α : Type) [SszType α] : Except String α :=
    (SszType.deserialize α bytes).mapError fun e => s!"{repr e}"
  if kind = 0 then .voluntaryExit <$> read SignedVoluntaryExit
  else if kind = 1 then .proposerSlashing <$> read ProposerSlashing
  else if kind = 2 then .attesterSlashing <$> read (AttesterSlashing preset fork)
  else if kind = 3 then
    if capella : .shapella ≤ fork then
      .blsToExecutionChange capella <$> read SignedBLSToExecutionChange
    else .error "a change of credentials before Capella"
  else if altair : .altair ≤ fork then
    (.syncCommitteeMessage altair · subnet) <$> read SyncCommitteeMessage
  else .error "a sync committee message before Altair"

/-- The numbers of a message of each kind, after its kind, its clock and its subnet. -/
def genGossip (shape : Shape) : Gen (List String) := do
  let ahead ← Gen.frequency [(8, pure "0"), (1, pure "1"), (1, pure "2")]
  let subnet ← num (Gen.nat (.constant 0 3))
  let word (kind : Nat) (fields : List (Gen String)) : Gen (List String) :=
    (fun rest => [",".intercalate ([toString kind, ahead, subnet] ++ rest)]) <$> genFields fields
  Gen.frequency [
    (2, word 0 [num genIndex, genOperationEpoch, genOk]),
    (2, word 1 [num genIndex, num (Gen.nat (.linear 0 (110 * shape.slots))),
      num (Gen.frequency [(5, pure 0), (1, pure 1)]), genOk, genOk, pure "0", pure "0"]),
    (2, (fun head a => head ++ [a, "="]) <$>
      word 2 [num (Gen.nat (.constant 0 2)), genOk, genOk, pure "1", pure "1"] <*> genIndices),
    (2, word 3 [num genIndex, num (Gen.frequency [(3, pure 9), (1, Gen.nat (.linear 0 5))]),
      num (Gen.nat (.linear 0 5)), genOk]),
    (3, word 4 [num (Gen.frequency [(8, Gen.nat (.linear 0 12)), (1, genIndex)]),
      num (Gen.frequency [(8, pure 0), (1, pure 1)]), genOk, genOk,
      num (Gen.nat (.constant 0 3))])]

/-- The gossip rules, on a store whose anchor is the state of the case. -/
def gossipCalls (world : World) (checks : SignatureChecks) : List (Call world.preset) := [
  ⟨"gossip", allForks, genGossip world.shape, fun fork state words bytes =>
    let config := world.config
    match (words.headD "").splitOn ",", splitParts bytes with
    | kindText :: aheadText :: subnetText :: rest, [anchorBytes, messageBytes] =>
      let kind := kindText.toNat!.toUInt64
      -- A sync committee message travels on the subnet that its own numbers give.
      let subnet := if kind = 4 then (rest.getD 4 "0").toNat!.toUInt64
        else subnetText.toNat!.toUInt64
      match SszType.deserialize (BeaconBlock world.preset fork) anchorBytes,
          gossipOf world.preset fork kind subnet messageBytes with
      | .ok anchor, .ok message =>
        match getForkchoiceStore config state anchor with
        | .error e => .broken s!"EthLib refuses the anchor that the reference takes: {e}"
        | .ok store =>
          let timeMs := store.timeMs + aheadText.toNat!.toUInt64 * config.SLOT_DURATION_MS
          let check (seen : Seen) :=
            validateGossipMessage config checks unusedSetup seen store ∅ timeMs message
          let first := check {}
          let seen := match first with
            | .ok (_, next) => next
            | .error _ => {}
          .value s!"{verdictText first},{verdictText (check seen)}"
      | .error e, _ => .broken s!"EthLib does not read the anchor: {repr e}"
      | _, .error e => .broken s!"EthLib does not read the message: {e}"
    | _, _ => .broken "the argument is not an anchor and a message"⟩]

end ProtocolsProperty

import Property.Protocols.Transition
import EthLib.Consensus.LightClient.FullNode
import EthLib.Consensus.LightClient.Upgrade

/-!
# The light client update that a full node makes, and its upgrade to the next fork

The earlier rounds compared the bootstrap of a full node, and the store of a light client.

Here a full node makes an update from a block, its parent and their states.

The update carries two headers and two Merkle branches of the attested state.

Then the node derives the finality update and the optimistic update from it.

Last, the update is upgraded to the next fork that changes its shape.

The oracle builds the blocks and states so that they agree as the function asks, or nearly.

The four results are compared by their roots.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ProtocolsProperty

/-- A refusal of the light client is shown by its text, since the error has no `Repr`. -/
instance : Repr LightClientError := ⟨fun e _ => s!"{e}"⟩

/-- The values that the oracle wrote one after another, each after its length in four bytes. -/
partial def splitParts (bytes : ByteArray) (at_ : Nat := 0) : List ByteArray :=
  if at_ + 4 > bytes.size then []
  else
    let size := bytes[at_]!.toNat + bytes[at_ + 1]!.toNat * 256 + bytes[at_ + 2]!.toNat * 65536 +
      bytes[at_ + 3]!.toNat * 16777216
    bytes.extract (at_ + 4) (at_ + 4 + size) :: splitParts bytes (at_ + 4 + size)

/-- The root of a value in hexadecimal, or a refusal. -/
def rootText {α : Type} [SszType α] (value : α) : Except LightClientError String :=
  match SszType.hashTreeRoot value with
  | .ok root => pure (hexVector root)
  | .error e => throw (.ssz e)

/-- The root of an update upgraded to the next fork that changes it, or `-` where none does. -/
def upgradedRoot (world : World) {fork : Fork} (update : LightClientUpdate world.preset fork) :
    Except LightClientError String :=
  let next : Option Fork := match fork with
    | .altair | .bellatrix => some .shapella
    | .shapella => some .dencun
    | .dencun => some .pectra
    | .pectra | .fusaka => some .glamsterdam
    | _ => none
  match next with
  | none => pure "-"
  | some post =>
    if later : fork ≤ post then do
      rootText (← update.upgrade world.config post later)
    else pure "-"

/-- The light client calls of a full node. -/
def lightCalls (world : World) (_ : SignatureChecks) : List (Call world.preset) := [
  ⟨"create_light_client_update", forksFrom .altair,
    genWord [num (Gen.nat (.linear 0 200)), num (Gen.frequency [(3, pure 1), (1, pure 0),
      (1, pure 2)]), num (Gen.frequency [(8, pure 0), (1, Gen.nat (.constant 1 4))]),
      num (Gen.frequency [(5, pure 0), (1, Gen.nat (.linear 0 (3 * world.shape.slots))),
        (1, Gen.element (periodEdges world.shape |>.map (· * world.shape.slots)))])],
    fun fork attested _ bytes =>
    match splitParts bytes with
    | [stateBytes, blockBytes, attestedBytes, finalizedBytes] =>
      match SszType.deserialize (State world.preset fork) stateBytes,
          SszType.deserialize (SignedBeaconBlock world.preset fork) blockBytes,
          SszType.deserialize (SignedBeaconBlock world.preset fork) attestedBytes with
      | .ok state, .ok block, .ok attestedBlock =>
        let finalized : Except String (Option (SignedBeaconBlock world.preset fork)) :=
          if finalizedBytes.isEmpty then .ok none
          else match SszType.deserialize (SignedBeaconBlock world.preset fork) finalizedBytes with
            | .ok signed => .ok (some signed)
            | .error e => .error s!"{repr e}"
        match finalized with
        | .error e => .broken s!"EthLib does not read the finalized block: {e}"
        | .ok finalizedBlock =>
          .ofValue id (do
            let update ← createLightClientUpdate world.config state block attested attestedBlock
              finalizedBlock (Nat.le_refl _)
            let roots ← [rootText update, rootText (createLightClientFinalityUpdate update),
              rootText (createLightClientOptimisticUpdate update),
              upgradedRoot world update].mapM id
            pure (",".intercalate roots))
      | _, _, _ => .broken "EthLib does not read a block or the state of the reference"
    | _ => .broken "the argument is not four values"⟩]

end ProtocolsProperty

import Property.ForkChoice.Store
import Property.ForkChoice.Slashing
import Property.ForkChoice.Helpers
import Property.ForkChoice.LightClient

/-!
# The consensus protocols around the state transition, on generated inputs

    lake exe forkchoice-property            # 100 cases of each
    lake exe forkchoice-property 1000
    ONLY=phase0 lake exe forkchoice-property 1000   # The properties whose name holds a word.

The group `forkchoice: findings` holds the properties that are expected to fail: each shows a
place where EthLib and its source differ, with the counterexample.
Its failures do not change the exit code.
-/

open Hedgehog Support ForkChoiceProperty

/-- The forks at which the store runs, with their names in the pyspec. -/
def forks : List (EthLib.Base.Fork × String) :=
  [(.glamsterdam, "gloas"), (.fusaka, "fulu"), (.pectra, "electra"), (.dencun, "deneb"), (.shapella, "capella"),
    (.bellatrix, "bellatrix"), (.altair, "altair"), (.phase0, "phase0")]

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "forkchoice"
  let only := (← IO.getEnv "ONLY").getD ""
  let pick (group : List (String × Property IO)) :=
    group.filter fun (name, _) => only.isEmpty || (name.splitOn only).length > 1
  let store ← checkGroup "forkchoice: the store and gossip" (pick (forks.map fun (fork, name) =>
    (s!"the store and gossip agree with the pyspec at {name}",
      ((machine fork name oracle).property (.linear 1 40)).withTests cases)))
  let slashing ← checkGroup "forkchoice: slashing protection" (pick [
    ("a signer follows EIP-3076 (state machine)",
      (SlashingProperty.machine.property (.linear 1 60)).withTests cases),
    ("a signer follows EIP-3076 (madhouse)", SlashingProperty.madhouse.withTests cases),
    ("an integer of the interchange file", SlashingProperty.numbers.withTests cases)])
  let lightForks : List (EthLib.Base.Fork × String) :=
    [(.pectra, "electra"), (.dencun, "deneb"), (.shapella, "capella"), (.altair, "altair")]
  let light ← checkGroup "forkchoice: the light client store" (pick (lightForks.map
    fun (fork, name) => (s!"the light client store agrees with the pyspec at {name} (madhouse)",
      (LightClientProperty.madhouse fork name oracle).withTests cases)))
  let helpers ← checkGroup "forkchoice: helpers" (pick [
    ("is_better_update at deneb",
      (HelpersProperty.betterUpdate .dencun "deneb" oracle).withTests cases),
    ("is_better_update at electra",
      (HelpersProperty.betterUpdate .pectra "electra" oracle).withTests cases),
    ("is_better_update is a strict weak order", HelpersProperty.betterOrder.withTests cases),
    ("get_custody_groups", (HelpersProperty.custodyGroups oracle).withTests cases),
    ("compute_columns_for_custody_group", (HelpersProperty.custodyColumns oracle).withTests cases),
    ("compute_subnet_for_attestation", (HelpersProperty.attestationSubnet oracle).withTests cases),
    ("compute_subnet_for_data_column_sidecar",
      (HelpersProperty.columnSubnet oracle).withTests cases),
    ("compute_subscribed_subnets", (HelpersProperty.subscribedSubnets oracle).withTests cases),
    ("the weak subjectivity period of phase 0",
      HelpersProperty.weakSubjectivityPhase0.withTests cases),
    ("the weak subjectivity period of Electra",
      HelpersProperty.weakSubjectivityElectra.withTests cases)])
  -- Expected to fail: see findings/forkchoice.md.
  let _ ← checkGroup "forkchoice: findings" (pick [
    ("on_attestation takes every vote that the pyspec takes, at fulu",
      ((machine .fusaka "fulu" oracle (loose := true)).property (.linear 1 40)).withTests cases),
    ("on_attestation takes every vote that the pyspec takes, at phase0",
      ((machine .phase0 "phase0" oracle (loose := true)).property (.linear 1 40)).withTests
        cases)])
  pure (if store && slashing && light && helpers then 0 else 1)

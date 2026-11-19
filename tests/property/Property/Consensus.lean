import Property.Consensus.Epoch
import Property.Consensus.Operations
import Property.Consensus.Requests
import Property.Consensus.DepositTree
import Property.Consensus.Scenario
import Property.Consensus.Helpers
import Property.Consensus.Pure
import Property.Consensus.Genesis

/-!
# The beacon chain state transition, on generated inputs

    lake exe consensus-property                 # 100 cases of each
    lake exe consensus-property 1000
    lake exe consensus-property 1000 epoch      # One group.
    lake exe consensus-property 1000 process_slashings   # The properties so named.
-/

open Hedgehog Support ConsensusProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let wanted := args.filter fun arg => arg.toNat?.isNone
  let oracle ← Oracle.start "consensus"
  -- The scenarios run in madhouse mode whatever the environment says; the scripted order
  -- runs once beside it.
  let scenarios ← allForks.mapM fun (forkName, fork) => do
    let chaos ← blockScenario oracle forkName fork .madhouse
    let script ← blockScenario oracle forkName fork .deterministic
    pure [(s!"the operations of a block in any order, {forkName}", chaos.withTests cases),
      (s!"the operations of a block in order, {forkName}", script)]
  let groups : List (String × List (String × Property IO)) := [
    ("pure", pureProperties oracle cases),
    ("genesis", [("the genesis state of generated deposits", (genesis oracle).withTests cases)]),
    ("deposit-tree", [("the deposit tree against a list of leaves",
      (depositTree oracle).withTests cases)]),
    ("scenario", scenarios.flatten),
    ("epoch", stepProperties oracle cases),
    ("operations", callProperties oracle cases genOperationState operations),
    ("requests", requestProperties oracle cases),
    ("blocks", callProperties oracle cases genOperationState blocks),
    ("accessors", callProperties oracle cases genOperationState accessors),
    ("mutators", callProperties oracle cases genOperationState mutators),
    ("upgrades", callProperties oracle cases genUpgradeState upgrades)]
  -- A word that names a group selects it; any other word selects the properties it is part of.
  let names := groups.map (·.1)
  let wantedGroups := wanted.filter names.contains
  let wantedParts := wanted.filter (!names.contains ·)
  let mut ok := true
  for (name, properties) in groups do
    let whole := wanted.isEmpty || wantedGroups.contains name
    let properties := properties.filter fun (label, _) =>
      whole || wantedParts.any fun part => (label.splitOn part).length > 1
    if !properties.isEmpty then
      ok := (← checkGroup s!"consensus: {name}" properties) && ok
      -- How often the reference accepted, left unchanged, refused and skipped: a group that
      -- only refuses tests little.
      oracle.stdin.putStrLn "stats"
      oracle.stdin.flush
      let counts := (← oracle.stdout.getLine).trimAsciiEnd
      IO.println s!"  accepted/unchanged/refused/skipped: {counts}"
  pure (if ok then 0 else 1)

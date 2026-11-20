import Property.Protocols.Blocks
import Property.Protocols.Duties
import Property.Protocols.Light
import Property.Protocols.Gossip
import Property.Protocols.Confirmation
import Property.Protocols.Optimistic
import Property.Protocols.Lists
import Property.Protocols.Pure

/-!
# The consensus protocols, on generated inputs

    lake exe protocols-property                 # 100 cases of each
    lake exe protocols-property 1000
    HEDGEHOG_ONLY=process_slashings lake exe protocols-property 1000
    PROTOCOLS_GROUP=epoch lake exe protocols-property 1000   # One group.
-/

open Hedgehog Support ProtocolsProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let only := (← IO.getEnv "PROTOCOLS_GROUP").map (·.splitOn ",")
  let selection ← Selection.fromEnv
  let oracle ← Oracle.start "protocols"
  -- A minimum of coverage is set from runs of 1,000 cases, and a short run has only small cases.
  --
  -- So the scenarios ask for their minimums from 100 cases on.
  let long := cases ≥ 100
  let worlds := genWorld
  -- Four states of five have every field filled, and one of six has two validators of one key.
  let standin (calls : Calls) (genWords : Shape → Gen (List String)) (suffix : String := "") :=
    callProperties oracle cases worlds "standin" standIn calls (filled genWords) suffix
  -- Real BLS is slower, so these properties run a quarter of the cases.
  let signed := ["process_voluntary_exit", "process_proposer_slashing", "process_attester_slashing",
    "process_attestation", "process_bls_to_execution_change", "process_deposit",
    "process_builder_deposit_request", "process_execution_payload_bid", "process_sync_aggregate",
    "process_pending_deposits", "upgrade_to_gloas", "process_block", "process_block_full",
    "state_transition", "process_payload_attestation"]
  let real (calls : Calls) (genWords : Shape → Gen (List String)) (suffix : String) :=
    (callProperties oracle (max (cases / 4) 5) worlds "real" EthLib.Consensus.SignatureChecks.bls
      calls (filled genWords) suffix).filter fun (name, _) =>
        signed.any fun call => name.startsWith call
  -- The whole state of mainnet is three megabytes, so these run a twentieth of the cases.
  let mainnet (calls : Calls) (genWords : Shape → Gen (List String)) :=
    callProperties oracle (max (cases / 20) 5) (World.ofKeys "mainnet" <$> genConfigKey)
      "standin" standIn calls (filled genWords) ", mainnet"
  -- The same calls at the forks of the execution layer that lie between consensus forks.
  let between (calls : Calls) (genWords : Shape → Gen (List String)) :=
    callProperties oracle cases worlds "standin" standIn calls (filled genWords)
      ", between forks" (between := true)
  let groups : List (String × List (String × Property IO)) := [
    ("epoch", standin steps genState),
    ("epoch-settled", standin steps genOperationState ", settled validators"),
    ("operations", standin operations genOperationState),
    ("blocks", standin blocks genBlockState),
    ("blocks-gloas", standin gloasBlocks genBlockState ", from Gloas"),
    ("accessors", standin accessors genOperationState),
    ("mutators", standin mutators genOperationState),
    ("upgrades", standin upgrades genUpgradeState),
    ("whole-blocks", standin wholeBlocks genBlockState),
    ("duties", standin duties genBlockState),
    ("across", callProperties oracle cases genForkingWorld "standin" standIn acrossCalls
      (filled genEarlyState)),
    ("light-client", standin lightCalls genBlockState),
    ("gossip", standin gossipCalls genBlockState),
    ("real-bls", real operations genOperationState ", real BLS" ++
      real steps genState ", real BLS" ++
      real upgrades genUpgradeState ", real BLS" ++
      real blocks genBlockState ", real BLS" ++
      real gloasBlocks genBlockState ", from Gloas, real BLS" ++
      real wholeBlocks genBlockState ", real BLS" ++
      real duties genBlockState ", real BLS"),
    ("between", between steps genOperationState ++ between operations genOperationState ++
      between accessors genOperationState ++ between mutators genOperationState ++
      between wholeBlocks genBlockState ++ between duties genBlockState),
    ("mainnet", mainnet steps genOperationState ++ mainnet operations genOperationState ++
      mainnet accessors genOperationState ++ mainnet mutators genOperationState ++
      mainnet upgrades genUpgradeState ++ mainnet wholeBlocks genBlockState)]
  let forkChoiceForks : List (EthLib.Base.Fork × String) :=
    [(.glamsterdam, "gloas"), (.fusaka, "fulu"), (.pectra, "electra"), (.dencun, "deneb"),
      (.shapella, "capella"), (.bellatrix, "bellatrix"), (.altair, "altair"), (.phase0, "phase0")]
  let groups := groups ++ [
    ("confirmation", forkChoiceForks.map fun (fork, name) =>
      (s!"the fast confirmation rule agrees with the reference at {name}",
        ((ConfirmationProperty.machine fork name oracle long).property (.linear 1 30)).withTests
          cases)),
    ("optimistic", (forkChoiceForks.filter fun (fork, _) =>
        .bellatrix ≤ fork && fork < .glamsterdam).map fun (fork, name) =>
      (s!"the optimistic store follows the guide at {name} (madhouse)",
        (OptimisticProperty.madhouse fork name oracle long).withTests cases))]
  let groups := groups ++ [
    ("pure", pureProperties oracle cases),
    ("lists", [("the store of inclusion lists follows consensus-specs (madhouse)",
      (ListsProperty.madhouse oracle long).withTests cases)])]
  let mut ok := true
  for (name, properties) in groups do
    if only.all (·.contains name) then
      ok := (← checkGroup s!"protocols: {name}" properties selection) && ok
      -- With `ORACLE_REASONS=1` the oracle prints where the reference refused, to tune a generator.
      if (← IO.getEnv "ORACLE_REASONS").isSome then
        oracle.stdin.putStrLn "stats"
        oracle.stdin.flush
        let _ ← oracle.stdout.getLine
  pure (if ok then 0 else 1)

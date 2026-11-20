import Property.Transition.Chain
import Property.Transition.Ledger
import Property.Transition.Size

/-!
# The transaction and the block transition, on generated worlds

Each property runs a whole transaction or a whole block in EthLib and in the reference.

The reference is the Python execution-specs (`oracle/transition.py`).

    lake exe transition-property            # 100 cases of each
    lake exe transition-property 1000
-/

open Hedgehog Support TransitionProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let setup ← Setup.start
  let selection ← Selection.fromEnv
  let ok ← checkGroup "transition" [
    ("a transaction leaves what the reference leaves", (oneTransaction setup).withTests cases),
    ("both sides refuse a transaction for the same reason",
      (refusalReason setup).withTests cases),
    ("a block is valid as in the reference, and leaves the same state",
      (wholeBlock setup).withTests cases),
    ("state machine: the transfers of a block leave the ledger of a model",
      ((ledgerMachine (decide (cases ≥ 300))).property (.linear 1 40)).withTests cases),
    ("a block passes the size rule exactly up to 8 MiB, from Fusaka",
      blockSize.withTests (min cases 200))] selection
  -- Scenarios of commands, in madhouse mode whatever the environment says.
  --
  -- A sequence is up to 50 commands, so each fork runs a tenth of the cases.
  let scenarios ← checkGroup "transition: scenarios" (scenarioForks.map fun fork =>
    (s!"scenario: a chain under commands at {fork.1.name}",
      chainScenario setup fork (max 10 (cases / 10)))) selection
  -- Glamsterdam, beside the branch of the reference that has it, if it is installed.
  let glamsterdam ← match setup.glamsterdam with
    | some _ =>
      let fork : EthLib.Base.Fork × String := (.glamsterdam, "amsterdam")
      checkGroup "transition: Glamsterdam" [
        ("a transaction at Glamsterdam leaves what the reference leaves",
          (oneTransaction setup (some fork)).withTests cases),
        ("a block at Glamsterdam is valid as in the reference, and leaves the same state",
          (wholeBlock setup (some fork)).withTests cases)] selection
    | none =>
      IO.println "Glamsterdam is skipped: see oracle/requirements-evm.txt for its reference."
      pure true
  -- A difference that EthLib documents: it must fail, and the group says so if it stops.
  if setup.glamsterdam.isSome then
    let _ ← checkGroup "transition: known differences (expected to fail)" [
      ("DOC: a creation over storage alone at Glamsterdam ends as in the branch",
        (storageOnlyCreation setup).withTests 100)] selection (mustFail := true)
  pure (if ok && scenarios && glamsterdam then 0 else 1)

import Property.Evm.Whole
import Property.Evm.Precompile
import Property.Evm.Machine
import Property.Evm.Fees
import Property.Evm.Pure
import Property.Evm.Tables

/-!
# The EVM, on generated inputs

Each property generates inputs and requires an answer that EthLib did not compute.

It is that of the Python execution-specs (`oracle/evm.py`), or of a model written from the EIPs.

    lake exe evm-property            # 100 cases of each
    lake exe evm-property 1000
    HEDGEHOG_ONLY="a message leaves" EVM_OPCODE_TABLE=1 lake exe evm-property 1000

`HEDGEHOG_ONLY` and `HEDGEHOG_RECHECK` select properties and replay a case, as lean-hedgehog reads.

`EVM_OPCODE_TABLE` prints the share of the programs of each fork in which each opcode ran.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Evm

open EvmProperty in
def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let selection ← Selection.fromEnv
  let oracle ← Oracle.start "evm"
  let programs ← IO.mkRef ({} : OpCounts)
  let frames ← IO.mkRef ({} : OpCounts)
  -- A minimum of `cover` is a share of a run of 1,000 cases, and a short run stays below it.
  let asked := cases ≥ 500 && selection.recheck.isNone
  -- The branch of the reference with Glamsterdam is installed apart, so it may be absent.
  let specs := (← IO.getEnv "ETHLIB_AMSTERDAM_SPECS").getD ".venv/evm-amsterdam"
  let amsterdam ← if ← System.FilePath.pathExists specs then some <$> Oracle.start "evm_amsterdam"
    else do
      IO.println s!"no reference of Glamsterdam at {specs}: its properties are skipped"
      pure none
  let properties : List (String × Property IO) := [
    ("a message leaves what the reference leaves",
      (wholeProgram oracle programs asked).withTests cases),
    ("a message of accounts that destroy themselves leaves what the reference leaves",
      (wholeProgram oracle programs asked (destroys := true)).withTests cases),
    ("a full stack and a full depth of calls leave what the reference leaves",
      (deepLimits oracle asked).withTests (cases / 10))] ++
    precompileProperties oracle cases asked ++ [
    ("arithmetic and bitwise instructions on integers", (arithmetic asked).withTests (10 * cases)),
    ("EXP is the power modulo 2^256", (exponent asked).withTests cases),
    ("the valid jump destinations", (jumpDests oracle).withTests cases),
    ("the addresses of CREATE and CREATE2", (contractAddress oracle asked).withTests cases),
    ("the growth of memory", (memoryGrowth oracle asked).withTests cases),
    ("the base fee of EIP-1559", (baseFee oracle asked).withTests cases),
    ("a gas limit may follow its parent's", (gasLimitRule oracle asked).withTests cases),
    ("fakeExponential is fake_exponential of EIP-4844", (fakeExponential oracle).withTests cases),
    ("the excess blob gas and the blob gas price", (blobGas oracle asked).withTests cases),
    ("the gas of a call, with all but one 64th", (callGas oracle asked).withTests cases)] ++
    tableProperties oracle amsterdam ++
    (match amsterdam with
    | some amsterdam =>
      [("a call at Glamsterdam leaves what the branch of the reference leaves",
        (glamsterdam amsterdam programs asked).withTests cases)]
    | none => []) ++ [
    ("SLOAD and SSTORE follow the model of the EIPs (StateMachine)",
      ((storageMachine asked).property (.linear 1 40)).withTests cases),
    ("DUPN, SWAPN and EXCHANGE follow the list of EIP-8024 (StateMachine)",
      ((deepStackMachine asked).property (.linear 1 30)).withTests cases)] ++
    -- Every fork steps a frame: a third of the cases each, since there are 24.
    forks.flatMap fun (fork, name) =>
      let ctx : FrameContext fork := ⟨name, oracle, frames, asked⟩
      [(s!"a frame steps as the reference at {fork.name} (Command, madhouse)",
        (frameScenario .madhouse fork ctx).withTests (cases / 3)),
       (s!"a frame steps as the reference at {fork.name} (Command, in order)",
        frameScenario .deterministic fork { ctx with asked := false })]
  let ok ← checkGroup "evm" properties selection
  let full := (← IO.getEnv "EVM_OPCODE_TABLE").isSome
  printOpCounts "whole programs" (← programs.get) full
  -- A command of a frame is short, so its opcodes are counted, not given as a share.
  printOpCounts "the commands of the frame scenario" (← frames.get) full (percent := false)
  -- What the campaign found: these fail by design, and the group holds while each still fails.
  let findings ← match amsterdam with
    | some amsterdam => checkGroup "evm: findings" [
        ("DELEGATECALL and STATICCALL record no read of the running account",
          (delegatecallReads amsterdam).withTests 20)] selection (mustFail := true)
    | none => pure true
  pure (if ok && findings then 0 else 1)

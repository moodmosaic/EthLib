import Property.Evm.Program

/-!
# Glamsterdam beside the branch of the reference

No release of the Python execution-specs has Glamsterdam.

So the reference is its branch `forks/amsterdam` at one commit, in `oracle/evm_amsterdam.py`.

The fork is not final: a disagreement may be a change of an EIP after the text that EthLib cites.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Evm

namespace EvmProperty

/-- What a frame of Glamsterdam left, in the text form of `oracle/evm_amsterdam.py`. -/
def showGlamsterdam (accounts : List PreAccount) (evm : Evm .glamsterdam StateGasMeter) : String :=
  let status := match evm.error with
    | none => "ok"
    | some .revert => "revert"
    | some _ => "halt"
  let deleted := (evm.substate.accountsToDelete.toList.toArray.qsort addressLt).toList
  let tail := if evm.error.isNone then
      s!"{evm.substate.refundCounter} {showLogs evm.substate.logs} \
        {if deleted.isEmpty then "-" else ",".intercalate (deleted.map hexVec)}"
    else "0 - -"
  let join (words : List String) : String :=
    if words.isEmpty then "-" else ",".intercalate (words.toArray.qsort (· < ·)).toList
  -- A transaction reads its sender and its recipient before the frame starts.
  let accountReads := join (((evm.state.accountReads.insert callerAddress).insert
    targetAddress).toList.map hexVec)
  let storageReads := join (evm.state.storageReads.toList.flatMap fun (address, keys) =>
    keys.toList.map fun key => s!"{hexVec address}:{hexVec key}")
  s!"{status} {evm.gas.gasLeft} {evm.gas.reservoir} {hex evm.output} {tail} \
    {showState accounts evm.state} {accountReads} {storageReads} {showTransient evm.state}"

/-- Run a call at Glamsterdam in EthLib, with a reservoir of state gas. -/
def runGlamsterdam (static : Bool) (gas reservoir value : Nat) (data code : ByteArray)
    (accounts : List PreAccount) : String × String :=
  let message := { messageOf .glamsterdam false static gas value data code with reservoir }
  match processMessage (Meter := StateGasMeter) .glamsterdam message (txState accounts)
      startSubstate with
  | .error e => (s!"abort {reprStr e}", "")
  | .ok ⟨evm, _⟩ => (showGlamsterdam accounts evm, reprStr evm.error)

end EvmProperty

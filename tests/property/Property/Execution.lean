import Property.Execution.Tx
import Property.Execution.Trie
import Property.Execution.Forged
import Property.Execution.Range
import Property.Execution.Blocks
import Property.Execution.State

/-!
# The execution chain, on generated inputs

    lake exe execution-property            # 100 cases of each
    lake exe execution-property 1000
    HEDGEHOG_ONLY="trie,proof" lake exe execution-property 5000

A run of 1,000 cases or more also asks the minimums of coverage.

The forks after BPO2 are compared with a branch of the reference, if it is installed.
-/

open Hedgehog Support ExecutionProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  -- The minimums of coverage are those of a run of 1,000 cases, and hold from there on.
  longRun.set (1000 ≤ cases)
  let oracle ← Oracle.start "execution"
  -- The later branch of the reference, for the forks that no release has, if it is installed.
  let specs := (← IO.getEnv "ETHLIB_AMSTERDAM_SPECS").getD ".venv/evm-amsterdam"
  let late ← if ← System.FilePath.pathExists specs then
      some <$> Oracle.start "execution_amsterdam"
    else
      IO.println "BPO3 to Hegotá are skipped: see oracle/requirements-evm.txt for their reference."
      pure none
  let oracles : Oracles := ⟨oracle, late⟩
  let selection ← Selection.fromEnv
  let ok ← checkGroup "execution" [
    ("a transaction as bytes is the reference's", (transactionBytes oracles).withTests cases),
    ("a signed transaction is valid as in the reference", (signedValid oracles).withTests cases),
    ("a transaction in a block body is the reference's", (bodyTransaction oracles).withTests cases),
    ("a transaction of eth-account reads back", (signedTransaction oracle).withTests cases),
    ("the authority of an authorization is the reference's",
      (authorityOf oracle).withTests cases),
    ("a transaction passes the rules that read no state, each at its edge",
      staticRules.withTests cases),
    ("the sender of a transaction passes the rules of its EIPs", senderRules.withTests cases),
    ("the root of a trie is the reference's", (trieRoot oracle).withTests cases),
    ("the root of a trie under another hash is the reference's",
      (trieOtherHash oracle).withTests cases),
    ("the proof of a key is py-trie's", (trieProof oracle).withTests cases),
    ("an accepted proof does not lie", (trieProofSound oracle).withTests cases),
    ("state machine: a trie under writes, beside py-trie",
      ((trieMachine oracle).property (.linear 1 40)).withTests cases),
    ("the logs bloom is the reference's", (bloomFilter oracle).withTests cases),
    ("a header as bytes is the reference's", (headerBytes oracles).withTests cases),
    ("a header after its parent is valid as in the reference",
      (headerAfterParent oracle).withTests cases),
    ("the first header of a fork is valid as the sources say",
      (headerAcrossForks oracle).withTests cases),
    ("the ommers of a block are valid as in the reference", (ommersValid oracle).withTests cases),
    ("a receipt as bytes is the reference's", (receiptBytes oracles).withTests cases),
    ("the receipts of a block count its gas", receiptsOfBlock.withTests cases),
    ("the difficulty of a block is the reference's", (difficulty oracle).withTests cases),
    ("the rewards of a block are the reference's", (rewards oracle).withTests cases),
    ("the requests hash is EIP-7685's", (requestsHashOf oracle).withTests cases),
    ("the deposit request of a log is the reference's", (depositRequest oracle).withTests cases),
    ("the root of a list is the reference's", (listRoots oracle).withTests cases),
    ("the DAO Fork moves the accounts of EIP-779", (daoFork oracle).withTests cases),
    ("state machine: the tracker reads as a model that copies its state",
      (trackerMachine.property (.linear 1 60)).withTests cases)] selection
  let tries ← checkGroup "execution: hex-prefix, and tries built node by node" [
    ("hex-prefix writes the bytes of the reference, at every length",
      (hexPrefixEncode oracle).withTests cases),
    ("hex-prefix reads exactly the encodings", (hexPrefixDecode oracle).withTests cases),
    ("a proof of a trie built node by node shows what its nodes say",
      (forgedProof oracle).withTests cases),
    ("a proof whose path meets an item that is no node is refused", brokenNode.withTests cases),
    ("a range of a trie is accepted exactly when it is true",
      (rangeProof oracle).withTests cases)] selection
  let proofs ← checkGroup "execution: account proofs" [
    ("an answer of eth_getProof holds exactly when it is true", accountProofs.withTests cases)]
    selection
  -- Scenarios of commands, in madhouse mode whatever the environment says.
  let scenarios ← checkGroup "execution: scenarios" (trackerForks.map fun fork =>
    (s!"scenario: the tracker beside state.py at {fork.2}",
      (trackerScenario .madhouse ⟨oracle, fork⟩).withTests cases)) selection
  -- What the campaign found: each of these must fail, and shows its counterexample.
  --
  -- The group does not change the exit code.
  let _ ← checkGroup "execution: findings (each must fail)" [
    ("OPEN: the empty proof shows absence in the empty trie",
      (emptyTrieProof oracle).withTests 100),
    ("OPEN: go-ethereum's answer for a slot of an empty storage holds",
      emptyStorageAnswer.withTests 100)] selection (mustFail := true)
  pure (if ok && tries && proofs && scenarios then 0 else 1)

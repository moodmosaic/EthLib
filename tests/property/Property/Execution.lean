import Property.Execution.Tx
import Property.Execution.Trie
import Property.Execution.Blocks
import Property.Execution.State

/-!
# The execution chain, on generated inputs

    lake exe execution-property            # 100 cases of each
    lake exe execution-property 1000
-/

open Hedgehog Support ExecutionProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "execution"
  let ok ← checkGroup "execution" [
    ("a transaction as bytes is the reference's", (transactionBytes oracle).withTests cases),
    ("a transaction of eth-account reads back", (signedTransaction oracle).withTests cases),
    ("the sender of a transaction passes the rules of its EIPs", senderRules.withTests cases),
    ("the root of a trie is the reference's", (trieRoot oracle).withTests cases),
    ("the proof of a key is py-trie's", (trieProof oracle).withTests cases),
    ("an accepted proof does not lie", (trieProofSound oracle).withTests cases),
    ("state machine: a trie under writes, beside py-trie",
      ((trieMachine oracle).property (.linear 1 40)).withTests cases),
    ("the logs bloom is the reference's", (bloomFilter oracle).withTests cases),
    ("a header as bytes is the reference's", (headerBytes oracle).withTests cases),
    ("a header after its parent is valid as in the reference",
      (headerAfterParent oracle).withTests cases),
    ("the ommers of a block are valid as in the reference", (ommersValid oracle).withTests cases),
    ("a receipt as bytes is the reference's", (receiptBytes oracle).withTests cases),
    ("the difficulty of a block is the reference's", (difficulty oracle).withTests cases),
    ("the rewards of a block are the reference's", (rewards oracle).withTests cases),
    ("the requests hash is EIP-7685's", (requestsHashOf oracle).withTests cases),
    ("the deposit request of a log is the reference's", (depositRequest oracle).withTests cases),
    ("the root of a list is the reference's", (listRoots oracle).withTests cases),
    ("the DAO Fork moves the accounts of EIP-779", (daoFork oracle).withTests cases),
    ("state machine: the tracker reads as a model that copies its state",
      (trackerMachine.property (.linear 1 60)).withTests cases)]
  let proofs ← checkGroup "execution: account proofs" [
    ("an answer of eth_getProof holds exactly when it is true", accountProofs.withTests cases)]
  -- Scenarios of commands, in madhouse mode whatever the environment says.
  let scenarios ← checkGroup "execution: scenarios" (trackerForks.map fun fork =>
    (s!"scenario: the tracker beside state.py at {fork.2}",
      (trackerScenario .madhouse ⟨oracle, fork⟩).withTests cases))
  -- What the campaign found: each of these is expected to fail, and shows its counterexample.
  let _ ← checkGroup "execution: findings (expected to fail)" [
    ("OPEN: the empty proof shows absence in the empty trie",
      (emptyTrieProof oracle).withTests 100),
    ("OPEN: go-ethereum's answer for a slot of an empty storage holds",
      emptyStorageAnswer.withTests 100)]
  pure (if ok && proofs && scenarios then 0 else 1)

import Property.Rpc.Getters
import Property.Rpc.Call
import Property.Rpc.Wire
import Property.Rpc.Era
import Property.Rpc.Snap
import Property.Rpc.Node
import Property.Rpc.Status

/-!
# The RPC of the execution layer, its wire messages and its history files

    lake exe rpc-property            # 100 cases of each property
    lake exe rpc-property 1000
    HEDGEHOG_ONLY="fee history" lake exe rpc-property 1000
-/

open Hedgehog Support RpcProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "rpc"
  let keys := (((← askIO oracle ["keys"]).splitOn ",").filterMap (vector? 20)).toArray
  if keys.size ≠ 8 then throw (IO.userError "the oracle gave no keys")
  let ok ← checkGroup "rpc" [
    ("fee history: eth_feeHistory is the model's", (feeHistory oracle).withTests cases),
    ("logs: eth_getLogs is a scan of the receipts", (getLogs oracle).withTests cases),
    ("getters: blocks, transactions, receipts and raw forms", (getters oracle).withTests cases),
    ("call: eth_call leaves what the message leaves in EELS",
      (ethCall oracle (keys.extract 0 4)).withTests cases),
    ("estimate: eth_estimateGas is the binary search on EELS",
      (estimateGas oracle (keys.extract 0 4)).withTests cases),
    ("state: the state getters and eth_getProof",
      (stateGetters oracle (keys.extract 0 4)).withTests cases),
    ("eth: a message reads as eth.md says, at every version",
      (ethDecode oracle).withTests (5 * cases)),
    ("snap: a message reads as snap.md says, at both versions",
      (snapDecode oracle).withTests (5 * cases)),
    ("eth: the fork identifier of a head is EIP-2124's", (forkIdOfHead oracle).withTests cases),
    ("eth: a Status is accepted as the rules say", (statusCheck oracle).withTests cases),
    ("eth: headers answer a GetBlockHeaders", (headersAnswer oracle).withTests cases),
    ("eth: transactions answer a GetPooledTransactions", (pooledAnswer oracle).withTests cases),
    ("snap: the value of a slim account", (slimAccountValue oracle).withTests cases),
    ("state machine: the walk of snap over account ranges",
      ((walkMachine oracle).property (.linear 1 12)).withTests cases),
    ("scenario: a node under commands answers as the model", nodeScenario oracle (cases / 2)),
    ("era1: a file reads back, and a fault is refused", (era1File oracle).withTests cases),
    ("era1: the limit of 8192 blocks", (era1Limit oracle).withTests 6),
    ("errors: an error shows its constructor and its named values", errorFormat.withTests cases)]
    (← Selection.fromEnv)
  -- What EthLib does not do as its text says: each property fails by design.
  let found ← checkGroup "rpc: findings" [
    ("finding: a precompile that lacks gas gets code 801",
      (precompileLacksGas oracle).withTests cases),
    ("finding: an AccountRange with a nested account body is read",
      nestedAccountBody.withTests cases)]
    (← Selection.fromEnv) (mustFail := true)
  pure (if ok && found then 0 else 1)

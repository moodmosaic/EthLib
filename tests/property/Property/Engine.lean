import Property.Engine.Wire
import Property.Engine.Jwt
import Property.Engine.NewPayload
import Property.Engine.Forkchoice
import Property.Engine.Stores
import Property.Engine.Node

/-!
# The Engine API, on generated inputs

    lake exe engine-property            # 100 cases of each
    lake exe engine-property 2000
-/

open Hedgehog Support EngineProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "engine"
  let selection ← Selection.fromEnv
  let ok ← checkGroup "engine" [
    ("a base type reads as base-types.yaml says", (wireSchema oracle).withTests cases),
    ("a quantity is written as both patterns ask", (quantityWrites oracle).withTests cases),
    ("data is written as both patterns ask", (dataWrites oracle).withTests cases),
    ("a token passes as the Engine profile says", (jwtChecks oracle).withTests cases),
    ("a built token verifies under PyJWT", (jwtBuilds oracle).withTests cases),
    ("newPayload answers as its specification says", (newPayloadMatrix oracle).withTests cases),
    ("forkchoiceUpdated chooses the head as its model does",
      (forkchoiceMachine.property (.linear 1 40)).withTests cases),
    ("forkchoiceUpdated answers payload attributes as its specification says",
      (forkchoiceAttributes oracle).withTests cases),
    ("payload bodies are read as their model reads them",
      (bodyMachine.property (.linear 1 40)).withTests cases),
    ("getBlobs reads the pool as its specification says", blobsRead.withTests (cases / 4)),
    ("a method name carries its version", (methodNames oracle).withTests cases),
    ("the methods are those of the specification", (methodList oracle).withTests 1),
    ("a structure of a response reads as its fields say", (responsesRead oracle).withTests cases),
    ("an error has the code and the message of common.md", errorsOfTable.withTests 1),
    ("each error code of common.md is an error of EthLib", errorsComplete.withTests 1),
    ("a node answers its calls, in madhouse mode", (nodeScenario oracle).withTests cases),
    ("a node answers long sequences of calls", (nodeLongScenario oracle).withTests (cases / 4))]
    selection
  -- The property of this group states what EthLib does not do, and must fail.
  let findings ← checkGroup "engine: findings" [
    ("a base type reads as the Encoding of common.md says", (wireEncoding oracle).withTests cases)]
    selection (mustFail := true)
  pure (if ok && findings then 0 else 1)

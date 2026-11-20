import Property.Rpc.Getters

/-!
# A node under commands

A node is a chain and methods, so a scenario of commands grows one chain and asks about it.

The state is the chain as plain fields, and the context holds the oracle.

A command that asks is generated for the chain that the commands before it lead to.

So a filter names blocks that exist by then, and a getter a transaction that a block holds.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Blocks EthLib.Execution.Transactions EthLib.Execution.Rpc
open Lean (Json)
open EthLib.Serialization.JsonRpc (RpcError)

namespace RpcProperty

/-- What the commands of a scenario are built from. -/
structure NodeContext where
  oracle : Oracle
  /-- Whether the run is long enough to ask for a share of each kind of command. -/
  long : Bool

/-- The state of a scenario: the chain of the node, and how many blocks the commands added. -/
structure NodeState where
  chain : ChainSpec
  sealed : Nat

/-- The chain as the view of fees that the model of the fee history reads. -/
def ChainSpec.fees (c : ChainSpec) : FeeView :=
  let block (b : BlockSpec) : FeeBlock := ⟨b.fork, b.header, b.txs.map fun t =>
    ⟨t.spec.type, t.spec.gasPrice, t.spec.maxFee, t.spec.priorityFee, t.gasUsed⟩⟩
  ⟨c.activations, [], c.blocks.map block, c.pending.map block, c.safe, c.finalized⟩

/-- Add a block to the chain, after its head. -/
structure Seal where
  block : BlockSpec

instance : Command Seal NodeState NodeContext IO where
  -- A block made for another head, after a shrink removed a command, is left out.
  check _ c s := (s.chain.blocks.getLast?.map (·.header.number + 1)) = some c.block.header.number
  apply ctx c s := do
    cover (if ctx.long then 30 else 0) "a block is added" true
    classify "a third block is added" (s.sealed ≥ 2)
    -- The run moves the state here, and `next` moves it for the generators of later commands.
    pure { s with chain := { s.chain with blocks := s.chain.blocks ++ [c.block] }
                  sealed := s.sealed + 1 }
  label c := s!"SEAL block {c.block.header.number} with {c.block.txs.length} transactions"
  build _ := pure ⟨⟨.frontier, { number := 0, time := 0, gasLimit := 0, gasUsed := 0, baseFee := 0
                                 excessBlobGas := 0, blobGasUsed := 0 }, []⟩⟩
  next _ c s := { s with chain := { s.chain with blocks := s.chain.blocks ++ [c.block] }
                         sealed := s.sealed + 1 }
  buildIn _ s := do
    let head := (s.chain.blocks.getLast?.map (·.header)).getD
      { number := 0, time := 0, gasLimit := 0, gasUsed := 0, baseFee := 0, excessBlobGas := 0
        blobGasUsed := 0 }
    let start := ((s.chain.blocks.head?.map (·.fork)).getD .frontier)
    let gap ← Gen.element [1, 12]
    Seal.mk <$> genBlockSpec s.chain.config start (head.number + 1) (head.time + gap) 0

/-- Name a block of the chain as safe and as finalized, as the consensus layer does. -/
structure Mark where
  safe : Nat
  finalized : Nat

instance : Command Mark NodeState NodeContext IO where
  check _ c s := s.chain.blocks.any (·.header.number = c.safe)
  apply _ c s := do
    classify "a block is marked safe and finalized" true
    pure { s with chain := { s.chain with safe := some c.safe, finalized := some c.finalized } }
  label c := s!"MARK safe {c.safe}, finalized {c.finalized}"
  build _ := pure ⟨0, 0⟩
  next _ c s := { s with chain := { s.chain with safe := some c.safe
                                                 finalized := some c.finalized } }
  buildIn _ s := do
    let low := (s.chain.blocks.head?.map (·.header.number)).getD 0
    let head := (s.chain.blocks.getLast?.map (·.header.number)).getD 0
    let safe ← Gen.nat (.constant low head)
    let finalized ← Gen.nat (.constant low safe)
    pure ⟨safe, finalized⟩

/-- Ask a method of the node, and require the answer of the model.

It gives how the request ended and the answer of EthLib. -/
def askNode (ctx : NodeContext) (s : NodeState) (method params : String) :
    TestT IO (String × Except RpcError Json) := do
  let built ← s.chain.build ctx.oracle
  let text := resolve built params
  let json ← orFail (Json.parse text)
  let got := built.view.call method (json.getArr?.toOption.getD #[]).toList
  let want ← ctx.oracle.ask (["rpc"] ++ s.chain.words ++ [method, text])
  pure (← sameAnswer got want, got)

/-- Ask for the logs of a filter. -/
structure AskLogs where
  filter : String

instance : Command AskLogs NodeState NodeContext IO where
  check _ _ _ := true
  apply ctx c s := do
    let (ended, got) ← askNode ctx s "eth_getLogs" s!"[{c.filter}]"
    let count := match got with
      | .ok (.arr items) => items.size
      | _ => 0
    cover (if ctx.long then 20 else 0) "a filter is answered" (ended = "ok")
    cover (if ctx.long then 8 else 0) "a filter selects a log" (count > 0)
    classify "a filter selects a log of a block that a command added" (count > 0 ∧ s.sealed > 0)
    pure s
  label c := s!"LOGS {c.filter}"
  build _ := pure ⟨"{}"⟩
  buildIn _ s := AskLogs.mk <$> genFilter s.chain

/-- Ask a getter of a block, a transaction or a receipt. -/
structure AskGetter where
  method : String
  params : String

instance : Command AskGetter NodeState NodeContext IO where
  check _ _ _ := true
  apply ctx c s := do
    let (ended, got) ← askNode ctx s c.method c.params
    let found := ended = "ok" ∧ (got.toOption.map (·.compress)) ≠ some "null"
    cover (if ctx.long then 20 else 0) "a getter finds what it asks for" found
    classify "a getter finds something after a command added a block" (found ∧ s.sealed > 0)
    pure s
  label c := s!"GET {c.method} {c.params}"
  build _ := pure ⟨"eth_blockNumber", "[]"⟩
  buildIn _ s := (fun (method, params) => ⟨method, params⟩) <$> genGetter s.chain

/-- Ask for the fee history of the last blocks. -/
structure AskFees where
  count : Nat
  newest : String
  percentiles : List String

instance : Command AskFees NodeState NodeContext IO where
  check _ _ _ := true
  apply ctx c s := do
    let built ← s.chain.build ctx.oracle
    let text := s!"[{", ".intercalate c.percentiles}]"
    let ps ← orFail (Json.parse text)
    let got := built.view.call "eth_feeHistory"
      [.str ("0x" ++ hexNat c.count), newestJson c.newest, ps]
    let want ← ctx.oracle.ask (["feehistory"] ++ s.chain.fees.words ++
      [toString c.count, c.newest, text])
    annotate s!"the reference: {want}"
    match got with
    | .error e =>
      ensure (want.startsWith "error") s!"EthLib refuses with {e.code} what the model answers"
      ensure (((want.drop 6).toString.splitOn " or ").contains (toString e.code))
        s!"EthLib answers the code {e.code}, the model {want}"
    | .ok json =>
      annotate s!"EthLib: {json.compress}"
      ensure (!want.startsWith "error") "EthLib answers a request that the model refuses"
      let fields := want.splitOn "|"
      if fields.length ≠ 7 then failWith s!"the oracle answered: {want}"
      let field (name : String) : TestT IO Json := orFail (json.getObjVal? name)
      (← orFail (quantities (.arr #[← field "oldestBlock"]))) === fields[0]!
      (← orFail (quantities (← field "baseFeePerGas"))) === fields[1]!
      (← orFail (quantities (← field "baseFeePerBlobGas"))) === fields[2]!
      sameRatios "gasUsedRatio" (← field "gasUsedRatio") fields[3]!
      sameRatios "blobGasUsedRatio" (← field "blobGasUsedRatio") fields[4]!
      if fields[5]! ≠ "none" then
        let rows ← orFail (do (← json.getObjVal? "reward").getArr?)
        joined ";" (← orFail (rows.toList.mapM quantities)) === fields[5]!
      cover (if ctx.long then 10 else 0) "a fee history is answered" true
      classify "a fee history covers a block that a command added" (s.sealed > 0)
    pure s
  label c := s!"FEES {c.count} {c.newest} {c.percentiles}"
  build _ := pure ⟨1, "latest", []⟩
  buildIn _ s := do
    let count ← Gen.nat (.constant 0 8)
    let newest ← genNewest s.chain.fees
    let percentiles ← genPercentiles
    pure ⟨count, newest, percentiles⟩

/-- A node under commands answers as the model, at every point of a growing chain.

The commands add blocks, mark a block safe and finalized, and ask for logs, objects and fees. -/
def nodeScenario (oracle : Oracle) (tests : Nat) : Property IO :=
  let ctx : NodeContext := ⟨oracle, decide (tests ≥ 100)⟩
  (scenarioFrom ((fun chain => (⟨{ chain with side := [], pending := none }, 0⟩ : NodeState))
      <$> genChainSpec) .madhouse ctx
    [Command.gen Seal, Command.gen Seal, Command.gen Mark, Command.gen AskLogs,
      Command.gen AskLogs, Command.gen AskGetter, Command.gen AskGetter, Command.gen AskFees]
    (.linear 1 30) (fun s => do
      annotate s!"the chain at the start: {reprStr s.chain}"
      pure s)).withTests tests

end RpcProperty

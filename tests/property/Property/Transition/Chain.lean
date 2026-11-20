import Property.Transition.Block

/-!
# A chain under commands

A scenario of commands extends one chain on both sides, block after block.

A command sends a transaction of one kind, adds a withdrawal, or seals the block.

The state holds the chain of EthLib and, as plain numbers, the nonce of each sender.

A command is generated for the nonce that the commands before it lead to.

So most transactions enter their block, and a later block starts from what an earlier one left.

The context holds the oracle and the fork, and the chain of the reference lives in the oracle.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Transactions EthLib.Execution.Blocks EthLib.Execution.Evm
open EthLib.Serialization.Rlp
open EvmProperty (PreAccount hexVec preState)

namespace TransitionProperty

/-- What the commands of a scenario at a fork are built from. -/
structure ChainContext (fork : Fork) where
  setup : Setup
  /-- The name of the fork in the reference. -/
  name : String
  /-- Whether the run is long enough to ask for a share of sealed blocks.

  A run of few sequences stays at small sizes, where a sequence is a few commands. -/
  long : Bool

/-- The chain of EthLib and its open block. -/
structure Live (fork : Fork) where
  chain : BlockChain
  env : BlockEnvironment fork
  /-- The body of the open block so far. -/
  body : BodyOutput fork

/-- The state of a scenario: what a generator can tell, and the chain once it has started. -/
structure ChainState (fork : Fork) where
  /-- The nonce of each of the four senders. -/
  nonces : List Nat
  /-- The withdrawals that wait for the block to be sealed. -/
  withdrawals : List (Nat × Nat × Address × Nat)
  /-- The blobs of the transactions of the open block. -/
  blobs : Nat
  /-- The blocks that were sealed. -/
  sealed : Nat
  /-- How far the child of the factory is: 1 once destroyed, 2 once created again. -/
  reborn : Nat
  spec : ChainSpec
  accounts : List PreAccount
  live : Option (Live fork)

/-- A scenario at its start: four senders at their nonces, on a chain from its first block. -/
def genStart {fork : Fork} (ctx : ChainContext fork) : Gen (ChainState fork) := do
  let nonces ← Gen.list (.singleton 4) (Gen.element [0, 1, 7])
  let (_, coinbase, coinbaseAccount) ← genCoinbase (ctx.setup.key 0)
  let recent ← if fork = .daoFork then pure 256 else Gen.nat (.constant 1 8)
  let parentBaseFee ← Gen.element [7, 1000]
  let gasLimit := 30000000
  let spec : ChainSpec := ⟨if fork = .daoFork then daoBlock + 500 else recent, gasLimit,
    parentBaseFee, gasLimit / 2, 0, 0, coinbase, 0x11, recent, .empty, 12⟩
  let program ← genProgramAccounts fork
  let child ← Gen.element [[], [childAccount]]
  pure ⟨nonces, [], 0, 0, 0, spec,
    blockAccounts ctx.setup fork nonces (coinbaseAccount ++ child ++ program), none⟩

/-- The header that some hexadecimal holds at a fork. -/
def headerOf (fork : Fork) (text : String) : Except String (Header fork) := do
  let bytes ← (unhex? text).elim (.error "a header is not hexadecimal") .ok
  (Codec.decode bytes).mapError fun e => s!"a header does not decode: {reprStr e}"

/-- Open the block of a header on a chain: its environment, and its body after the system calls.

It is the start of `applyBody`, so that the transactions can then run one by one. -/
def openBlock {fork : Fork} (chain : BlockChain) (header : Header fork) :
    Except String (Live fork) := do
  let hashes ← (recentHashes chain.recent).mapError reprStr
  let env := blockEnvironment chain.config hashes header
  let body ← (startSystemCalls env header.parentHash (.init ⟨chain.state, ∅, ∅, ∅, ∅⟩)).mapError
    reprStr
  pure ⟨chain, env, ⟨body, .zero, 0, [], [], []⟩⟩

/-- A value, or a failed test with the error. -/
def orFail {α : Type} (result : Except String α) : TestT IO α :=
  match result with
  | .ok value => pure value
  | .error e => failWith e

/-- Start the chain on both sides. -/
def startChain {fork : Fork} (ctx : ChainContext fork) (s : ChainState fork) :
    TestT IO (ChainState fork) := do
  annotate s!"chain={s.spec.show}\n  accounts=\n    \
    {"\n    ".intercalate (s.accounts.map (·.show))}"
  let answer ← ctx.setup.oracle.ask ["open", ctx.name, s.spec.show, showAccounts s.accounts]
  let words := answer.splitOn "\t"
  if words.length ≠ 2 then failWith s!"the oracle answered: {answer}"
  let recent ← orFail (recentOf fork words[0]!)
  let header ← orFail (headerOf fork words[1]!)
  let live ← orFail (openBlock ⟨configOf fork, preState s.accounts, recent⟩ header)
  pure { s with live := some live }

/-- The chain of a state, which the setup started. -/
def liveOf {fork : Fork} (s : ChainState fork) : TestT IO (Live fork) :=
  match s.live with
  | some live => pure live
  | none => failWith "the chain did not start"

/-- Send a transaction to both sides and compare what it left.

It gives the verdict of EthLib and the state with the body after the transaction. -/
def sendBoth {fork : Fork} (ctx : ChainContext fork) (tx : TxSpec) (s : ChainState fork) :
    TestT IO (TxResult × ChainState fork) := do
  let live ← liveOf s
  let answer ← ctx.setup.oracle.ask ["add", tx.show]
  let words := answer.splitOn "\t"
  if words.length ≠ 7 then failWith s!"the oracle answered: {answer}"
  let raw := (unhex? words[0]!).getD .empty
  let (got, body) := runTransaction live.env live.body.receipts.length live.body raw
  annotate s!"the reference: {words[1]!}, {words[2]!}; EthLib: {got.verdict}, {got.detail}"
  sameResult got (words.drop 1)
  -- The nonce of the sender as the state has it now, for the commands that follow.
  let sender := ctx.setup.key tx.key
  let nonce := ((body.block.applyChanges.accounts[sender]?).map (·.nonce)).getD 0
  pure (got, { s with nonces := s.nonces.set tx.key nonce, live := some { live with body } })

/-! ## The commands -/

/-- A transaction of one kind that should enter the open block. -/
structure Send (fork : Fork) (kind : String) where
  tx : TxSpec
  name : String
  /-- How far the transaction moves the nonce of its sender. -/
  moved : Nat

/-- The kind of action and the type of transaction of a kind of command. -/
def kindOfSend (kind : String) : Option String × Option Nat :=
  match kind with
  | "blob" => (some "call", some 3)
  | "set code" => (some "call", some 4)
  | "any" => (none, none)
  | kind => (some kind, none)

instance {fork : Fork} {kind : String} :
    Command (Send fork kind) (ChainState fork) (ChainContext fork) IO where
  -- A command made for a nonce that a refused or removed command did not reach is left out.
  check _ c s := c.tx.nonce = s.nonces.getD c.tx.key 0 &&
    (c.tx.type ≠ 3 || s.blobs + c.tx.blobs.length ≤ maxBlobs fork)
  apply ctx c s := do
    let (got, after) ← sendBoth ctx c.tx s
    let valid := got.verdict = "valid"
    cover (if ctx.long then 30 else 0) "a generated transaction entered its block" valid
    if valid then
      classify s!"entered: {kind}" true
      classify s!"ended in {got.detail}" true
    else classify s!"expected to enter, refused: {got.detail}" true
    -- The model said how far the nonce moves, with the authorizations of the sender itself.
    if valid then after.nonces.getD c.tx.key 0 === c.tx.nonce + c.moved
    -- The child of the factory: destroyed, then created again, then called.
    let ok := valid ∧ got.detail = "ok"
    let reborn := if ok ∧ c.name = "destroy the child" then 1
      else if ok ∧ c.name = "create the child" ∧ s.reborn = 1 then 2
      else s.reborn
    classify "the child was destroyed, created again and called"
      (ok ∧ c.name = "call the child" ∧ s.reborn = 2)
    pure (if valid then { after with
      reborn
      blobs := after.blobs + (if c.tx.type = 3 then c.tx.blobs.length else 0) } else after)
  label c := s!"SEND {kind} ({c.name}) {c.tx.show}"
  build _ := pure ⟨⟨0, 0, 0, 0, 0, 0, 0, 21000, none, 0, .empty, [], 0, [], [], 0⟩, "none", 1⟩
  next _ c s := { s with
    nonces := s.nonces.set c.tx.key (c.tx.nonce + c.moved)
    blobs := s.blobs + (if c.tx.type = 3 then c.tx.blobs.length else 0) }
  buildIn ctx s := do
    let key ← Gen.nat (.constant 0 3)
    let (action, type) := kindOfSend kind
    let (tx, name, moved) ← genIncluded fork (s.spec.prices fork) key (s.nonces.getD key 0)
      (ctx.setup.key key) s.spec.coinbase blockAuthorities action type
    pure ⟨tx, name, moved⟩

/-- A transaction that no block may hold: it must be refused, and leave the state as it was. -/
structure Refuse (fork : Fork) where
  tx : TxSpec
  why : String
  /-- The nonce of the sender that the fault was made for. -/
  nonce : Nat

instance {fork : Fork} : Command (Refuse fork) (ChainState fork) (ChainContext fork) IO where
  -- A nonce is too low or too high only against the nonce that the command was made for.
  check _ c s := c.nonce = s.nonces.getD c.tx.key 0
  apply ctx c s := do
    let live ← liveOf s
    let before := showState live.body.block.applyChanges
    let (got, after) ← sendBoth ctx c.tx s
    got.verdict === "invalid"
    showState (← liveOf after).body.block.applyChanges === before
    classify "a transaction was refused" true
    pure after
  label c := s!"REFUSE ({c.why}) {c.tx.show}"
  build _ := pure ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, none, 0, .empty, [], 0, [], [], 0⟩, "no gas", 0⟩
  buildIn ctx s := do
    let key ← Gen.nat (.constant 0 3)
    let (tx, _, _) ← genIncluded fork (s.spec.prices fork) key (s.nonces.getD key 0)
      (ctx.setup.key key) s.spec.coinbase blockAuthorities (some "transfer")
    let later := (typesAt fork).length % 5
    let faults : List (TxSpec × String) := [
      ({ tx with nonce := tx.nonce + 1 }, "nonce too high"),
      ({ tx with gas := tx.minimumGas fork - 1 }, "gas below the least"),
      ({ tx with fault := 2 }, "signature"),
      ({ tx with gas := 30000001 }, "gas above the block"),
      ({ tx with value := 10 ^ 30 }, "value above the balance")] ++
      (if later > 0 then [({ tx with type := later, chain := 1, gas := tx.gas + 100000 },
        "type of a later fork")] else []) ++
      (if tx.nonce > 0 then [({ tx with nonce := tx.nonce - 1 }, "nonce too low")] else [])
    (fun (broken, why) => ⟨broken, why, tx.nonce⟩) <$> Gen.element faults

/-- A withdrawal, which the next sealed block holds. -/
structure Withdraw (fork : Fork) where
  address : Address
  amount : Nat

instance {fork : Fork} : Command (Withdraw fork) (ChainState fork) (ChainContext fork) IO where
  check _ _ _ := fork ≥ .shapella
  apply _ c s :=
    pure { s with withdrawals := s.withdrawals ++ [(s.withdrawals.length, 7, c.address, c.amount)] }
  label c := s!"WITHDRAW {c.amount} gwei to {hexVec c.address}"
  build ctx := Gen.zipWith Withdraw.mk
    (Gen.element [richAddress, absentAddress, storeAddress, ctx.setup.key 0, emptyAddress])
    (Gen.element [0, 1, 7, 10 ^ 9])

/-- Seal the open block: both sides run it whole from the state before it, and open the next. -/
structure Seal (fork : Fork) where

instance {fork : Fork} : Command (Seal fork) (ChainState fork) (ChainContext fork) IO where
  apply ctx _ s := do
    let live ← liveOf s
    let answer ← ctx.setup.oracle.ask ["seal", showWithdrawals s.withdrawals]
    let words := answer.splitOn "\t"
    if words.length ≠ 4 then failWith s!"the oracle answered: {answer}"
    let (verdict, after) ← compareBlock (fork := fork) live.chain (words.take 3)
    let chain := match after with
      | some (block, post) => live.chain.addBlock block post
      | none => live.chain
    let count := live.body.receipts.length
    cover (if ctx.long then 20 else 0) "a block was sealed" after.isSome
    classify "a block with three transactions or more was sealed" (after.isSome ∧ count ≥ 3)
    classify "a second block was sealed" (after.isSome ∧ s.sealed ≥ 1)
    if after.isNone then classify s!"a block was refused: {verdict}" true
    let next ← orFail (do openBlock chain (← headerOf fork words[3]!))
    -- A refused block gives back the nonces of the state before it.
    let nonces := (List.range 4).map fun key =>
      ((chain.state.accounts[ctx.setup.key key]?).map (·.nonce)).getD 0
    pure { s with
      nonces, withdrawals := [], blobs := 0, live := some next
      sealed := s.sealed + (if after.isSome then 1 else 0) }
  label _ := "SEAL"
  build _ := pure {}
  next _ _ s := { s with withdrawals := [], blobs := 0 }

/-- The kinds of transaction that a fork has a command for. -/
def sendKinds (fork : Fork) : List String :=
  ["transfer", "call", "create", "self-destruct", "any"] ++
    -- The factory creates its child with CREATE2, which Constantinople adds.
    --
    -- The kind is listed three times, since only three of its commands in order tell much.
    (if fork ≥ .constantinople then ["reborn", "reborn", "reborn"] else []) ++
    (if fork ≥ .dencun then ["blob"] else []) ++ (if fork ≥ .pectra then ["set code"] else [])

/-- A chain under commands is the chain of the reference, at one fork.

Each transaction leaves the same gas used, receipt and state on both sides, in its turn.

Each sealed block is then run whole on both sides, from the state before it.

A transaction that no block may hold is refused and leaves the state as it was. -/
def chainScenario (setup : Setup) (fork : Fork × String) (tests : Nat)
    (mode : Mode := .madhouse) : Property IO :=
  let ctx : ChainContext fork.1 := ⟨setup, fork.2, decide (tests ≥ 30)⟩
  let sends : List (ChainContext fork.1 → ChainState fork.1 →
      Gen (CommandWrapper (ChainState fork.1) IO)) :=
    match sendKinds fork.1 with
    | kinds => kinds.map fun kind => Command.gen (Send fork.1 kind)
  (scenarioFrom (genStart ctx) mode ctx
    (sends ++ [Command.gen (Refuse fork.1), Command.gen (Withdraw fork.1),
      Command.gen (Seal fork.1), Command.gen (Seal fork.1)])
    (.linear 1 50) (startChain ctx)).withTests tests

/-- The forks of the scenarios: one of each family, and the forks at the edges of a family.

The last three have no module in the reference, and run beside the fork whose rules they keep. -/
def scenarioForks : List (Fork × String) := familyForks ++ [
  (.frontier, "frontier"), (.daoFork, "dao_fork"), (.tangerineWhistle, "tangerine_whistle"),
  (.spuriousDragon, "spurious_dragon"), (.istanbul, "istanbul"), (.grayGlacier, "gray_glacier"),
  (.bpo2, "bpo2"), (.petersburg, "constantinople"), (.bellatrix, "gray_glacier"),
  (.bpo5, "bpo2")]

end TransitionProperty

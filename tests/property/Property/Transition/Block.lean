import Property.Transition.Tx

/-!
# A whole block on a world

The oracle builds a block from its parts: a chain, transactions, withdrawals and ommers.

Its header holds what the reference computed, so the reference accepts the block.

EthLib must then accept the same bytes and reach the same state.

A block with one field of its header changed, or with a part that breaks a rule, must be refused.

Both sides must then refuse it at the same place.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Transactions EthLib.Execution.Blocks EthLib.Execution.Evm
open EthLib.Serialization.Rlp
open EvmProperty (PreAccount addressOf hexVec word32 preState)

namespace TransitionProperty

/-! ## A chain as its fields -/

/-- The chain before a block and the fields of the block that its producer chooses. -/
structure ChainSpec where
  number : Nat
  gasLimit : Nat
  parentBaseFee : Nat
  parentGasUsed : Nat
  parentExcessBlobGas : Nat
  parentBlobGasUsed : Nat
  coinbase : Address
  randao : UInt8
  /-- The number of recent blocks, at least one. -/
  recent : Nat
  extraData : ByteArray
  /-- The seconds from the parent to the block. -/
  seconds : Nat

/-- A chain in the text form of the oracle. -/
def ChainSpec.show (c : ChainSpec) : String :=
  let word (b : UInt8) : String := hexVec (Vector.replicate 32 b)
  ",".intercalate [toString c.number, toString c.gasLimit, toString c.parentBaseFee,
    toString c.parentGasUsed, toString c.parentExcessBlobGas, toString c.parentBlobGasUsed,
    hexVec c.coinbase, word c.randao, word 0x22, toString c.recent, hex c.extraData,
    toString c.seconds]

/-- The base fee and the base fee per blob gas of the block after a parent, as EthLib counts them.

Earlier properties compared both rules with the reference. -/
def ChainSpec.prices (c : ChainSpec) (fork : Fork) (schedule : Option Schedule := none) :
    Prices :=
  let baseFee := if fork ≥ .london then
      Fees.BaseFee.calculateBaseFeePerGas c.gasLimit c.parentGasUsed c.parentBaseFee
    else 0
  let excess := if h : .dencun ≤ fork then
      Fees.BlobBaseFee.calcExcessBlobGas fork (scheduleAt fork h schedule)
        c.parentExcessBlobGas c.parentBlobGasUsed c.parentBaseFee
    else 0
  ⟨baseFee, blobPrice fork excess schedule⟩

/-- The first block of the DAO Fork on mainnet, which the reference fixes. -/
def daoBlock : Nat := 1920000

/-- The configuration of a chain that is at one fork from its first block.

The chain of the DAO Fork is at Homestead before the block of the fork.

The chain sets the blob schedule that is given, from its first block. -/
def configOf (fork : Fork) (schedule : Option Schedule := none) : ChainConfig where
  chainId := 1
  depositContractAddress := depositAddress
  activations := if fork = .daoFork then [(.homestead, .block 0), (.daoFork, .block daoBlock)]
    else [(fork, .block 0)]
  blobSchedules := if h : .dencun ≤ fork then
      (if schedule.isSome then [(.time 0, scheduleAt fork h schedule)] else [])
    else []

/-- The fork of a block number on the chain of a fork. -/
def forkAt (fork : Fork) (number : Nat) : Fork :=
  if fork = .daoFork ∧ number < daoBlock then .homestead else fork

/-! ## Reading what the oracle built -/

/-- The recent blocks that the oracle built, from their headers joined with `.`. -/
def recentOf (fork : Fork) (word : String) : Except String (List RecentBlock) :=
  (word.splitOn ".").mapM fun text => do
    let bytes ← (unhex? text).elim (.error "a header is not hexadecimal") .ok
    let item ← (decode bytes).mapError fun e => s!"a header is not RLP: {reprStr e}"
    let ⟨f, header⟩ ← (Header.ofItemAtNumber (forkAt fork) item).mapError
      fun e => s!"a header does not decode: {reprStr e}"
    pure ⟨f, header, []⟩

/-- The block that some bytes hold at a fork, or why they hold none. -/
def blockOf (fork : Fork) (bytes : ByteArray) : Except String (Block fork Transaction) := do
  let raw : Block fork Item ← (Block.decode (forkAt fork) bytes).mapError
    fun e => s!"block: {reprStr e}"
  let transactions ← raw.transactions.mapM fun item =>
    (decodeBodyTransaction fork item).mapError fun e => s!"transaction: {reprStr e}"
  pure { raw with transactions }

/-- Where EthLib refuses a block, in the words of the oracle. -/
def kindOf : BlockError → String
  | .invalidTransaction index _ => s!"tx:{index}"
  | .deposit _ => "deposit"
  | .systemContractEmpty _ | .systemCallFailed .. => "system"
  | .ommers _ | .ommersAfterParis _ => "ommers"
  | .wrongGasUsed .. | .gasUsedAboveLimit .. => "output gas"
  | .wrongStateRoot .. => "output state"
  | .wrongTransactionsRoot .. => "output transactions"
  | .wrongReceiptRoot .. => "output receipts"
  | .wrongBloom .. => "output bloom"
  | .wrongWithdrawalsRoot .. => "output withdrawals"
  | .wrongBlobGasUsed .. => "output blobgas"
  | .wrongRequestsHash .. => "output requests"
  | .wrongBlockAccessListHash .. => "output accesslist"
  | .blockAccessList _ => "accesslist"
  | .wrongDaoExtraData _ => "header"
  | e => s!"other {reprStr e}"

/-- Where the reference refuses a block, from the words of the oracle after `invalid`. -/
def kindOfReference (words : List String) : String :=
  match words with
  | "output" :: field :: _ => s!"output {field}"
  | "header" :: "gas" :: _ => "output gas"
  | kind :: _ => kind
  | [] => "none"

/-- The two states, account by account, where they differ. -/
def stateDifference (mine theirs : String) : String :=
  let (a, b) := (mine.splitOn ";", theirs.splitOn ";")
  s!"EthLib only:    {a.filter (!b.contains ·)}\n  reference only: {b.filter (!a.contains ·)}"

/-- Run a block of the oracle in EthLib and compare the verdict and the state after it.

`answer` holds the verdict of the reference, the bytes of the block and the state after it.

It gives the verdict, and the state of EthLib after a valid block. -/
def compareBlock {fork : Fork} (chain : BlockChain) (answer : List String) :
    TestT IO (String × Option (Block fork Transaction × State.State)) := do
  let verdict := (answer.getD 0 "").splitOn " "
  let bytes := (unhex? (answer.getD 1 "")).getD .empty
  let theirs := answer.getD 2 ""
  annotate s!"the reference: {answer.getD 0 ""}"
  annotate s!"the block: {answer.getD 1 ""}"
  let valid := verdict.head! = "valid"
  match blockOf fork bytes with
  | .error e =>
    annotate s!"EthLib does not read the block: {e}"
    ensure (!valid) "the reference accepts a block that EthLib does not read"
    "decode" === kindOfReference (verdict.drop 1)
    pure ("invalid decode", none)
  | .ok block =>
    match stateTransition chain block (checkSeal := false) with
    | .ok post =>
      ensure valid "EthLib accepts a block that the reference refuses"
      let mine := showState post
      if mine ≠ theirs then failWith s!"the state differs.\n  {stateDifference mine theirs}"
      pure ("valid", some (block, post))
    | .error e =>
      annotate s!"EthLib refuses the block: {reprStr e}"
      if valid then
        -- The body alone says which account differs.
        match runBody chain block with
        | .ok result =>
          failWith s!"EthLib refuses a block that the reference accepts.\n  \
            {stateDifference (showState result.post) theirs}"
        | .error _ => failWith "EthLib refuses a block that the reference accepts"
      kindOf e === kindOfReference (verdict.drop 1)
      let kind := kindOf e
      pure (s!"invalid {if kind.startsWith "tx:" then "transaction" else kind}", none)

/-! ## A case -/

/-- A block on a world: a chain, accounts, and the parts of the block. -/
structure BlockCase where
  fork : Fork × String
  chain : ChainSpec
  accounts : List PreAccount
  /-- Each transaction, with what it does. -/
  txs : List (TxSpec × String)
  /-- Each withdrawal: its index, its validator, its address and its amount in gwei. -/
  withdrawals : List (Nat × Nat × Address × Nat)
  /-- Each ommer: its age, its beneficiary and its fault. -/
  ommers : List (Nat × Address × Nat)
  /-- The field of the header to change, or `-`. -/
  mutation : String
  coinbase : String
  /-- The blob schedule that the chain sets itself, if it does. -/
  schedule : Option Schedule
  /-- Whether the block starts by destroying the child of the factory and creating it again. -/
  reborn : Bool

/-- The withdrawals in the text form of the oracle. -/
def showWithdrawals (withdrawals : List (Nat × Nat × Address × Nat)) : String :=
  joined "/" (withdrawals.map fun (index, validator, address, amount) =>
    s!"{index}:{validator}:{hexVec address}:{amount}")

/-- The ommers in the text form of the oracle. -/
def showOmmers (ommers : List (Nat × Address × Nat)) : String :=
  joined "/" (ommers.map fun (age, coinbase, fault) => s!"{age}:{hexVec coinbase}:{fault}")

/-- A case as a report shows it. -/
def BlockCase.show (c : BlockCase) : String :=
  s!"fork={c.fork.2} ({c.fork.1.name}) mutation={c.mutation} coinbase={c.coinbase} \
    schedule={c.schedule}\n  \
    chain={c.chain.show}\n  withdrawals={showWithdrawals c.withdrawals} \
    ommers={showOmmers c.ommers}\n  txs=\n    \
    {"\n    ".intercalate (c.txs.map fun (tx, name) => s!"{name}: {tx.show}")}\n  accounts=\n    \
    {"\n    ".intercalate (c.accounts.map (·.show))}"

/-- The authorities of a world of several transactions: none, plain, delegated and a contract. -/
def blockAuthorities : List Authority := [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 5⟩, ⟨3, 0⟩]

/-- Transactions of four senders, each at the nonce that the ones before it leave. -/
def genTxs (setup : Setup) (fork : Fork) (prices : Prices) (coinbase : Address) :
    Nat → List Nat → Gen (List (TxSpec × String))
  | 0, _ => pure []
  | n + 1, nonces => do
    let key ← Gen.nat (.constant 0 3)
    let nonce := nonces.getD key 0
    let (tx, name, moved) ← genIncluded fork prices key nonce (setup.key key) coinbase
      blockAuthorities
    let rest ← genTxs setup fork prices coinbase n (nonces.set key (nonce + moved))
    pure ((tx, name) :: rest)

/-- Three transactions of the last sender: destroy the child, create it again, and call it.

Before Dencun the child is deleted between the first two, so the third counts from nothing.

The storage of the child must then be the storage that its new init code wrote. -/
def genReborn (setup : Setup) (fork : Fork) (prices : Prices) (coinbase : Address)
    (nonces : List Nat) : Gen (List (TxSpec × String) × List Nat) := do
  let step (kind : String) (nonces : List Nat) : Gen ((TxSpec × String) × List Nat) := do
    let nonce := nonces.getD 3 0
    let (tx, name, moved) ← genIncluded fork prices 3 nonce (setup.key 3) coinbase
      blockAuthorities (some kind)
    pure ((tx, name), nonces.set 3 (nonce + moved))
  let (first, nonces) ← step "reborn: destroy" nonces
  let (second, nonces) ← step "reborn: create" nonces
  let (third, nonces) ← step "reborn: count" nonces
  pure ([first, second, third], nonces)

/-- A transaction with one fault that keeps it out of a block. -/
def breakTx (kind : Nat) (tx : TxSpec) : TxSpec :=
  match kind with
  | 0 => { tx with nonce := tx.nonce + 1 }
  | 1 => { tx with gas := 1000 }
  | _ => { tx with fault := 2 }

/-- The accounts of a world of several transactions, with the senders at their nonces. -/
def blockAccounts (setup : Setup) (fork : Fork) (nonces : List Nat)
    (extra : List PreAccount) (broken : Bool := false) : List PreAccount :=
  distinctAccounts (nonces.zipIdx.map (fun (nonce, key) =>
      (⟨setup.key key, nonce, 10 ^ 24, .empty, []⟩ : PreAccount)) ++
    authorityAccounts setup blockAuthorities ++ extra ++ fixedAccounts fork broken)

/-- The beneficiary of a block, with its account if it has one. -/
def genCoinbase (sender : Address) : Gen (String × Address × List PreAccount) :=
  Gen.element [
    ("absent", addressOf 0xba 0x5e, []), ("absent", addressOf 0xba 0x5e, []),
    ("empty", addressOf 0xba 0x5e, [(⟨addressOf 0xba 0x5e, 0, 0, .empty, []⟩ : PreAccount)]),
    ("funded", addressOf 0xba 0x5e, [⟨addressOf 0xba 0x5e, 0, 5, .empty, []⟩]),
    ("a sender", sender, []), ("a contract", storeAddress, []),
    ("a precompile", numberAddress 3, [])]

/-- A block on a world: mostly valid, with every part that its fork has. -/
def genBlockCase (setup : Setup) (only : Option (Fork × String) := none) : Gen BlockCase := do
  let fork ← match only with
    | some fork => pure fork
    | none => Gen.frequency [(12, genFork), (1, pure (.daoFork, "dao_fork"))]
  let (fork, schedule) ← if only.isSome then pure (fork, none) else genCrossed fork
  let f := fork.1
  -- A chain holds every block from its first one, or 255 blocks and more.
  --
  -- BLOCKHASH reads the last 256, and the reference fails on a chain that is cut short.
  let recent ← if f = .daoFork then pure 256 else
    Gen.frequency [(12, Gen.nat (.constant 1 8)), (1, Gen.element [254, 255, 256, 257, 300])]
  let later ← Gen.nat (.constant 0 50)
  let number ← if f = .daoFork then
      Gen.element [daoBlock, daoBlock, daoBlock + 1, daoBlock + 9, daoBlock + 10, daoBlock + 500]
    else pure (if recent < 255 then recent else recent + later)
  let gasLimit ← Gen.frequency [(5, pure 30000000), (1, Gen.nat (.linear 100000 3000000))]
  let parentBaseFee ← Gen.element [7, 1000, 10 ^ 9]
  let parentGasUsed ← Gen.element [0, gasLimit / 2, gasLimit]
  let parentExcess ← Gen.element [0, 3000000, 10000000]
  let parentBlob ← Gen.element [0, 393216, 786432]
  let (coinbaseName, coinbase, coinbaseAccount) ← genCoinbase (setup.key 0)
  let extraData ← if f = .daoFork then
      Gen.element ["dao-hard-fork", "dao-hard-fork", "dao-hard-fork", "", "dao-hard-forl"]
    else Gen.element ["", "x"]
  let seconds ← Gen.element [1, 12, 13, 1000]
  let chain : ChainSpec := ⟨number, gasLimit, parentBaseFee, parentGasUsed, parentExcess,
    parentBlob, coinbase, 0x11, recent, extraData.toUTF8, seconds⟩
  -- The transactions, one of them broken now and then.
  let nonces ← Gen.list (.singleton 4) (Gen.element [0, 1, 7])
  let count ← Gen.nat (.linear 0 6)
  let reborn ← Gen.frequency [(4, pure false), (1, pure true)]
  let (first, later) ← if reborn then genReborn setup f (chain.prices f schedule) coinbase nonces
    else pure ([], nonces)
  let rest ← genTxs setup f (chain.prices f schedule) coinbase (count - first.length) later
  let txs := first ++ rest
  let broken ← Gen.frequency [(9, pure none),
    (1, some <$> Gen.zip (Gen.nat (.constant 0 5)) (Gen.nat (.constant 0 2)))]
  let txs := match broken with
    | some (index, kind) => txs.zipIdx.map fun ((tx, name), i) =>
        if i = index % (max 1 txs.length) then (breakTx kind tx, name) else (tx, name)
    | none => txs
  -- The withdrawals and the ommers.
  let withdrawals ← if f ≥ .shapella then
      Gen.list (.linear 0 3) (Gen.zip (Gen.nat (.constant 0 9)) (Gen.zip (Gen.nat (.constant 0 9))
        (Gen.zip (Gen.element [richAddress, absentAddress, storeAddress, setup.key 0, coinbase,
            emptyAddress, numberAddress 1])
          (Gen.element [0, 1, 7, 10 ^ 9, 2 ^ 64 - 1]))))
    else pure []
  -- An ommer is at most six blocks older than its block, so an age of seven is refused.
  let oldest := min 7 (max 1 (recent - 1))
  let ommer : Gen (Nat × Address × Nat) := Gen.zip (Gen.nat (.constant 1 oldest))
    (Gen.zip (Gen.element [richAddress, absentAddress, coinbase, setup.key 1])
      (Gen.frequency [(18, pure 0), (1, pure 1), (1, pure 2)]))
  let ommers ← if recent < 2 ∨ only.isSome then pure []
    else if f < .paris then
      Gen.frequency [(8, pure []), (10, Gen.list (.constant 1 2) ommer),
        (1, Gen.list (.singleton 3) ommer)]
    else Gen.frequency [(15, pure []), (1, Gen.list (.singleton 1) ommer)]
  let mutation ← Gen.frequency [(7, pure "-"), (3, Gen.element (["gas", "state", "transactions",
    "receipts", "bloom", "withdrawals", "blobgas", "requests"] ++
    (if f ≥ .glamsterdam then ["accesslist", "accesslist"] else [])))]
  let withoutContract ← Gen.frequency [(14, pure false), (1, pure (decide (f ≥ .pectra)))]
  -- The world.
  let empty ← Gen.frequency [(2, pure []),
    (1, pure [(⟨emptyAddress, 0, 0, .empty, []⟩ : PreAccount)])]
  let program ← genProgramAccounts f
  let dao : List PreAccount := if f = .daoFork then
      [⟨DAO_ACCOUNTS.getD 0 absentAddress, 1, 1000, .empty, []⟩,
       ⟨DAO_ACCOUNTS.getD 115 absentAddress, 0, 7, bytesOf [0x00], []⟩]
    else []
  let child ← Gen.element [[], [childAccount]]
  let accounts := blockAccounts setup f nonces
    (coinbaseAccount ++ empty ++ (if reborn then [childAccount] else child) ++ program ++ dao)
    withoutContract
  pure ⟨fork, chain, accounts, txs, withdrawals, ommers, mutation, coinbaseName, schedule,
    reborn⟩

/-! ## The property -/

/-- A block is valid in EthLib exactly when it is in the reference, and leaves the same state.

The reference builds the header from its own run of the body.

So EthLib must compute the same gas used, roots, logs Bloom, blob gas and requests hash.

The body holds the system calls, the transactions, the withdrawals, the requests and the rewards.

A block that the reference refuses must be refused at the same place. -/
def wholeBlock (setup : Setup) (only : Option (Fork × String) := none) : Property IO :=
  propertyM do
  let c ← forAllWith BlockCase.show (genBlockCase setup only)
  let oracle := if only.isSome then setup.glamsterdam.getD setup.oracle else setup.oracle
  pure do
    let fork := c.fork.1
    let answer ← oracle.ask ["block", c.fork.2, c.chain.show, showAccounts c.accounts,
      joined ";" (c.txs.map (·.1.show)), showWithdrawals c.withdrawals, showOmmers c.ommers,
      c.mutation]
    let words := answer.splitOn "\t"
    if words.length ≠ 4 then failWith s!"the oracle answered: {answer}"
    let recent ← match recentOf fork words[0]! with
      | .ok recent => pure recent
      | .error e => failWith e
    let chain : BlockChain := ⟨configOf fork c.schedule, preState c.accounts, recent⟩
    let (verdict, after) ← compareBlock (fork := fork) chain (words.drop 1)
    label s!"{family fork}: {verdict}"
    classify s!"verdict: {verdict}" true
    cover 20 "valid" after.isSome
    cover 10 "invalid" after.isNone
    classify "valid on a chain that sets its blob schedule" (after.isSome ∧ c.schedule.isSome)
    classify "valid with the child destroyed and created again" (after.isSome ∧ c.reborn)
    classify "valid with three transactions or more" (after.isSome ∧ c.txs.length ≥ 3)
    classify "valid with withdrawals" (after.isSome ∧ !c.withdrawals.isEmpty)
    classify "valid with ommers" (after.isSome ∧ !c.ommers.isEmpty)
    classify "valid at the first block of the DAO Fork"
      (after.isSome ∧ fork = .daoFork ∧ c.chain.number = daoBlock)
    -- How the transactions of a valid block ended, as EthLib ran them.
    match after with
    | some (block, _) =>
      match runBody chain block with
      | .ok result =>
        for outcome in ["ok", "revert", "oog", "halt"] do
          classify s!"valid with a transaction that ends in {outcome}"
            (result.output.results.any fun r => outcomeOf r.error = outcome)
        classify "valid with requests" (!result.output.requests.isEmpty)
        classify "valid with logs" (!result.output.logs.isEmpty)
      | .error _ => pure ()
    | none => pure ()

end TransitionProperty

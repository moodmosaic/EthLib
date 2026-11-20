import Property.Rpc.Fees

/-!
# A chain of blocks with transactions, receipts and logs

The getters of a node read blocks, signed transactions, receipts and logs, and run nothing.

So a chain here is plain fields, and the oracle signs its transactions.

Both sides then build the same blocks: EthLib from the signed bytes, the oracle from the fields.

A receipt is what the generator says, not what the transaction would leave.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Blocks EthLib.Execution.Transactions EthLib.Execution.Rpc
open Lean (Json)
open EthLib.Serialization.JsonRpc (RpcError)

namespace RpcProperty

/-! ## A transaction as its fields -/

/-- An authorization of EIP-7702 as its fields, which the oracle signs with a key. -/
structure AuthSpec where
  chain : Nat
  address : Address
  nonce : Nat
  key : Nat
  deriving Repr

/-- A transaction as its fields, which the oracle signs with a key. -/
structure TxSpec where
  type : Nat
  key : Nat
  /-- The chain that the transaction names, or 0 for a legacy transaction that names none. -/
  chain : Nat
  nonce : Nat
  gasPrice : Nat
  priorityFee : Nat
  maxFee : Nat
  gas : Nat
  to : Option Address
  value : Nat
  data : ByteArray
  access : List (Address × List Nat)
  blobFee : Nat
  blobs : List Nat
  auths : List AuthSpec

/-- A transaction in the text form of the oracle. -/
def TxSpec.show (t : TxSpec) : String :=
  let access := t.access.map fun (address, keys) =>
    s!"{hexVec address}:{".".intercalate (keys.map fun k => hexVec (word32 k))}"
  let auths := t.auths.map fun a => s!"{a.chain}:{hexVec a.address}:{a.nonce}:{a.key}:0"
  ",".intercalate [toString t.type, toString t.key, toString t.chain, toString t.nonce,
    toString t.gasPrice, toString t.priorityFee, toString t.maxFee, toString t.gas,
    (t.to.map hexVec).getD "-", toString t.value, hex t.data, joined "/" access,
    toString t.blobFee, joined "." (t.blobs.map fun b => hexVec (word32 b)), joined "/" auths,
    "0"]

instance : Repr TxSpec where
  reprPrec t _ := t.show

/-- A log as its fields. -/
structure LogSpec where
  address : Address
  topics : List Nat
  data : ByteArray

/-- A log in the text form of the oracle. -/
def LogSpec.show (l : LogSpec) : String :=
  s!"{hexVec l.address}!{joined "." (l.topics.map fun t => hexVec (word32 t))}!{hex l.data}"

/-- The log of EthLib with the fields. -/
def LogSpec.toLog (l : LogSpec) : Log := ⟨l.address, l.topics.map word32, l.data⟩

/-- A transaction of a block, with the receipt that the chain gives it. -/
structure TxEntry where
  spec : TxSpec
  gasUsed : Nat
  succeeded : Bool
  logs : List LogSpec

/-- The entry in the text form of the oracle. -/
def TxEntry.show (t : TxEntry) : String :=
  s!"{t.spec.show}~{t.gasUsed}~{if t.succeeded then 1 else 0}~{joined "^" (t.logs.map (·.show))}"

instance : Repr TxEntry where
  reprPrec t _ := t.show

/-- A block as its fields. -/
structure BlockSpec where
  fork : Fork
  header : HeaderSpec
  txs : List TxEntry
  deriving Repr

/-- The block in the text form of the oracle. -/
def BlockSpec.show (b : BlockSpec) : String :=
  s!"{b.fork.name}|{b.header.show}|{joined "+" (b.txs.map (·.show))}"

/-- A chain as its fields: the canonical blocks, blocks off the chain, and the marks of a node. -/
structure ChainSpec where
  activations : List (Fork × Activation)
  blocks : List BlockSpec
  side : List BlockSpec
  pending : Option BlockSpec
  safe : Option Nat
  finalized : Option Nat
  deriving Repr

/-- The words of the chain in a command of the oracle. -/
def ChainSpec.words (c : ChainSpec) : List String :=
  let mark (n : Option Nat) : String := (n.map toString).getD "-"
  [joined "," (c.activations.map fun (f, a) => s!"{f.name}:{showActivation a}"),
   joined ";" (c.blocks.map (·.show)), joined ";" (c.side.map (·.show)),
   s!"{mark c.safe}&{mark c.finalized}&{(c.pending.map (·.show)).getD "-"}"]

/-- The configuration of the chain. -/
def ChainSpec.config (c : ChainSpec) : ChainConfig :=
  ⟨1, addressOf 0xde 0x90, c.activations, []⟩

/-! ## Building the view -/

/-- The record of a block whose transactions the oracle signed. -/
def BlockSpec.record (b : BlockSpec) (raws : String) : Except String BlockRecord := do
  let texts := if raws = "-" then [] else raws.splitOn "."
  if texts.length ≠ b.txs.length then throw s!"the oracle signed {texts.length} transactions"
  let transactions ← texts.mapM fun text => do
    let bytes ← (unhex? text).elim (.error "a transaction is not hexadecimal") .ok
    (decodeTransaction b.fork bytes).mapError fun e => s!"a transaction: {reprStr e}"
  let outcome (succeeded : Bool) : Outcome b.fork :=
    if h : Fork.byzantium ≤ b.fork then .status h succeeded
    else .postState (Nat.lt_of_not_le h) (Vector.replicate 32 0)
  let receipts := makeReceipts (b.txs.map fun t =>
    (outcome t.succeeded, t.gasUsed, t.logs.map (·.toLog)))
  recordOf b.fork (b.header.toHeader b.fork) ⟨∅, ∅, ∅⟩ transactions
    ((b.txs.map fun t => t.spec.type.toUInt8).zip receipts)

/-- A chain on both sides: the view of EthLib, and the hashes that the oracle computed. -/
structure Built where
  view : ChainView
  /-- The records of the canonical blocks, then of the blocks off the chain, then the pending. -/
  records : List BlockRecord
  /-- The hash of each of those blocks, as the oracle computed it. -/
  hashes : List String

/-- Build the chain on both sides.

The hash of each header must be the one that the oracle computes from the fields. -/
def ChainSpec.build (oracle : Oracle) (c : ChainSpec) : TestT IO Built := do
  let answer ← oracle.ask (["chain"] ++ c.words)
  let groups := answer.splitOn "/"
  if groups.length ≠ 4 then failWith s!"the oracle answered: {answer}"
  let records (blocks : List BlockSpec) (word : String) : TestT IO (List BlockRecord) := do
    let raws := if word = "" then [] else word.splitOn ";"
    if raws.length ≠ blocks.length then failWith s!"the oracle answered {raws.length} blocks"
    orFail ((blocks.zip raws).mapM fun (b, r) => b.record r)
  let canonical ← records c.blocks groups[0]!
  let side ← records c.side groups[1]!
  let pending ← records c.pending.toList groups[2]!
  let hashes := groups[3]!.splitOn "."
  let all := canonical ++ side ++ pending
  (all.map fun r => hexVec r.hash) === hashes
  let hashOf (n : Option Nat) : Option Hash32 := n.map fun n =>
    ((canonical.find? (·.block.header.number = n)).map (·.hash)).getD (Vector.replicate 32 0xee)
  match viewOf c.config canonical pending.head? (hashOf c.safe) (hashOf c.finalized) side with
  | some view => pure ⟨view, all, hashes⟩
  | none => failWith "a chain has no block"

/-! ## Generators -/

/-- The addresses that write logs. -/
def logAddresses : List Address := [addressOf 0xc5 0x05, addressOf 0xc6 0x06, addressOf 0xc7 0x07]

/-- The topics of logs, as numbers. -/
def logTopics : List Nat :=
  [1, 2, 3, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef]

/-- A log: an address and up to four topics from few values, so that a filter meets some. -/
def genLog : Gen LogSpec := do
  let address ← Gen.element logAddresses
  let topics ← Gen.list (.constant 0 4) (Gen.element logTopics)
  let data ← genBytes (.linear 0 8)
  pure ⟨address, topics, data⟩

/-- A transaction of a block at a fork, of a type that the fork has. -/
def genTxSpec (fork : Fork) (baseFee : Nat) : Gen TxSpec := do
  let type ← Gen.element (typesAt fork)
  let key ← Gen.nat (.constant 0 3)
  let chain ← if type ≠ 0 then pure 1
    else if fork ≥ .spuriousDragon then Gen.element [0, 1] else pure 0
  let nonce ← Gen.nat (.linear 0 300)
  let tip ← genTip
  let cap ← Gen.frequency [(2, pure tip), (1, genTip)]
  let fee := if fork ≥ .london then baseFee else 0
  let gas ← Gen.element [21000, 100000, 30000000]
  let creates ← Gen.frequency [(3, pure false), (1, pure (decide (type < 3)))]
  let to ← Gen.element ([addressOf 0xaa 0xbb] ++ logAddresses)
  let value ← Gen.frequency [(1, pure 0), (1, genNatBits 96)]
  let data ← genBytes (.linear 0 12)
  let access ← if type = 0 then pure [] else
    Gen.list (.constant 0 2) (Gen.zip (Gen.element logAddresses)
      (Gen.list (.constant 0 2) (Gen.nat (.constant 0 3))))
  let blobs ← if type = 3 then
      Gen.list (.constant 1 3) ((2 ^ 248 + ·) <$> Gen.nat (.constant 0 9))
    else pure []
  let auths ← if type = 4 then
      Gen.list (.constant 1 2) (do
        let chain ← Gen.element [0, 1]
        let address ← Gen.element logAddresses
        let nonce ← Gen.nat (.constant 0 3)
        let key ← Gen.nat (.constant 4 7)
        pure ⟨chain, address, nonce, key⟩)
    else pure []
  let blobFee ← Gen.element [1, 1000]
  pure ⟨type, key, chain, nonce, fee + tip, tip, fee + cap, gas, if creates then none else some to,
    value, data, access, blobFee, blobs, auths⟩

/-- A transaction with its receipt: a gas used, an outcome and some logs. -/
def genTxEntry (fork : Fork) (baseFee : Nat) : Gen TxEntry := do
  let spec ← genTxSpec fork baseFee
  let gasUsed ← genGasUsed
  let succeeded ← Gen.frequency [(3, pure true), (1, pure false)]
  let logs ← Gen.frequency [(1, pure []), (2, Gen.list (.constant 1 3) genLog)]
  pure ⟨spec, gasUsed, succeeded, logs⟩

/-- A block at a number and a time, at the fork that the timeline gives it. -/
def genBlockSpec (config : ChainConfig) (start : Fork) (number time : Nat) (parent : UInt8) :
    Gen BlockSpec := do
  let fork := (config.activeFork number time).getD start
  let baseFee ← Gen.element [7, 1000, 10 ^ 9]
  let txs ← Gen.list (.constant 0 4) (genTxEntry fork baseFee)
  let used := (txs.map (·.gasUsed)).sum
  let excess ← Gen.element [0, 2 ^ 17, 5000000, 50000000]
  let blobUsed := 2 ^ 17 * ((txs.map (·.spec.blobs.length)).sum)
  let difficulty ← if fork < .paris then Gen.element [131072, 2 ^ 70] else pure 0
  pure ⟨fork, ⟨number, time, 30000000, used, baseFee, excess, blobUsed, addressOf 0xba 0x5e,
    difficulty, 0x11, Vector.replicate 32 parent⟩, txs⟩

/-- The blocks of a chain from a number and a time on. -/
def genBlockSpecs (config : ChainConfig) (start : Fork) : Nat → Nat → List Nat →
    Gen (List BlockSpec)
  | _, _, [] => pure []
  | number, time, gap :: gaps => do
    let block ← genBlockSpec config start number time 0
    let rest ← genBlockSpecs config start (number + 1) (time + gap) gaps
    pure (block :: rest)

/-- A chain: a walk of one or two forks, some blocks, and sometimes blocks off the chain. -/
def genChainSpec : Gen ChainSpec := do
  let first ← Gen.nat (.constant 0 (timeline.length - 1))
  let second ← Gen.frequency [(1, pure none), (1, pure (timeline[first + 1]?))]
  let start := timeline.getD first .frontier
  let number ← Gen.element [0, 1, 5, 1000]
  let time ← Gen.element [1000, 1700000000]
  let gaps ← Gen.list (.constant 1 6) (Gen.element [1, 12])
  let count := gaps.length
  let timeAt (i : Nat) : Nat := time + (gaps.take i).sum
  let place ← Gen.nat (.constant 1 count)
  let activations : List (Fork × Activation) :=
    [(start, if start < .shapella then .block 0 else .time 0)] ++ second.toList.map fun fork =>
      if fork < .shapella then (fork, .block (number + place)) else (fork, .time (timeAt place))
  let config : ChainConfig := ⟨1, addressOf 0xde 0x90, activations, []⟩
  let blocks ← genBlockSpecs config start number time gaps
  -- A block off the chain has the number and the time of a canonical one, and another parent.
  let side ← Gen.frequency [(2, pure []),
    (1, do
      let i ← Gen.nat (.constant 0 (count - 1))
      let block ← genBlockSpec config start (number + i) (timeAt i) 0x55
      pure [block])]
  let pending ← Gen.frequency [(2, pure none),
    (1, some <$> genBlockSpec config start (number + count) (timeAt count) 0)]
  let mark : Gen (Option Nat) := Gen.frequency [(1, pure none),
    (3, (fun i => some (number + i)) <$> Gen.nat (.constant 0 (count - 1))), (1, pure (some 77777))]
  let safe ← mark
  let finalized ← mark
  pure ⟨activations, blocks, side, pending, safe, finalized⟩

/-! ## The comparison -/

/-- The answer of EthLib to a request is the one of the model.

It gives how the request ended: `ok`, or `error` and the code. -/
def sameAnswer (got : Except RpcError Json) (want : String) : TestT IO String := do
  annotate s!"the reference: {want.take 2000}"
  match got with
  | .error e =>
    annotate s!"EthLib: {showError e} {e.message} {(e.data.map (·.compress)).getD ""}"
    ensure (want.startsWith "error ") "EthLib refuses a request that the model answers"
    let codes := (want.drop 6).toString
    ensure (codes = "*" ∨ codes = toString e.code)
      s!"EthLib answers the code {e.code}, the model {codes}"
    pure s!"error {e.code}"
  | .ok json =>
    annotate s!"EthLib: {json.compress.take 2000}"
    ensure (!want.startsWith "error ") "EthLib answers a request that the model refuses"
    let expected ← orFail (Json.parse want)
    if json.compress ≠ expected.compress then
      -- The first member that differs says more than two long texts.
      for (name, value) in membersOf expected do
        let mine := (json.getObjVal? name).toOption
        if (mine.map (·.compress)) ≠ some value.compress then
          failWith s!"{name} differs.\n  EthLib:    {(mine.map (·.compress)).getD "absent"}\n  \
            reference: {value.compress}"
      failWith "the answers differ"
    pure "ok"

end RpcProperty

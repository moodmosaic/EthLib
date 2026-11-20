import Property.Rpc.World

/-!
# The fee history

`eth_feeHistory` reads headers, the fees of transactions and the gas of receipts.

So a view here is plain fields: forks on a timeline, headers, and transactions with a gas used.

The request goes through `ChainView.call` as JSON, so the readers of its parameters run too.

The reference is `oracle/rpc_fees.py`, a model from `fee_market.yaml`, the fee EIPs and go-ethereum.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Blocks EthLib.Execution.Transactions EthLib.Execution.Rpc
open Lean (Json)

namespace RpcProperty

/-! ## A view of fees -/

/-- A transaction as what the fee history reads of it. -/
structure FeeTx where
  kind : Nat
  gasPrice : Nat
  maxFee : Nat
  priority : Nat
  gasUsed : Nat
  deriving Repr

/-- The transaction of EthLib with the fees, unsigned. -/
def FeeTx.toTransaction (t : FeeTx) : Transaction :=
  let u (n : Nat) : U256 := BitVec.ofNat 256 n
  let to : Address := addressOf 0xaa 0xbb
  match t.kind with
  | 0 => .legacy { nonce := 0, gasPrice := u t.gasPrice, gas := 21000, to := some to, value := 0
                   data := .empty, v := 27, r := 1, s := 1 }
  | 1 => .accessList { chainId := 1, nonce := 0, gasPrice := u t.gasPrice, gas := 21000
                       to := some to, value := 0, data := .empty, accessList := [], yParity := 0
                       r := 1, s := 1 }
  | 2 => .feeMarket { chainId := 1, nonce := 0, maxPriorityFeePerGas := u t.priority
                      maxFeePerGas := u t.maxFee, gas := 21000, to := some to, value := 0
                      data := .empty, accessList := [], yParity := 0, r := 1, s := 1 }
  | 3 => .blob { chainId := 1, nonce := 0, maxPriorityFeePerGas := u t.priority
                 maxFeePerGas := u t.maxFee, gas := 21000, to, value := 0, data := .empty
                 accessList := [], maxFeePerBlobGas := 1, blobVersionedHashes := [word32 1]
                 yParity := 0, r := 1, s := 1 }
  | _ => .setCode { chainId := 1, nonce := 0, maxPriorityFeePerGas := u t.priority
                    maxFeePerGas := u t.maxFee, gas := 21000, to, value := 0, data := .empty
                    accessList := [], authorizations := [], yParity := 0, r := 1, s := 1 }

/-- A block as what the fee history reads of it. -/
structure FeeBlock where
  fork : Fork
  header : HeaderSpec
  txs : List FeeTx
  deriving Repr

/-- The block in the text form of the oracle. -/
def FeeBlock.show (b : FeeBlock) : String :=
  let txs := b.txs.map fun t => s!"{t.kind}:{t.gasPrice}:{t.maxFee}:{t.priority}:{t.gasUsed}"
  s!"{b.fork.name}|{b.header.show}|{joined "/" txs}"

/-- The record of the block: its header, its transactions, and a receipt for the gas of each. -/
def FeeBlock.record (b : FeeBlock) : Except String BlockRecord :=
  let outcome : Outcome b.fork :=
    if h : Fork.byzantium ≤ b.fork then .status h true
    else .postState (Nat.lt_of_not_le h) (Vector.replicate 32 0)
  let receipts := makeReceipts (b.txs.map fun t => (outcome, t.gasUsed, []))
  recordOf b.fork (b.header.toHeader b.fork) ⟨∅, ∅, ∅⟩ (b.txs.map (·.toTransaction))
    ((b.txs.map fun t => t.kind.toUInt8).zip receipts)

/-- A view of fees: a timeline, the blob schedules of the chain, and its blocks. -/
structure FeeView where
  activations : List (Fork × Activation)
  schedules : List (Activation × Nat × Nat × Nat)
  blocks : List FeeBlock
  pending : Option FeeBlock
  /-- The numbers of the blocks that are safe and finalized, or none. -/
  safe : Option Nat
  finalized : Option Nat
  deriving Repr

/-- An activation in the text form of the oracle. -/
def showActivation : Activation → String
  | .block n => s!"b:{n}"
  | .time t => s!"t:{t}"

/-- The blob schedule of EthLib with three numbers, which the generator keeps within its bounds. -/
def scheduleOf (numbers : Nat × Nat × Nat) : BlobSchedule :=
  let (target, most, fraction) := numbers
  if ok : target ≤ most ∧ 0 < most ∧ 0 < fraction then
    ⟨target, most, fraction, ok.1, ok.2.1, ok.2.2⟩
  else ⟨3, 6, 3338477, by decide, by decide, by decide⟩

/-- The configuration of the chain of a view. -/
def FeeView.config (v : FeeView) : ChainConfig where
  chainId := 1
  depositContractAddress := addressOf 0xde 0x90
  activations := v.activations
  blobSchedules := v.schedules.map fun (a, numbers) => (a, scheduleOf numbers)

/-- The words of the view in a command of the oracle. -/
def FeeView.words (v : FeeView) : List String :=
  let mark (n : Option Nat) : String := (n.map toString).getD "-"
  [joined "," (v.activations.map fun (f, a) => s!"{f.name}:{showActivation a}"),
   joined "," (v.schedules.map fun (a, t, m, f) => s!"{showActivation a}:{t}:{m}:{f}"),
   joined ";" (v.blocks.map (·.show)),
   s!"{mark v.safe}&{mark v.finalized}&{(v.pending.map (·.show)).getD "-"}"]

/-- The chain view of EthLib with the blocks. -/
def FeeView.view (v : FeeView) : Except String ChainView := do
  let records ← v.blocks.mapM (·.record)
  let pending ← v.pending.mapM (·.record)
  let hashOf (n : Option Nat) : Option Hash32 := n.map fun n =>
    ((records.find? (·.block.header.number = n)).map (·.hash)).getD (Vector.replicate 32 0xee)
  match viewOf v.config records pending (hashOf v.safe) (hashOf v.finalized) with
  | some view => pure view
  | none => .error "a view has no block"

/-! ## Generators -/

/-- The forks of a timeline: those that the reference has, in order. -/
def timeline : List Fork := forks.map (·.1)

/-- The types of transaction that a fork has. -/
def typesAt (fork : Fork) : List Nat :=
  [0] ++ (if fork ≥ .berlin then [1] else []) ++ (if fork ≥ .london then [2] else []) ++
    (if fork ≥ .dencun then [3] else []) ++ (if fork ≥ .pectra then [4] else [])

/-- A tip per gas: few values, so that transactions tie. -/
def genTip : Gen Nat := Gen.frequency [(4, Gen.element [0, 1, 2, 5, 1000]),
  (1, Gen.nat (.exponential 0 (10 ^ 12)))]

/-- The gas that a transaction used: values that meet a share of the block exactly, and others. -/
def genGasUsed : Gen Nat := Gen.frequency [(4, Gen.element [21000, 21001, 42000, 63000, 1, 3]),
  (1, Gen.nat (.exponential 1 5000000))]

/-- A transaction that pays the base fee of its block and a tip. -/
def genFeeTx (fork : Fork) (baseFee : Nat) : Gen FeeTx := do
  let kind ← Gen.element (typesAt fork)
  let tip ← genTip
  let cap ← Gen.frequency [(2, pure tip), (1, genTip)]
  let gasUsed ← genGasUsed
  let fee := if fork ≥ .london then baseFee else 0
  pure ⟨kind, fee + tip, fee + cap, tip, gasUsed⟩

/-- A block at a number and a time, at the fork that the timeline gives it. -/
def genFeeBlock (config : ChainConfig) (start : Fork) (number time : Nat) : Gen FeeBlock := do
  let fork := (config.activeFork number time).getD start
  let baseFee ← Gen.element [7, 1000, 10 ^ 9, 10 ^ 11]
  let txs ← Gen.list (.linear 0 5) (genFeeTx fork baseFee)
  let used := (txs.map (·.gasUsed)).sum
  let gasLimit ← Gen.element [used, 2 * used, 2 * used + 1, 30000000, 3 * used + 7]
  let excess ← Gen.element [0, 2 ^ 17, 393216, 5000000, 50000000, 200000000]
  let blobUsed ← Gen.element [0, 2 ^ 17, 3 * 2 ^ 17, 6 * 2 ^ 17, 9 * 2 ^ 17, 21 * 2 ^ 17]
  pure ⟨fork, ⟨number, time, max gasLimit 5000, used, baseFee, excess, blobUsed,
    addressOf 0xba 0x5e, 0, 0x11, Vector.replicate 32 0⟩, txs⟩

/-- The blocks of a chain from a number and a time on, each some seconds after the one before. -/
def genFeeBlocks (config : ChainConfig) (start : Fork) : Nat → Nat → List Nat →
    Gen (List FeeBlock)
  | _, _, [] => pure []
  | number, time, gap :: gaps => do
    let block ← genFeeBlock config start number time
    let rest ← genFeeBlocks config start (number + 1) (time + gap) gaps
    pure (block :: rest)

/-- A view: a walk along the timeline, whose forks activate at blocks of the chain or after it. -/
def genFeeView : Gen FeeView := do
  -- Half of the walks start just before London or Dencun, where the fee fields appear.
  let first ← Gen.frequency [(2, Gen.nat (.constant 0 (timeline.length - 1))),
    (1, Gen.element [9, 10]), (1, Gen.element [16, 17])]
  let steps ← Gen.list (.constant 0 3) (Gen.frequency [(4, pure 1), (1, Gen.element [2, 3, 7])])
  let path := (steps.foldl (fun (acc : List Nat) step => acc ++ [acc.getLast! + step]) [first]
    ).filterMap (timeline[·]?)
  let start := path.headD .frontier
  let number ← Gen.element [0, 1, 5, 1000]
  let time ← Gen.element [0, 1000, 1700000000]
  let gaps ← Gen.list (.constant 1 7) (Gen.element [1, 12, 13])
  let count := gaps.length
  -- The time of the block at an index, and of the block after the head.
  let timeAt (i : Nat) : Nat := time + (gaps.take i).sum
  let places ← Gen.list (.singleton (path.length - 1)) (Gen.nat (.constant 1 count))
  let late ← Gen.element [0, 0, 1, 11]
  let later := (path.drop 1).zip (places.mergeSort (· ≤ ·))
  let activations : List (Fork × Activation) :=
    [(start, if start < .shapella then .block 0 else .time 0)] ++ later.map fun (fork, i) =>
      if fork < .shapella then (fork, .block (number + i))
      -- A fork by time after the head starts one second after it, or later.
      else (fork, .time (if i = count then timeAt (count - 1) + 1 + late else timeAt i))
  let schedules ← Gen.frequency [(3, pure []),
    (1, do
      let i ← Gen.nat (.constant 0 count)
      let numbers ← Gen.element [(1, 2, 1000000), (6, 9, 5007716), (2, 2, 3338477)]
      pure [(Activation.time (timeAt i), numbers)])]
  let config : ChainConfig := ⟨1, addressOf 0xde 0x90, activations,
    schedules.map fun (a, numbers) => (a, scheduleOf numbers)⟩
  let blocks ← genFeeBlocks config start number time gaps
  let pending ← Gen.frequency [(2, pure none),
    (1, some <$> genFeeBlock config start (number + count) (timeAt count))]
  let mark : Gen (Option Nat) := Gen.frequency [(2, pure none),
    (2, (fun i => some (number + i)) <$> Gen.nat (.constant 0 (count - 1))), (1, pure (some 77777))]
  let safe ← mark
  let finalized ← mark
  pure ⟨activations, schedules, blocks, pending, safe, finalized⟩

/-- Percentiles in the text of JSON, in rising order of their values, no two equal. -/
def percentilePool : List String :=
  ["0", "1e-1", "5", "1e1", "12.5", "2.5e1", "33.3", "50", "50.5", "66.67", "75", "99.9",
    "1E2"]

/-- The texts of some percentiles: mostly a rising list, sometimes with one fault. -/
def genPercentiles : Gen (List String) := do
  let rising ← Gen.subsequence percentilePool
  let rising := rising.take 5
  let at_ ← Gen.nat (.constant 0 rising.length)
  let put (text : String) : List String := rising.take at_ ++ [text] ++ rising.drop at_
  Gen.frequency [
    (16, pure rising),
    (2, pure []),
    (1, pure (put ((rising[at_ - 1]?).getD "50"))),
    (1, pure rising.reverse),
    (2, put <$> Gen.element ["50", "50.0", "5e1", "100", "100.0", "0", "0.0", "-0"]),
    (1, put <$> Gen.element ["101", "100.0001", "-1", "-0.5", "1e3", "\"50\"", "null", "true",
      "[50]"])]

/-- What a request names as its newest block. -/
def genNewest (v : FeeView) : Gen String :=
  let head := (v.blocks.getLast?.map (·.header.number)).getD 0
  let low := (v.blocks.head?.map (·.header.number)).getD 0
  Gen.frequency [(3, pure "latest"), (3, toString <$> Gen.nat (.constant low head)),
    (1, Gen.element ["earliest", "pending", "safe", "finalized"]),
    (1, toString <$> Gen.element [head + 1, head + 100, low - 1])]

/-! ## The comparison -/

/-- The JSON of a block parameter of a request, from its name or its number. -/
def newestJson (name : String) : Json :=
  match name.toNat? with
  | some n => .str ("0x" ++ hexNat n)
  | none => .str name

/-- The members of a JSON object, or none. -/
def membersOf (j : Json) : List (String × Json) :=
  match j with
  | .obj kvs => kvs.toList
  | _ => []

/-- The quantities of a JSON array as numbers in decimal, joined with `,`. -/
def quantities (j : Json) : Except String String := do
  let items ← j.getArr?
  let numbers ← items.toList.mapM fun item => do
    let text ← item.getStr?
    if !text.startsWith "0x" then throw s!"not a quantity: {text}"
    let digits := (text.drop 2).toString
    if digits.isEmpty ∨ (digits.length > 1 ∧ digits.startsWith "0") then
      throw s!"not a quantity: {text}"
    let value ← digits.toList.foldlM (init := 0) fun acc c =>
      match hexDigit? c with
      | some d => pure (16 * acc + d)
      | none => throw s!"not a quantity: {text}"
    pure (toString value)
  pure (joined "," numbers)

/-- Whether a JSON number is a ratio rounded down to 18 decimal places.

A numerator above the denominator counts as the denominator, and a denominator of 0 gives 0. -/
def isRatio (j : Json) (ratio : String) : Bool :=
  match j, ratio.splitOn "/" with
  | .num ⟨m, e⟩, [num, den] =>
    let (num, den) := (num.toNat!, den.toNat!)
    let digits := if den = 0 then 0 else min num den * 10 ^ 18 / den
    m ≥ 0 && m.toNat * 10 ^ 18 == digits * 10 ^ e
  | _, _ => false

/-- The ratios of a JSON array are those of the reference. -/
def sameRatios (name : String) (j : Json) (want : String) : TestT IO Unit := do
  let items ← orFail (j.getArr?)
  let want := if want = "-" then [] else want.splitOn ","
  if items.size ≠ want.length then failWith s!"{name}: {items.size} ratios, not {want.length}"
  for (item, ratio) in items.toList.zip want do
    if !isRatio item ratio then failWith s!"{name}: {item.compress} is not {ratio}"

/-- The fee history of a view is the one of the model.

The model follows `fee_market.yaml`, EIP-1559, EIP-4844 with EIP-7691, EIP-7892 and EIP-7918.

Its percentile rule is go-ethereum's, with an exact comparison where go-ethereum rounds in floats.

A request with a fault gets the code of invalid parameters, or of a resource not found. -/
def feeHistory (oracle : Oracle) : Property IO := propertyM do
  let v ← forAll genFeeView
  let count ← forAll (Gen.frequency [(1, pure 0), (3, Gen.nat (.constant 1 4)),
    (4, Gen.nat (.constant 5 12)), (1, pure 1024)])
  let newest ← forAll (genNewest v)
  let percentiles ← forAll genPercentiles
  pure do
    let view ← orFail v.view
    let text := s!"[{", ".intercalate percentiles}]"
    let ps ← orFail (Json.parse text)
    let got := view.call "eth_feeHistory" [.str ("0x" ++ hexNat count), newestJson newest, ps]
    let want ← oracle.ask (["feehistory"] ++ v.words ++ [toString count, newest, text])
    annotate s!"the reference: {want}"
    let forksOf := (v.blocks.map (·.fork)).eraseDups
    classify "the view crosses a fork" (forksOf.length > 1)
    classify "the view has blocks before and from London"
      (forksOf.any (· < .london) ∧ forksOf.any (· ≥ .london))
    classify "the view has blocks before and from Dencun"
      (forksOf.any (· < .dencun) ∧ forksOf.any (· ≥ .dencun))
    classify "the chain sets a blob schedule" (!v.schedules.isEmpty)
    match got with
    | .error e =>
      annotate s!"EthLib: {showError e} {e.message} {(e.data.map (·.compress)).getD ""}"
      classify s!"refused: {e.code}" true
      ensure (want.startsWith "error") "EthLib refuses a request that the model answers"
      ensure (((want.drop 6).toString.splitOn " or ").contains (toString e.code))
        s!"EthLib answers the code {e.code}, the model {want}"
    | .ok json =>
      annotate s!"EthLib: {json.compress}"
      cover 40 "answered" true
      ensure (!want.startsWith "error") "EthLib answers a request that the model refuses"
      let fields := want.splitOn "|"
      if fields.length ≠ 7 then failWith s!"the oracle answered: {want}"
      let field (name : String) : TestT IO Json := orFail (json.getObjVal? name)
      (← orFail (quantities (.arr #[← field "oldestBlock"]))) === fields[0]!
      (← orFail (quantities (← field "baseFeePerGas"))) === fields[1]!
      (← orFail (quantities (← field "baseFeePerBlobGas"))) === fields[2]!
      sameRatios "gasUsedRatio" (← field "gasUsedRatio") fields[3]!
      sameRatios "blobGasUsedRatio" (← field "blobGasUsedRatio") fields[4]!
      let names := (membersOf json).map (·.1)
      if fields[5]! = "none" then
        ensure (!names.contains "reward") "a reward without a percentile"
        ensure (names.length = 5) s!"the members are {names}"
      else
        ensure (names.length = 6) s!"the members are {names}"
        let rows ← orFail (do (← json.getObjVal? "reward").getArr?)
        let rows ← orFail (rows.toList.mapM quantities)
        joined ";" rows === fields[5]!
        classify "go-ethereum's rounding gives another reward" (fields[5]! ≠ fields[6]!)
      let held := v.blocks.length + (if v.pending.isSome then 1 else 0)
      let blocks := if fields[3]! = "-" then 0 else (fields[3]!.splitOn ",").length
      classify "no block in the range" (blocks = 0)
      cover 15 "three blocks or more in the range" (blocks ≥ 3)
      classify "the count is above the blocks held" (count > held)
      cover 20 "percentiles are asked for" (fields[5]! ≠ "none")
      classify "a block of the range has tied tips" (v.blocks.any fun b =>
        (b.txs.map (·.priority)).eraseDups.length < b.txs.length)
      classify "the next base fee per blob gas is above 1"
        (((fields[2]!.splitOn ",").getLast?.bind String.toNat?).getD 0 > 1)

end RpcProperty

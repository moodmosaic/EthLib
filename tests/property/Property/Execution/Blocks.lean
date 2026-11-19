import Property.Execution.Common

/-!
# Headers, receipts, blooms, difficulty and requests, against execution-specs
-/

open Hedgehog Support EthLib EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace ExecutionProperty

/-- A log of a receipt, which is not a log of a test. -/
abbrev TxLog := Execution.Blocks.Log

/-! ## The logs bloom -/

/-- A log: an address, at most four topics, and data. -/
def genLog : Gen TxLog :=
  Execution.Blocks.Log.mk <$> genAddress <*> Gen.list (.linear 0 4) genWord <*>
    genBytes (.linear 0 40)

/-- A log as a word of a command of the oracle. -/
def logWord (log : TxLog) : String :=
  s!"{hexV log.address}:{",".intercalate (log.topics.map hexV)}:{hex log.data}"

/-- The item of a log. -/
def logItem (log : TxLog) : Item :=
  .list [.bytes ⟨log.address.toArray⟩, .list (log.topics.map fun t => .bytes ⟨t.toArray⟩),
    .bytes log.data]

/-- The logs bloom is the one of execution-specs and of eth-bloom.

Every entry of the logs may be in the filter, and the filter of no log is all zero. -/
def bloomFilter (oracle : Oracle) : Property IO := propertyM do
  let logs ← forAllWith (fun logs => " ".intercalate (logs.map logWord))
    (Gen.list (.linear 0 6) genLog)
  pure do
    let expected ← oracle.ask ("bloom" :: logs.map logWord)
    hexV (logsBloom logs) === expected
    for entry in logs.flatMap Bloom.entries do
      ensure (Bloom.mayContain (Bloom.ofLogs logs) entry) "an entry of a log is not in the filter"
    if logs.isEmpty then (logsBloom logs).toList === List.replicate 256 0

/-! ## Headers -/

/-- The fields of a header as plain values, for every fork at once. -/
structure RawHeader where
  parentHash : ByteArray
  ommersHash : ByteArray
  coinbase : ByteArray
  roots : ByteArray
  difficulty : Nat
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : ByteArray
  nonce : ByteArray
  baseFee : Nat
  blobGasUsed : Nat
  excessBlobGas : Nat

/-- The item of a header at a fork: the fields that the fork has, in order. -/
def RawHeader.item (fork : Fork) (h : RawHeader) : Item :=
  let word := Item.bytes h.roots
  .list ([.bytes h.parentHash, .bytes h.ommersHash, .bytes h.coinbase, word, word, word,
    .bytes (bytesOf (List.replicate 256 0)), .scalar h.difficulty, .scalar h.number,
    .scalar h.gasLimit, .scalar h.gasUsed, .scalar h.timestamp, .bytes h.extraData, word,
    .bytes h.nonce]
    ++ (if fork ≥ .london then [.scalar h.baseFee] else [])
    ++ (if fork ≥ .shapella then [word] else [])
    ++ (if fork ≥ .dencun then [.scalar h.blobGasUsed, .scalar h.excessBlobGas, word] else [])
    ++ (if fork ≥ .pectra then [word] else []))

/-- The hash of the empty list of ommers. -/
def emptyOmmers : ByteArray := ⟨(keccak256 ⟨#[0xc0]⟩).toArray⟩

/-- A header that some chain could hold: every field in its range. -/
def genRawHeader (fork : Fork) : Gen RawHeader := do
  let word ← genBytesN 32
  let ommersHash ← if fork ≥ .paris then pure emptyOmmers else
    Gen.element [emptyOmmers, word]
  let gasLimit ← Gen.frequency [(3, Gen.nat (.constant 5000 40000000)),
    (1, Gen.element [5000, 5001, 1024, 2 ^ 63 - 1])]
  let gasUsed ← Gen.frequency [(2, Gen.nat (.constant 0 gasLimit)),
    (1, Gen.element [0, gasLimit / 2, gasLimit / 2 + 1, gasLimit / 2 - 1, gasLimit])]
  let difficulty ← if fork ≥ .paris then pure 0 else
    Gen.frequency [(2, Gen.nat (.exponential 131072 (2 ^ 70))),
      (1, Gen.element [131072, 131073, 133120, 2 ^ 64])]
  let number ← Gen.frequency [(1, Gen.nat (.exponential 0 20000000)),
    (1, (fun (k : Nat) (d : Nat) => k * 100000 + d - 2) <$> Gen.nat (.constant 0 160) <*>
      Gen.nat (.constant 0 3))]
  pure {
    parentHash := word, ommersHash, coinbase := word.extract 0 20, roots := word
    difficulty, number, gasLimit, gasUsed
    timestamp := ← Gen.nat (.exponential 0 (2 ^ 40))
    extraData := ← genBytes (.linear 0 32)
    nonce := if fork ≥ .paris then bytesOf (List.replicate 8 0) else word.extract 0 8
    baseFee := ← Gen.frequency [(3, Gen.nat (.exponential 0 (2 ^ 40))),
      (1, Gen.element [0, 1, 7, 8])]
    blobGasUsed := 131072 * (← Gen.nat (.constant 0 22))
    excessBlobGas := ← Gen.frequency [(2, (131072 * ·) <$> Gen.nat (.constant 0 400)),
      (1, Gen.nat (.exponential 0 (2 ^ 40)))] }

/-- What EthLib says of the bytes of a header at a fork, in the words of the oracle. -/
def describeHeader (fork : Fork) (bytes : ByteArray) : String :=
  match (Codec.decode bytes : Except RlpError (Header fork)) with
  | .error _ => "error"
  | .ok h =>
    let since := (if hh : Fork.london ≤ fork then [h.baseFeePerGas hh] else [])
      ++ (if hh : Fork.dencun ≤ fork then
        [(h.blobGasUsed hh).toNat, (h.excessBlobGas hh).toNat] else [])
    let fields := [h.difficulty, h.number, h.gasLimit, h.gasUsed, h.timestamp.toNat] ++ since
    " ".intercalate (["ok", orError (hexV <$> h.hash)] ++ fields.map toString)

/-- A header as bytes, almost valid, at a fork. -/
def genHeaderBytes : Gen ((Fork × String) × ByteArray) := do
  let fork ← genFork
  let header ← genRawHeader fork.1
  let wide ← Gen.frequency [(5, pure header),
    (1, (fun (n : Nat) => { header with blobGasUsed := n }) <$> Gen.element [2 ^ 64 - 1, 2 ^ 64]),
    (1, (fun (n : Nat) => { header with timestamp := n }) <$> Gen.element [2 ^ 256 - 1, 2 ^ 256]),
    (1, (fun (n : Nat) => { header with gasLimit := n, difficulty := n, baseFee := n }) <$>
      Gen.element [2 ^ 64, 2 ^ 256 - 1])]
  let mutations ← Gen.frequency [(2, pure []), (1, Gen.list (.constant 1 2) genMutation)]
  -- Now and then the fields of the next or the previous fork.
  let shape ← Gen.frequency [(8, pure fork.1),
    (1, Gen.element [.london, .shapella, .dencun, .pectra, .grayGlacier])]
  pure (fork, enc (mutateAll mutations (wide.item shape)))

/-- EthLib and execution-specs agree on the bytes of a header.

They agree on whether the bytes hold a header of the fork, and then on its hash and on the
numbers that it holds. -/
def headerBytes (oracle : Oracle) : Property IO := propertyM do
  let (fork, bytes) ← forAllWith (fun (fork, bytes) => s!"{fork.2} {hex bytes}") genHeaderBytes
  pure do
    describeHeader fork.1 bytes === (← oracle.ask ["header", fork.2, hex bytes])

/-- A number that is mostly the right one, and now and then one beside it. -/
def genNear (right : Nat) : Gen Nat :=
  Gen.frequency [(14, pure right), (1, pure (right + 1)), (1, pure (right - 1))]

/-- A header and a child that follows it at the same fork, right in most fields.

The child takes what EthLib expects of it, and now and then a value beside that.
So a rule that EthLib has wrong shows as a child that the reference refuses. -/
def genHeaderPair : Gen ((Fork × String) × RawHeader × RawHeader) := do
  let fork ← genFork
  let parent ← genRawHeader fork.1
  let parentBytes := enc (parent.item fork.1)
  let step := parent.gasLimit / 1024
  let gasLimit ← Gen.frequency [(4, pure parent.gasLimit),
    (4, Gen.element [parent.gasLimit + step - 1, parent.gasLimit - step + 1]),
    (1, Gen.element [parent.gasLimit + step, parent.gasLimit - step, parent.gasLimit + step + 1,
      parent.gasLimit - step - 1, 4999, 5000])]
  let gasUsed ← Gen.frequency [(8, Gen.nat (.constant 0 gasLimit)), (1, pure gasLimit),
    (1, pure (gasLimit + 1))]
  let elapsed ← Gen.frequency [(8, Gen.nat (.constant 1 30)), (2, Gen.nat (.constant 1 1200)),
    (1, pure 0)]
  let timestamp := parent.timestamp + elapsed
  let number ← genNear (parent.number + 1)
  let ommersHash ← if fork.1 ≥ .paris then
      Gen.frequency [(15, pure emptyOmmers), (1, pure parent.roots)]
    else pure parent.roots
  let nonce ← Gen.frequency [(15, pure (bytesOf (List.replicate 8 0))),
    (1, pure (bytesOf (List.replicate 7 0 ++ [1])))]
  let parentHash ← Gen.frequency [(15, pure ⟨(keccak256 parentBytes).toArray⟩),
    (1, pure parent.roots)]
  let extraData ← genBytes (.constant 0 33)
  -- What EthLib expects of the child, read from the parent as EthLib decodes it.
  let (baseFee, excess, difficulty) :=
    match (Codec.decode parentBytes : Except RlpError (Header fork.1)) with
    | .error _ => (0, 0, 0)
    | .ok p =>
      let excess := if hd : Fork.dencun ≤ fork.1 then
          if hl : Fork.london ≤ fork.1 then expectedExcessBlobGas hl hd p else 0
        else 0
      (expectedBaseFeeAcross p, excess,
        blockDifficulty fork.1 number timestamp parent.timestamp parent.difficulty
          (parent.ommersHash.data != emptyOmmers.data))
  let child : RawHeader := {
    parentHash, ommersHash, coinbase := parent.coinbase, roots := parent.roots
    difficulty := ← genNear difficulty
    number, gasLimit, gasUsed, timestamp, extraData, nonce
    baseFee := ← genNear baseFee
    blobGasUsed := 131072 * (← Gen.nat (.constant 0 9))
    excessBlobGas := ← genNear excess }
  pure (fork, parent, child)

/-- EthLib accepts a header after its parent exactly when execution-specs does, the seal aside. -/
def headerAfterParent (oracle : Oracle) : Property IO := propertyM do
  let (fork, parent, child) ← forAllWith
    (fun (fork, parent, child) =>
      s!"{fork.2} {hex (enc (parent.item fork.1))} {hex (enc (child.item fork.1))}")
    genHeaderPair
  pure do
    let parentBytes := enc (parent.item fork.1)
    let childBytes := enc (child.item fork.1)
    let expected ← oracle.ask ["headerpair", fork.2, hex parentBytes, hex childBytes]
    annotate s!"the reference: {expected}"
    let decoded : Except RlpError (Header fork.1 × Header fork.1) := do
      pure (← Codec.decode parentBytes, ← Codec.decode childBytes)
    match decoded with
    | .error _ => failWith "EthLib does not decode a header"
    | .ok (p, c) =>
      let result := checkHeader (Nat.le_refl _) p c
      annotate s!"EthLib: {repr result}"
      result.isOk === (expected == "ok")

/-! ## Receipts -/

/-- A receipt as bytes at a fork: its type byte, or none, and its almost valid fields. -/
def genReceiptBytes : Gen ((Fork × String) × ByteArray) := do
  let fork ← genFork
  let outcome ← Gen.frequency [
    (if fork.1 ≥ .byzantium then 6 else 1, Item.scalar <$> Gen.element [0, 1]),
    (if fork.1 ≥ .byzantium then 1 else 6, Item.bytes <$> genBytesN 32),
    (1, Item.scalar <$> Gen.element [2, 255, 256])]
  let gas ← Item.scalar <$> genNatNear 64 [2 ^ 64, 2 ^ 256]
  let logs ← Gen.list (.linear 0 3) genLog
  let bloomBytes ← Gen.frequency [(8, pure ⟨(logsBloom logs).toArray⟩), (1, genBytesN 255)]
  let item := Item.list [outcome, gas, .bytes bloomBytes, .list (logs.map logItem)]
  let mutations ← Gen.frequency [(3, pure []), (1, Gen.list (.constant 1 2) genMutation)]
  let types := (List.range 5).filter fun type =>
    type = 0 ∨ (Execution.Transactions.typeFork (UInt8.ofNat type)).any (· ≤ fork.1)
  let type ← Gen.frequency [(9, Gen.element types.reverse), (1, Gen.nat (.constant 0 5))]
  let payload := enc (mutateAll mutations item)
  pure (fork, if type = 0 then payload else ⟨#[UInt8.ofNat type]⟩ ++ payload)

/-- What EthLib says of the bytes of a receipt at a fork, in the words of the oracle. -/
def describeReceipt (fork : Fork) (bytes : ByteArray) : String :=
  match decodeReceipt fork bytes with
  | .error _ => "error"
  | .ok (type, r) =>
    let outcome := match r.outcome with
      | .postState _ root => hexV root
      | .status _ succeeded => toString succeeded
    let hash := orError ((fun encoded => hexV (keccak256 encoded)) <$> Codec.encode r)
    s!"ok {type} {outcome} {r.cumulativeGasUsed} {r.logs.length} {hash}"

/-- EthLib and execution-specs agree on the bytes of a receipt.

They agree on whether the bytes hold a receipt of the fork, and then on its type, its outcome,
its gas, its logs and the hash of its fields. -/
def receiptBytes (oracle : Oracle) : Property IO := propertyM do
  let (fork, bytes) ← forAllWith (fun (fork, bytes) => s!"{fork.2} {hex bytes}") genReceiptBytes
  pure do
    describeReceipt fork.1 bytes === (← oracle.ask ["receipt", fork.2, hex bytes])

/-! ## Difficulty and rewards -/

/-- The inputs of the difficulty of a block. -/
structure DifficultyCase where
  fork : Fork × String
  number : Nat
  elapsed : Nat
  parentTimestamp : Nat
  parentDifficulty : Nat
  parentHasOmmers : Bool

instance : Repr DifficultyCase where
  reprPrec c _ := s!"{c.fork.2} number {c.number} elapsed {c.elapsed} parentTimestamp \
    {c.parentTimestamp} parentDifficulty {c.parentDifficulty} ommers {c.parentHasOmmers}"

/-- Inputs around each period of the bomb, each delay, each step of the time, and the minimum. -/
def genDifficultyCase : Gen DifficultyCase := do
  let fork ← genWorkFork
  let delay ← Gen.element [0, 3000000, 5000000, 9000000, 9700000, 10700000, 11400000]
  let number ← Gen.frequency [
    (4, (fun (period : Nat) (d : Nat) => delay + period * 100000 + d - 2) <$>
      Gen.nat (.constant 0 60) <*> Gen.nat (.constant 0 4)),
    (1, Gen.nat (.exponential 0 30000000))]
  let elapsed ← Gen.frequency [(4, Gen.nat (.constant 0 100)), (2, Gen.nat (.constant 880 1010)),
    (1, Gen.nat (.exponential 0 (2 ^ 32)))]
  let parentDifficulty ← Gen.frequency [(2, Gen.nat (.constant 131072 135168)),
    (2, Gen.nat (.exponential 131072 (2 ^ 80))), (1, Gen.element [2 ^ 64 - 1, 2 ^ 64, 2 ^ 128])]
  pure ⟨fork, number, elapsed, ← Gen.nat (.exponential 0 (2 ^ 40)), parentDifficulty,
    ← Gen.bool⟩

/-- The difficulty of a block is the one of execution-specs, at every fork before Paris. -/
def difficulty (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genDifficultyCase
  pure do
    let timestamp := c.parentTimestamp + c.elapsed
    let expected ← oracle.ask ["difficulty", c.fork.2, toString c.number, toString timestamp,
      toString c.parentTimestamp, toString c.parentDifficulty, toString c.parentHasOmmers]
    toString (blockDifficulty c.fork.1 c.number timestamp c.parentTimestamp c.parentDifficulty
      c.parentHasOmmers) === expected

/-- The rewards of a block are those of execution-specs, and none from Paris.

The block reward is the constant of the fork there.
The reward of a beneficiary and of an ommer follow the Yellow Paper, 11.3, in `Nat`. -/
def rewards (oracle : Oracle) : Property IO := propertyM do
  let fork ← forAllWith (·.2) genWorkFork
  let ommers ← forAll (Gen.nat (.constant 0 2))
  let age ← forAll (Gen.nat (.constant 1 7))
  pure do
    let expected ← oracle.ask ["reward", fork.2]
    let some reward := expected.toNat? | failWith expected
    blockReward fork.1 === reward
    minerReward fork.1 ommers === reward + ommers * (reward / 32)
    ommerReward fork.1 age === (8 - age) * reward / 8

/-! ## Requests, deposits and roots -/

/-- The requests hash is the one of EIP-7685: a request of its type alone is left out. -/
def requestsHashOf (oracle : Oracle) : Property IO := propertyM do
  let requests ← forAllWith (fun rs => " ".intercalate (rs.map hex))
    (Gen.list (.linear 0 5) (Gen.frequency [(3, genBytes (.linear 0 40)),
      (2, genBytes (.constant 0 2))]))
  pure do
    hexV (requestsHash requests) === (← oracle.ask ("requestshash" :: requests.map hex))

/-- The data of a deposit log, right in its offsets and sizes, then changed in a few bytes. -/
def genDepositData : Gen ByteArray := do
  let body ← genBytesN 576
  let word (position value : Nat) (data : ByteArray) : ByteArray :=
    (natToBytes 32 value).zipIdx.foldl (fun data (byte, i) => data.set! (position + i) byte) data
  let right := [(0, 160), (32, 256), (64, 320), (96, 384), (128, 512), (160, 48), (256, 32),
    (320, 8), (384, 96), (512, 8)].foldl (fun data (position, value) => word position value data)
    body
  let changes ← Gen.frequency [(2, pure []),
    (3, Gen.list (.constant 1 2) (Gen.zip
      (Gen.frequency [(3, (· + 31) <$> Gen.element [0, 32, 64, 96, 128, 160, 256, 320, 384, 512]),
        (1, Gen.element [0, 159, 160, 161, 255, 287, 319, 351, 415, 543]),
        (1, Gen.nat (.constant 0 575))])
      genByte))]
  let changed := changes.foldl (fun data (position, value) => data.set! position value) right
  Gen.frequency [(8, pure changed), (1, pure (changed.extract 0 575)),
    (1, pure (changed ++ ⟨#[0]⟩))]

/-- The deposit request of a deposit log is the one of execution-specs, or neither reads one. -/
def depositRequest (oracle : Oracle) : Property IO := propertyM do
  let data ← forAllWith hex genDepositData
  pure do
    orError (hex <$> depositRequestOfEvent data) === (← oracle.ask ["deposit", hex data])

/-- A withdrawal: its numbers at the edges of 64 bits. -/
def genWithdrawal : Gen Withdrawal :=
  Withdrawal.mk <$> genUInt64 <*> genUInt64 <*> genAddress <*> genUInt64

/-- The withdrawals root and the root of a list are those of execution-specs.

The lists reach the indices 127 and 128, where the RLP of the index changes its form. -/
def listRoots (oracle : Oracle) : Property IO := propertyM do
  let withdrawals ← forAll (Gen.frequency [(4, Gen.list (.linear 0 20) genWithdrawal),
    (1, Gen.list (.constant 126 131) genWithdrawal)])
  let values ← forAllWith (fun vs => " ".intercalate (vs.map hex))
    (Gen.frequency [(4, Gen.list (.linear 0 20) (genBytes (.linear 1 40))),
      (1, Gen.list (.constant 126 131) (genBytes (.constant 1 3)))])
  pure do
    let words := withdrawals.map fun w =>
      s!"{w.index.toNat}:{w.validatorIndex.toNat}:{hexV w.address}:{w.amount.toNat}"
    orError (hexV <$> withdrawalsRoot withdrawals) === (← oracle.ask ("withdrawalsroot" :: words))
    orError (hexV <$> indexedRoot values) === (← oracle.ask ("indexroot" :: values.map hex))

end ExecutionProperty

namespace ExecutionProperty

open EthLib.Execution.State in
/-- The DAO Fork moves the ether of the accounts of EIP-779 to its recovery contract.

Each account of the list, the length of the list and the recovery contract are those of
execution-specs.
After the fork an account of the list holds nothing, and the recovery contract holds what the
accounts held, with what it held before. -/
def daoFork (oracle : Oracle) : Property IO := propertyM do
  let index ← forAll (Gen.nat (.constant 0 (DAO_ACCOUNTS.length + 1)))
  let funded ← forAll (Gen.list (.linear 0 12)
    (Gen.zip (Gen.nat (.constant 0 (DAO_ACCOUNTS.length - 1))) (Gen.nat (.exponential 0 (2 ^ 80)))))
  let before ← forAll (Gen.nat (.exponential 0 (2 ^ 80)))
  pure do
    let account := match DAO_ACCOUNTS[index]? with
      | some address => hexV address
      | none => "none"
    s!"{account} {DAO_ACCOUNTS.length} {hexV DAO_RECOVERY}" ===
      (← oracle.ask ["dao", toString index])
    let empty : TransactionState := .ofBlock ⟨⟨∅, ∅, ∅⟩, ∅, ∅, ∅, ∅⟩
    let start := (funded.map fun (i, amount) => (DAO_ACCOUNTS.getD i DAO_RECOVERY, amount)) ++
      [(DAO_RECOVERY, before)]
    let .ok state := start.foldlM (fun (state : TransactionState) (address, amount) =>
        state.setAccountBalance .homestead address (.ofNat 256 amount)) empty
      | failWith "the state does not build"
    -- A later balance of the same account replaces the earlier one.
    let held := (List.range DAO_ACCOUNTS.length).map fun i =>
      ((funded.reverse.find? (·.1 == i)).map (·.2)).getD 0
    match applyDaoFork .daoFork state with
    | .error _ => failWith "the fork fails"
    | .ok after =>
      (after.getAccount DAO_RECOVERY).balance.toNat === before + held.sum
      for address in DAO_ACCOUNTS do
        (after.getAccount address).balance.toNat === 0

end ExecutionProperty

namespace ExecutionProperty

/-! ## Ommers -/

/-- The child that follows a parent at a fork, valid as a header, with a mark in its coinbase.

Its difficulty and its base fee are those that EthLib expects, which the reference then judges. -/
def validChild (fork : Fork) (parent : RawHeader) (mark : UInt8) (ommersHash : ByteArray) :
    RawHeader :=
  let parentBytes := enc (parent.item fork)
  let timestamp := parent.timestamp + 13
  let baseFee := match (Codec.decode parentBytes : Except RlpError (Header fork)) with
    | .ok p => expectedBaseFeeAcross p
    | .error _ => 0
  { parent with
    parentHash := ⟨(keccak256 parentBytes).toArray⟩
    ommersHash
    coinbase := bytesOf (List.replicate 20 mark)
    number := parent.number + 1
    timestamp
    gasUsed := 0
    baseFee
    difficulty := blockDifficulty fork (parent.number + 1) timestamp parent.timestamp
      parent.difficulty (parent.ommersHash.data != emptyOmmers.data) }

/-- The hash of a list of ommers: the hash of the list of their headers. -/
def ommersHashOf (fork : Fork) (ommers : List RawHeader) : ByteArray :=
  ⟨(keccak256 (enc (.list (ommers.map (·.item fork))))).toArray⟩

/-- A candidate ommer of the block after a chain of nine blocks, numbered 0 to 8. -/
inductive Pick where
  /-- A fresh child of the block `parent`, which is valid for the parents 2 to 7. -/
  | uncle (parent : Nat) (mark : UInt8)
  /-- The ommer that the block `block` of the chain holds, if it holds one. -/
  | included (block : Nat)
  /-- The block `block` of the chain itself. -/
  | canonical (block : Nat)
  /-- A fresh child of the block `parent` with a difficulty that is one too high. -/
  | bad (parent : Nat) (mark : UInt8)
  deriving Repr

/-- A chain, the ommers of each of its blocks, and candidates for the next block. -/
structure OmmersCase where
  fork : Fork × String
  /-- The blocks of the chain, the oldest first, each with its ommers. -/
  chain : List (RawHeader × List RawHeader)
  /-- The candidates. -/
  picks : List Pick
  /-- Whether the header of the block holds the hash of its ommers. -/
  rightHash : Bool

instance : Repr OmmersCase where
  reprPrec c _ := s!"{c.fork.2} {repr c.picks} hash {c.rightHash} holders \
    {(c.chain.map fun b => b.2.length)}"

/-- A chain of nine blocks where some hold an ommer, and up to three candidates for the next. -/
def genOmmersCase : Gen OmmersCase := do
  let fork ← Gen.element [(Fork.frontier, "frontier"), (.homestead, "homestead"),
    (.byzantium, "byzantium"), (.london, "london"), (.grayGlacier, "gray_glacier")]
  let root ← genRawHeader fork.1
  let root := { root with number := root.number + 1, gasLimit := max root.gasLimit 5000 }
  let holders ← Gen.list (.singleton 9) (Gen.frequency [(2, pure false), (1, pure true)])
  let chain := (List.range 8).foldl (fun (chain : List (RawHeader × List RawHeader)) i =>
      -- The block `i + 1` may hold a sibling of its parent, a child of the block `i - 1`.
      let ommers := if holders.getD i false ∧ 1 ≤ i then
          [validChild fork.1 (chain.getD (i - 1) (root, [])).1 (UInt8.ofNat (100 + i)) emptyOmmers]
        else []
      let hash := if ommers.isEmpty then emptyOmmers else ommersHashOf fork.1 ommers
      chain ++ [(validChild fork.1 (chain.getD i (root, [])).1 0 hash, ommers)])
    [(root, [])]
  let block := Gen.nat (.constant 0 8)
  let mark : Gen UInt8 := Gen.element [1, 2]
  let pick := Gen.frequency [(8, Pick.uncle <$> Gen.nat (.constant 2 7) <*> mark),
    (2, Pick.uncle <$> block <*> mark), (1, Pick.included <$> block),
    (1, Pick.canonical <$> block), (1, Pick.bad <$> Gen.nat (.constant 2 7) <*> mark)]
  let picks ← Gen.frequency [(1, pure []), (6, Gen.list (.constant 1 2) pick),
    (1, Gen.list (.singleton 3) pick)]
  pure ⟨fork, chain, picks, ← Gen.frequency [(9, pure true), (1, pure false)]⟩

/-- The headers that the picks name. -/
def OmmersCase.candidates (c : OmmersCase) : List RawHeader :=
  let header (i : Nat) : RawHeader := (c.chain.getD i (c.chain.headD default)).1
  c.picks.flatMap fun
    | .uncle parent mark => [validChild c.fork.1 (header parent) mark emptyOmmers]
    | .included block => (c.chain.getD block (c.chain.headD default)).2
    | .canonical block => [header block]
    | .bad parent mark =>
      let child := validChild c.fork.1 (header parent) mark emptyOmmers
      [{ child with difficulty := child.difficulty + 1 }]
where
  /-- A header that no case reads. -/
  default : RawHeader × List RawHeader :=
    (⟨.empty, .empty, .empty, .empty, 0, 0, 0, 0, 0, .empty, .empty, 0, 0, 0⟩, [])

open EthLib.Execution.Blocks in
/-- EthLib accepts the ommers of a block exactly when execution-specs does, the seal aside.

The candidates are fresh siblings of recent blocks, mostly valid, and also ommers that a recent
block holds, blocks of the chain, headers with a wrong difficulty, the same header twice, three
headers, siblings of the block itself and ommers that are too old. -/
def ommersValid (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genOmmersCase
  pure do
    let fork := c.fork.1
    let candidates := c.candidates
    let last := (c.chain.getLastD OmmersCase.candidates.default).1
    let hash := if c.rightHash then
        (if candidates.isEmpty then emptyOmmers else ommersHashOf fork candidates)
      else last.roots
    let header := validChild fork last 0 hash
    let word (h : RawHeader) : String := hex (enc (h.item fork))
    let words (hs : List RawHeader) : String :=
      if hs.isEmpty then "-" else ",".intercalate (hs.map word)
    let expected ← oracle.ask (["ommers", c.fork.2, word header, words candidates] ++
      c.chain.map fun (h, ommers) => s!"{word h}:{words ommers}")
    annotate s!"the reference: {expected}"
    let read (h : RawHeader) : Except RlpError (Header fork) := Codec.decode (enc (h.item fork))
    let sigma (h : RawHeader) : Except RlpError ((f : Fork) × Header f) :=
      (fun h => ⟨fork, h⟩) <$> read h
    let decoded : Except RlpError _ := do
      let recent ← c.chain.mapM fun (h, ommers) => do
        pure (⟨fork, ← read h, ← ommers.mapM sigma⟩ : RecentBlock)
      pure (recent, ← read header, ← candidates.mapM sigma)
    match decoded with
    | .error _ => failWith "EthLib does not decode a header"
    | .ok (recent, header, ommers) =>
      -- A chain that activates no fork by number, so that no rule of the DAO Fork applies.
      let config : ChainConfig := ⟨1, Vector.replicate 20 0, [], []⟩
      let result := validateOmmers config false recent header ommers
      annotate s!"EthLib: {repr result}"
      result.isOk === (expected == "ok")

end ExecutionProperty

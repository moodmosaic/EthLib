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

/-- A log: an address, at most four topics, and data.

Each count of topics from 0 to 4 is as common as another.

Half the addresses and topics are any bytes, so that an entry sets any bit of the filter. -/
def genLog : Gen TxLog :=
  let address := Gen.frequency [(1, genAddress), (1, genVector 20)]
  let topic := Gen.frequency [(1, genWord), (1, genVector 32)]
  Execution.Blocks.Log.mk <$> address <*> Gen.list (.constant 0 4) topic <*>
    genBytes (.linear 0 40)

/-- A few logs: none now and then, mostly one to six. -/
def genLogs : Gen (List TxLog) :=
  Gen.frequency [(1, pure []), (2, Gen.list (.singleton 1) genLog),
    (6, Gen.list (.constant 2 6) genLog)]

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
  let logs ← forAllWith (fun logs => " ".intercalate (logs.map logWord)) genLogs
  let other ← forAllWith hex (Gen.frequency [(3, genBytes (.constant 20 32)),
    (if logs.isEmpty then 0 else 1, Gen.element (logs.flatMap Bloom.entries))])
  pure do
    label (if logs.isEmpty then "logs: 0" else if logs.length = 1 then "logs: 1" else "logs: 2+")
    coverMin 13 "a log with no topic" (logs.any (·.topics.isEmpty))
    coverMin 14 "a log with one topic" (logs.any (·.topics.length = 1))
    coverMin 25 "a log with two topics or more" (logs.any (2 ≤ ·.topics.length))
    coverMin 13 "a log with four topics" (logs.any (·.topics.length = 4))
    let entries := (logs.flatMap Bloom.entries).map hex
    let distinct := entries.eraseDups.length
    label (if distinct = 0 then "distinct entries: 0" else if distinct ≤ 3 then
      "distinct entries: 1 to 3" else if distinct ≤ 8 then "distinct entries: 4 to 8"
      else "distinct entries: 9+")
    coverMin 28 "an entry outside the seven fixed ones" (logs.any fun log =>
      (log.address.toList.eraseDups.length > 1) || log.topics.any (·.toList.eraseDups.length > 1))
    coverMin 13 "an entry twice" (distinct < entries.length)
    let expected ← oracle.ask ("bloom" :: logs.map logWord)
    hexV (logsBloom logs) === expected
    for entry in logs.flatMap Bloom.entries do
      ensure (Bloom.mayContain (Bloom.ofLogs logs) entry) "an entry of a log is not in the filter"
    -- Another entry may be in the filter exactly when the bytes of the reference hold its bits.
    --
    -- Bit `k` of the filter is bit `k mod 8` of the byte `255 - k / 8`, as the Yellow Paper says.
    let reference := (unhex? expected).getD .empty
    let digest := keccak256 other
    let bitsOf := [0, 2, 4].map fun i =>
      (digest[i]!.toNat * 256 + digest[i + 1]!.toNat) % 2048
    let held := bitsOf.all fun k =>
      (reference.data.getD (255 - k / 8) 0).toNat / 2 ^ (k % 8) % 2 = 1
    coverMin 7 "another entry: the filter holds its bits" held
    coverMin 26 "another entry: the filter lacks a bit" (!held)
    Bloom.mayContain (Bloom.ofLogs logs) other === held
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
  slotNumber : Nat := 0

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
    ++ (if fork ≥ .pectra then [word] else [])
    ++ (if fork ≥ .glamsterdam then [word, .scalar h.slotNumber] else []))

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
      (1, Gen.nat (.exponential 0 (2 ^ 40)))]
    slotNumber := ← genNatNear 64 [2 ^ 64 - 1, 2 ^ 64] }

/-- What EthLib says of the bytes of a header at a fork, in the words of the oracle. -/
def describeHeader (fork : Fork) (bytes : ByteArray) : String :=
  match (Codec.decode bytes : Except RlpError (Header fork)) with
  | .error _ => "error"
  | .ok h =>
    let since := (if hh : Fork.london ≤ fork then [h.baseFeePerGas hh] else [])
      ++ (if hh : Fork.dencun ≤ fork then
        [(h.blobGasUsed hh).toNat, (h.excessBlobGas hh).toNat] else [])
      ++ (if hh : Fork.glamsterdam ≤ fork then [(h.slotNumber hh).toNat] else [])
    let fields := [h.difficulty, h.number, h.gasLimit, h.gasUsed, h.timestamp.toNat] ++ since
    " ".intercalate (["ok", orError (hexV <$> h.hash)] ++ fields.map toString)

/-- A header as bytes, almost valid, at a fork. -/
def genHeaderBytes (forks : List (Fork × String)) : Gen ((Fork × String) × ByteArray) := do
  let fork ← genForkOf forks
  let header ← genRawHeader fork.1
  let wide ← Gen.frequency [(5, pure header),
    (1, (fun (n : Nat) => { header with blobGasUsed := n }) <$> Gen.element [2 ^ 64 - 1, 2 ^ 64]),
    (1, (fun (n : Nat) => { header with timestamp := n }) <$> Gen.element [2 ^ 256 - 1, 2 ^ 256]),
    (1, (fun (n : Nat) => { header with gasLimit := n, difficulty := n, baseFee := n }) <$>
      Gen.element [2 ^ 64, 2 ^ 256 - 1])]
  let mutations ← Gen.frequency [(2, pure []), (1, Gen.list (.constant 1 2) genMutation)]
  -- Now and then the fields of the next or the previous fork.
  let shape ← Gen.frequency [(8, pure fork.1),
    (1, Gen.element [.london, .shapella, .dencun, .pectra, .grayGlacier, .glamsterdam])]
  pure (fork, enc (mutateAll mutations (wide.item shape)))

/-- EthLib and execution-specs agree on the bytes of a header.

They agree on whether the bytes hold a header of the fork.

Then they agree on its hash and on the numbers that it holds. -/
def headerBytes (oracles : Oracles) : Property IO := propertyM do
  let (fork, bytes) ← forAllWith (fun (fork, bytes) => s!"{fork.1.name} {hex bytes}")
    (genHeaderBytes oracles.forks)
  pure do
    labelFork fork.1
    let count := match decode bytes with
      | .ok (.list items) => some items.length
      | _ => none
    label (match count with
      | none => "form: not a list"
      | some n => if n = Header.fieldCount fork.1 then "form: the count of fields of the fork"
        else if n < Header.fieldCount fork.1 then "form: fewer fields" else "form: more fields")
    match (Codec.decode bytes : Except RlpError (Header fork.1)) with
    | .ok h =>
      label "verdict: a header"
      coverMin 10 "a header with a base fee" (Fork.london ≤ fork.1)
      coverMin 7 "a header with a withdrawals root" (Fork.shapella ≤ fork.1)
      coverMin 5 "a header with blob gas" (Fork.dencun ≤ fork.1)
      coverMin 4 "a header with a requests hash" (Fork.pectra ≤ fork.1)
      coverMin 1 "a header with a block access list hash and a slot" (Fork.glamsterdam ≤ fork.1)
      coverMin 4 "a header with a number of 2^64 or more"
        (2 ^ 64 ≤ h.gasLimit || 2 ^ 64 ≤ h.difficulty || 2 ^ 64 ≤ h.timestamp.toNat)
    | .error error => label s!"verdict: no header, {errorName error}"
    describeHeader fork.1 bytes === (← (oracles.at fork).ask ["header", fork.2, hex bytes])

/-- The one thing wrong with a header after its parent, or nothing. -/
inductive HeaderFault where
  /-- Nothing: the header is valid. -/
  | none
  /-- The gas used is one above the gas limit. -/
  | gasUsedAbove
  /-- The gas limit is the first one too far above the parent's. -/
  | gasLimitUp
  /-- The gas limit is the first one too far below the parent's. -/
  | gasLimitDown
  /-- The gas limit is 4999, one below the least, after a parent at 5001. -/
  | gasLimitFloor
  /-- The base fee is one above the right one. -/
  | baseFeeUp
  /-- The base fee is one below the right one, or 2 where the right one is 0. -/
  | baseFeeDown
  /-- The timestamp is the parent's. -/
  | sameTime
  /-- The timestamp is one before the parent's. -/
  | earlier
  /-- The number is two above the parent's. -/
  | numberUp
  /-- The number is the parent's. -/
  | numberSame
  /-- The number is 0. -/
  | genesis
  /-- The extra data has 33 bytes. -/
  | extraData
  /-- The difficulty is one above the right one. -/
  | difficultyUp
  /-- The difficulty is one below the right one. -/
  | difficultyDown
  /-- The nonce is not zero, from Paris. -/
  | nonce
  /-- The ommers hash is not that of the empty list, from Paris. -/
  | ommersHash
  /-- The parent hash is another hash. -/
  | parentHash
  /-- The excess blob gas is one above the right one. -/
  | excessUp
  /-- The excess blob gas is one below the right one, or 2 where the right one is 0. -/
  | excessDown
  deriving Repr, BEq

/-- The faults that a header at a fork can have, those of the later forks twice. -/
def HeaderFault.at (fork : Fork) : List HeaderFault :=
  [.gasUsedAbove, .gasLimitUp, .gasLimitDown, .gasLimitFloor, .sameTime, .earlier, .numberUp,
    .numberSame, .genesis, .extraData, .parentHash]
  ++ (if fork ≥ .london then [.baseFeeUp, .baseFeeDown, .baseFeeUp, .baseFeeDown] else [])
  ++ (if fork < .paris then [.difficultyUp, .difficultyDown, .difficultyDown]
    else [.difficultyUp, .difficultyUp, .nonce, .ommersHash, .nonce, .ommersHash])
  ++ (if fork ≥ .dencun then [.excessUp, .excessDown, .excessUp, .excessDown, .excessUp,
    .excessDown] else [])

/-- A parent at a fork and a child at a fork, with the one fault of the child. -/
structure HeaderPair where
  /-- The fork of the parent, and its name in the reference. -/
  parentFork : Fork × String
  /-- The fork of the child, and its name in the reference. -/
  fork : Fork × String
  /-- The parent. -/
  parent : RawHeader
  /-- The child. -/
  child : RawHeader
  /-- What is wrong with the child. -/
  fault : HeaderFault

instance : Repr HeaderPair where
  reprPrec c _ := s!"{c.parentFork.1.name} {c.fork.1.name} {reprStr c.fault} \
    {hex (enc (c.parent.item c.parentFork.1))} {hex (enc (c.child.item c.fork.1))}"

/-- A header and a child that follows it, valid or with one fault.

The child takes the base fee, the excess blob gas and the difficulty that EthLib expects of it.

So a rule that EthLib has wrong shows as a valid child that the reference refuses.

A fault moves one field to the first value that its rule refuses, so no fault hides another.

A valid child is also at the edge of each rule:

- Its gas limit is the last one near enough to the parent's, on either side.
- Its gas used is its gas limit.
- Its extra data has 32 bytes.
- It comes one second after its parent.

At the first block of London the gas limit of the parent counts twice, as EIP-1559 says. -/
def genHeaderPairAt (parentFork fork : Fork × String) : Gen HeaderPair := do
  let fault ← Gen.frequency [(3, pure HeaderFault.none), (7, Gen.element (HeaderFault.at fork.1))]
  let parent ← genRawHeader parentFork.1
  let limit := if fault == .gasLimitFloor then 5001 else max parent.gasLimit 6000
  -- The gas that the parent used moves the base fee: below, at and above the target.
  let used ← Gen.frequency [(3, Gen.nat (.constant 0 limit)),
    (3, Gen.element [limit / 2, limit / 2 + 1, limit / 2 - 1, 0, limit])]
  let parent := { parent with gasLimit := limit, gasUsed := used }
  let parentBytes := enc (parent.item parentFork.1)
  -- EIP-1559: the parent of the first London block counts with twice its gas limit.
  let before := if parentFork.1 < .london ∧ fork.1 ≥ .london then 2 * parent.gasLimit
    else parent.gasLimit
  let step := before / 1024
  let gasLimit ← Gen.element [before, before + step - 1, before - step + 1]
  let gasUsed ← Gen.frequency [(4, Gen.nat (.constant 0 gasLimit)), (1, pure gasLimit)]
  let elapsed ← Gen.frequency [(6, Gen.nat (.constant 1 30)), (2, Gen.nat (.constant 1 1200)),
    (2, pure 1)]
  let timestamp := parent.timestamp + elapsed
  let number := parent.number + 1
  let extraData ← Gen.frequency [(3, genBytes (.constant 0 31)), (1, genBytesN 32)]
  -- What EthLib expects of the child, read from the parent as EthLib decodes it.
  let (baseFee, excess, difficulty) :=
    match (Codec.decode parentBytes : Except RlpError (Header parentFork.1)) with
    | .error _ => (0, 0, 0)
    | .ok p =>
      let excess := if hd : Fork.dencun ≤ fork.1 then
          if hl : Fork.london ≤ parentFork.1 then expectedExcessBlobGas hl hd p else 0
        else 0
      (expectedBaseFeeAcross p, excess,
        blockDifficulty fork.1 number timestamp parent.timestamp parent.difficulty
          (parent.ommersHash.data != emptyOmmers.data))
  let valid : RawHeader := {
    parentHash := ⟨(keccak256 parentBytes).toArray⟩
    ommersHash := if fork.1 ≥ .paris then emptyOmmers else parent.roots
    coinbase := parent.coinbase, roots := parent.roots
    difficulty, number, gasLimit, gasUsed, timestamp, extraData
    nonce := if fork.1 ≥ .paris then bytesOf (List.replicate 8 0) else parent.roots.extract 0 8
    baseFee
    blobGasUsed := 131072 * (← Gen.nat (.constant 0 9))
    excessBlobGas := excess
    slotNumber := parent.slotNumber + 1 }
  let child : RawHeader := match fault with
    | .none => valid
    | .gasUsedAbove => { valid with gasUsed := valid.gasLimit + 1 }
    | .gasLimitUp => { valid with gasLimit := before + step, gasUsed := 0 }
    | .gasLimitDown => { valid with gasLimit := before - step, gasUsed := 0 }
    | .gasLimitFloor => { valid with gasLimit := 4999, gasUsed := 0 }
    | .baseFeeUp => { valid with baseFee := baseFee + 1 }
    | .baseFeeDown => { valid with baseFee := if baseFee = 0 then 2 else baseFee - 1 }
    | .sameTime => { valid with timestamp := parent.timestamp }
    | .earlier => { valid with timestamp := parent.timestamp - 1 }
    | .numberUp => { valid with number := number + 1 }
    | .numberSame => { valid with number := parent.number }
    | .genesis => { valid with number := 0 }
    | .extraData => { valid with extraData := bytesOf (List.replicate 33 7) }
    | .difficultyUp => { valid with difficulty := difficulty + 1 }
    | .difficultyDown => { valid with difficulty := difficulty - 1 }
    | .nonce => { valid with nonce := bytesOf (List.replicate 7 0 ++ [1]) }
    | .ommersHash => { valid with ommersHash := parent.roots }
    | .parentHash => { valid with parentHash := parent.roots }
    | .excessUp => { valid with excessBlobGas := excess + 1 }
    | .excessDown => { valid with excessBlobGas := if excess = 0 then 2 else excess - 1 }
  pure ⟨parentFork, fork, parent, child, fault⟩

/-- The labels of a header after its parent: its fork, its fault, and what EthLib says of it. -/
def labelHeaderPair (c : HeaderPair)
    (result : Except BlockError Unit) : TestT IO Unit := do
  labelFork c.fork.1
  label s!"fault: {(((reprStr c.fault).splitOn " ").headD "").splitOn "." |>.getLastD ""}"
  label (match result with
    | .ok _ => "verdict: valid"
    | .error error => s!"verdict: invalid, {errorName error}")
  coverMin 1 "valid, before London" (result.isOk && c.fork.1 < .london)
  classify "valid, London to Gray Glacier" (result.isOk && c.fork.1 ≥ .london && c.fork.1 < .paris)
  coverMin 1 "valid, Paris and Shapella" (result.isOk && c.fork.1 ≥ .paris && c.fork.1 < .dencun)
  coverMin 2 "valid, from Dencun" (result.isOk && c.fork.1 ≥ .dencun)
  let before := if c.parentFork.1 < .london ∧ c.fork.1 ≥ .london then 2 * c.parent.gasLimit
    else c.parent.gasLimit
  coverMin 3 "valid, the gas limit as far above the parent's as it may be"
    (result.isOk && c.child.gasLimit > before)
  coverMin 3 "valid, the gas limit as far below the parent's as it may be"
    (result.isOk && c.child.gasLimit < before)
  coverMin 2 "valid, the gas used is the gas limit"
    (result.isOk && c.child.gasUsed = c.child.gasLimit)
  coverMin 2 "valid, extra data of 32 bytes" (result.isOk && c.child.extraData.size = 32)
  coverMin 2 "valid, one second after the parent"
    (result.isOk && c.child.timestamp = c.parent.timestamp + 1)
  label (if c.parent.gasUsed = c.parent.gasLimit / 2 then "parent gas: at the target"
    else if c.parent.gasUsed > c.parent.gasLimit / 2 then "parent gas: above the target"
    else "parent gas: below the target")
  coverMin 6 "the excess blob gas that EthLib expects is not zero"
    (c.fork.1 ≥ .dencun && 0 < c.child.excessBlobGas)

/-- What EthLib says of a header after its parent, or none where a header does not decode. -/
def checkPair (c : HeaderPair) : Option (Except BlockError Unit) :=
  if h : c.parentFork.1 ≤ c.fork.1 then
    let decoded : Except RlpError (Header c.parentFork.1 × Header c.fork.1) := do
      pure (← Codec.decode (enc (c.parent.item c.parentFork.1)),
        ← Codec.decode (enc (c.child.item c.fork.1)))
    match decoded with
    | .error _ => none
    | .ok (p, child) => some (checkHeader h p child)
  else none

/-- EthLib accepts a header after its parent exactly when execution-specs does, the seal aside.

The two headers are at the same fork.

A child is valid, or has one fault: each rule is met alone, at the first value that it refuses. -/
def headerAfterParent (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll (do
    let fork ← genFork
    genHeaderPairAt fork fork)
  pure do
    let expected ← oracle.ask ["headerpair", c.fork.2, hex (enc (c.parent.item c.fork.1)),
      hex (enc (c.child.item c.fork.1))]
    annotate s!"the reference: {expected}"
    match checkPair c with
    | none => failWith "EthLib does not decode a header"
    | some result =>
      annotate s!"EthLib: {repr result}"
      labelHeaderPair c result
      result.isOk === (expected == "ok")
      -- A valid header is accepted, and a header with a fault refused.
      result.isOk === (c.fault == .none)

/-- The index of a fork of the reference in its order of forks. -/
def referenceIndex (name : String) : Nat :=
  (eelsForks.findIdx? (·.2 == name)).getD 0

/-- A fork and the fork of its parent: the fork before it, or the same rules under another name.

The reference defines a header after a parent of the fork just before, and no further back. -/
def genForkStep : Gen ((Fork × String) × (Fork × String)) :=
  let steps := releaseForks.flatMap fun fork =>
    (releaseForks.filter fun parent =>
      parent.1 < fork.1 ∧ referenceIndex parent.2 + 1 ≥ referenceIndex fork.2).map (·, fork)
  let first (since : Fork) := steps.filter fun (parent, fork) => parent.1 < since ∧ fork.1 ≥ since
  -- The steps into London, Paris and Dencun change a rule, so they come as often as the rest.
  Gen.frequency [(3, Gen.element steps), (1, Gen.element (first .london)),
    (1, Gen.element (first .paris)), (1, Gen.element (first .dencun)),
    (1, Gen.element (steps.filter fun (parent, _) => parent.1 ≥ .dencun))]

/-- EthLib accepts the first header of a fork after its parent as the sources say.

The parent is at the fork before, so the child is the first block of its fork.

- At London the parent has no base fee: the child takes the initial one.
  The gas limit of the parent counts twice.
- At Dencun the parent has no blob gas, which counts as zero.
- From Pectra the excess blob gas reads the blob gas of the parent, at the target of the child.
- Before Paris the difficulty follows the rule of the child.

The reference is `validate_header` of the fork of the child, in execution-specs.

Two rules are added to it from the EIPs, as the oracle says:

- The gas limit at the first London block, which execution-specs does not check.
- The blob gas of a parent from Dencun on, which execution-specs reads as zero at a new fork. -/
def headerAcrossForks (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll (do
    let (parentFork, fork) ← genForkStep
    genHeaderPairAt parentFork fork)
  pure do
    let expected ← oracle.ask ["headeracross", c.parentFork.2, c.fork.2,
      hex (enc (c.parent.item c.parentFork.1)), hex (enc (c.child.item c.fork.1))]
    annotate s!"the reference: {expected}"
    match checkPair c with
    | none => failWith "EthLib does not decode a header"
    | some result =>
      annotate s!"EthLib: {repr result}"
      labelHeaderPair c result
      label s!"step: {c.parentFork.2} to {c.fork.2}"
      coverMin 1 "the two forks have one name in the reference" (c.parentFork.2 == c.fork.2)
      coverMin 5 "the first block of London" (c.parentFork.1 < .london && c.fork.1 ≥ .london)
      coverMin 5 "the first block of Paris" (c.parentFork.1 < .paris && c.fork.1 ≥ .paris)
      coverMin 5 "the first block of Dencun" (c.parentFork.1 < .dencun && c.fork.1 ≥ .dencun)
      coverMin 6 "the first block of a fork after Dencun"
        (c.parentFork.1 ≥ .dencun && c.parentFork.2 != c.fork.2)
      result.isOk === (expected == "ok")
      result.isOk === (c.fault == .none)

/-! ## Receipts -/

/-- A receipt as bytes at a fork: its type byte, or none, and its almost valid fields. -/
def genReceiptBytes (forks : List (Fork × String)) : Gen ((Fork × String) × ByteArray) := do
  let fork ← genForkOf forks
  let outcome ← Gen.frequency [
    (if fork.1 ≥ .byzantium then 6 else 1, Item.scalar <$> Gen.element [0, 1]),
    (if fork.1 ≥ .byzantium then 1 else 6, Item.bytes <$> genBytesN 32),
    (1, Item.scalar <$> Gen.element [2, 255, 256])]
  let gas ← Item.scalar <$> genNatNear 64 [2 ^ 64, 2 ^ 256]
  let logs ← Gen.frequency [(1, pure []), (3, Gen.list (.constant 1 3) genLog)]
  let bloomBytes ← Gen.frequency [(8, pure ⟨(logsBloom logs).toArray⟩), (1, genBytesN 255)]
  let item := Item.list [outcome, gas, .bytes bloomBytes, .list (logs.map logItem)]
  let mutations ← Gen.frequency [(3, pure []), (1, Gen.list (.constant 1 2) genMutation)]
  let types := (List.range 5).filter fun type =>
    type = 0 ∨ (Execution.Transactions.typeFork (UInt8.ofNat type)).any (· ≤ fork.1)
  let type ← Gen.frequency [(8, Gen.element types.reverse), (1, Gen.nat (.constant 0 5)),
    (1, Gen.element [5, 0x7f, 0x80, 0xbf])]
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

They agree on whether the bytes hold a receipt of the fork.

Then they agree on its type, its outcome, its gas, its logs and the hash of its fields. -/
def receiptBytes (oracles : Oracles) : Property IO := propertyM do
  let (fork, bytes) ← forAllWith (fun (fork, bytes) => s!"{fork.1.name} {hex bytes}")
    (genReceiptBytes oracles.forks)
  pure do
    labelFork fork.1
    let first := bytes.data.getD 0 0
    label (if bytes.isEmpty then "form: no byte" else if 0xc0 ≤ first then "form: legacy"
      else if 1 ≤ first ∧ first ≤ 4 then s!"form: type {first}" else "form: another first byte")
    match decodeReceipt fork.1 bytes with
    | .ok (_, r) =>
      label (match r.outcome with
        | .postState _ _ => "verdict: a receipt with a state root"
        | .status _ succeeded =>
          if succeeded then "verdict: a receipt with status 1"
          else "verdict: a receipt with status 0")
      label (if r.logs.isEmpty then "logs: 0" else if r.logs.length = 1 then "logs: 1"
        else "logs: 2+")
      coverMin 10 "a log with a topic" (r.logs.any (!·.topics.isEmpty))
    | .error (.decoding error) => label s!"verdict: no receipt, {errorName error}"
    | .error error => label s!"verdict: no receipt, {errorName error}"
    describeReceipt fork.1 bytes === (← (oracles.at fork).ask ["receipt", fork.2, hex bytes])
    -- The bytes that EthLib writes for a receipt that it read are the bytes that it read.
    if let .ok (type, r) := decodeReceipt fork.1 bytes then
      orError (hex <$> encodeReceipt type r) === hex bytes

/-- The receipts of a block count its gas so far, and each holds its outcome and its logs.

The outcome is the state root before Byzantium, and the status from it, at every fork.

The gas of a receipt is the gas before the list, and that of each transaction up to its own.

The model is a sum in `Nat`. -/
def receiptsOfBlock : Property IO := propertyM do
  let fork ← forAllWith (·.1.name) (genForkOf (releaseForks ++ lateForks))
  let results ← forAllWith
    (fun rs => toString (rs.map fun (r : Bool × Nat × List TxLog) => (r.1, r.2.1, r.2.2.length)))
    (Gen.frequency [(1, pure []), (9, Gen.list (.constant 1 5) (Gen.zip Gen.bool
      (Gen.zip (Gen.nat (.exponential 0 (2 ^ 40))) (Gen.list (.constant 0 2) genLog))))])
  let start ← forAll (Gen.frequency [(1, pure 0), (1, Gen.nat (.exponential 0 (2 ^ 40)))])
  pure do
    let stateRoot : Hash32 := Vector.replicate 32 7
    let inputs := results.map fun (succeeded, gas, logs) =>
      (Outcome.make fork.1 succeeded fun _ => stateRoot, gas, logs)
    let receipts := makeReceiptsFrom (fork := fork.1) start inputs
    coverMin 7 "a state root, before Byzantium" (fork.1 < .byzantium && !results.isEmpty)
    coverMin 22 "a status, from Byzantium" (fork.1 ≥ .byzantium && !results.isEmpty)
    coverMin 3 "no transaction" results.isEmpty
    coverMin 23 "two transactions or more" (2 ≤ results.length)
    coverMin 14 "gas before the list" (0 < start && !results.isEmpty)
    receipts.length === results.length
    for (receipt, i) in receipts.zipIdx do
      let (succeeded, _, logs) := results.getD i (false, 0, [])
      receipt.cumulativeGasUsed === start + ((results.take (i + 1)).map (·.2.1)).sum
      hexV receipt.bloom === hexV (logsBloom logs)
      receipt.logs.length === logs.length
      (match receipt.outcome with
        | .postState _ root => s!"root {hexV root}"
        | .status _ status => s!"status {status}") ===
        (if fork.1 < .byzantium then s!"root {hexV stateRoot}" else s!"status {succeeded}")
    if start = 0 then
      (makeReceipts (fork := fork.1) inputs).map (·.cumulativeGasUsed) ===
        receipts.map (·.cumulativeGasUsed)

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

/-- The delay of the bomb at a fork, from the EIPs: 649, 1234, 2384, 3554, 4345 and 5133. -/
def delayOf (fork : Fork) : Nat :=
  if fork < .byzantium then 0 else if fork < .constantinople then 3000000
  else if fork < .muirGlacier then 5000000 else if fork < .london then 9000000
  else if fork < .arrowGlacier then 9700000 else if fork < .grayGlacier then 10700000
  else 11400000

/-- Inputs around each period of the bomb, each delay, each step of the time, and the minimum.

The number is mostly near a period of the bomb of the fork:

- Below the delay of the fork.
- In the first two periods, where the bomb is zero.
- At the third period, where the bomb is one.
- Far above.

The time since the parent is near each step of the factor: 9 and 10 seconds, 13, and the least.

The parent's difficulty is near the minimum, where the result is the minimum or just above. -/
def genDifficultyCase : Gen DifficultyCase := do
  -- Each fork as often as another: each has its delay of the bomb.
  let fork ← Gen.element (releaseForks.filter fun fork => fork.1 < .paris)
  let delay ← Gen.frequency [(3, pure (delayOf fork.1)),
    (1, Gen.element [0, 3000000, 5000000, 9000000, 9700000, 10700000, 11400000])]
  let number ← Gen.frequency [
    (5, (fun (period : Nat) (d : Nat) => delay + period * 100000 + d - 2) <$>
      Gen.frequency [(3, Gen.element [0, 1, 2, 3]), (2, Gen.nat (.constant 4 60))] <*>
      Gen.nat (.constant 0 4)),
    (1, Gen.nat (.exponential 0 30000000))]
  let elapsed ← Gen.frequency [(3, Gen.nat (.constant 1 20)), (3, Gen.nat (.constant 0 100)),
    (2, Gen.nat (.constant 880 1010)), (1, Gen.nat (.exponential 0 (2 ^ 32)))]
  let parentDifficulty ← Gen.frequency [(2, Gen.nat (.constant 131072 135168)),
    (2, (fun (k : Nat) (d : Nat) => 131072 + 64 * k + d - 1) <$> Gen.nat (.constant 0 8) <*>
      Gen.nat (.constant 0 2)),
    (3, Gen.nat (.exponential 131072 (2 ^ 80))), (1, Gen.element [2 ^ 64 - 1, 2 ^ 64, 2 ^ 128])]
  let parentTimestamp ← Gen.nat (.exponential 0 (2 ^ 40))
  -- One case in eight lands on the minimum.
  --
  -- The parent is `64 k` above it, with no bomb, and the time gives the factor `-k`.
  let k ← Gen.nat (.constant 1 8)
  let late ← if fork.1 < .homestead then Gen.nat (.constant 13 100)
    else if fork.1 < .byzantium then (10 * (k + 1) + ·) <$> Gen.nat (.constant 0 9)
    else (9 * (k + 1) + ·) <$> Gen.nat (.constant 0 8)
  let onMinimum : DifficultyCase := ⟨fork, 1, late, parentTimestamp,
    131072 + 64 * (if fork.1 < .homestead then 1 else k), false⟩
  Gen.frequency [(7, pure ⟨fork, number, elapsed, parentTimestamp, parentDifficulty, ← Gen.bool⟩),
    (1, pure onMinimum)]

/-- The difficulty of a block is the one of execution-specs, at every fork before Paris. -/
def difficulty (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genDifficultyCase
  pure do
    let timestamp := c.parentTimestamp + c.elapsed
    let fork := c.fork.1
    label (if fork < .homestead then "rule: Frontier" else if fork < .byzantium then
      "rule: Homestead to Spurious Dragon" else "rule: Byzantium on")
    label s!"bomb delay: {bombDelay fork}"
    let factor := timeFactor fork timestamp c.parentTimestamp c.parentHasOmmers
    label (if factor = -99 then "time factor: -99, the least" else if factor < 0 then
      "time factor: below 0" else if factor = 0 then "time factor: 0" else if factor = 1 then
      "time factor: 1" else "time factor: 2")
    coverMin 10 "the parent has ommers, from Byzantium" (c.parentHasOmmers && fork ≥ .byzantium)
    let periods := (c.number - bombDelay fork) / 100000
    label (if c.number < bombDelay fork then "bomb: the number is below the delay"
      else if periods < 2 then "bomb: none, in the first two periods"
      else if periods = 2 then "bomb: 1, the third period" else "bomb: 2 or more")
    let step : Int := c.parentDifficulty / 2048
    let raw : Int := c.parentDifficulty + step * factor + bomb fork c.number
    label (if raw < 131072 then "result: the minimum, by the rule" else if raw = 131072 then
      "result: exactly the minimum" else "result: above the minimum")
    classify "elapsed: 0 seconds" (c.elapsed = 0)
    let expected ← oracle.ask ["difficulty", c.fork.2, toString c.number, toString timestamp,
      toString c.parentTimestamp, toString c.parentDifficulty, toString c.parentHasOmmers]
    toString (blockDifficulty c.fork.1 c.number timestamp c.parentTimestamp c.parentDifficulty
      c.parentHasOmmers) === expected
    -- From Paris on the difficulty is zero, at every fork.
    for later in (releaseForks ++ lateForks).filter fun later => later.1 ≥ .paris do
      blockDifficulty later.1 c.number timestamp c.parentTimestamp c.parentDifficulty
        c.parentHasOmmers === 0

/-- The rewards of a block are those of execution-specs, and none from Paris.

The block reward is the constant of the fork there.

The reward of a beneficiary and of an ommer follow the Yellow Paper, 11.3, in `Nat`. -/
def rewards (oracle : Oracle) : Property IO := propertyM do
  -- Each fork as often as another: Byzantium alone has its reward.
  let fork ← forAllWith (·.1.name) (Gen.element (releaseForks.filter fun fork => fork.1 < .paris))
  let ommers ← forAll (Gen.nat (.constant 0 2))
  let age ← forAll (Gen.nat (.constant 1 7))
  pure do
    label s!"reward: {blockReward fork.1 / 10 ^ 18} ether"
    label s!"ommers: {ommers}"
    label s!"age: {age}"
    let expected ← oracle.ask ["reward", fork.2]
    let some reward := expected.toNat? | failWith expected
    blockReward fork.1 === reward
    minerReward fork.1 ommers === reward + ommers * (reward / 32)
    ommerReward fork.1 age === (8 - age) * reward / 8

/-! ## Requests, deposits and roots -/

/-- The requests hash is the one of EIP-7685: a request of its type alone is left out. -/
def requestsHashOf (oracle : Oracle) : Property IO := propertyM do
  let requests ← forAllWith (fun rs => " ".intercalate (rs.map hex))
    (Gen.frequency [(1, pure []), (9, Gen.list (.constant 1 5)
      (Gen.frequency [(3, genBytes (.linear 0 40)), (2, genBytes (.constant 0 2))]))])
  pure do
    label (if requests.isEmpty then "requests: 0" else if requests.length = 1 then "requests: 1"
      else "requests: 2+")
    coverMin 12 "a request of no byte" (requests.any (·.size = 0))
    coverMin 12 "a request of its type alone" (requests.any (·.size = 1))
    coverMin 13 "a request of two bytes" (requests.any (·.size = 2))
    coverMin 21 "a request with data" (requests.any (2 < ·.size))
    coverMin 4 "every request is left out" (!requests.isEmpty && requests.all (·.size ≤ 1))
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
    label (match depositRequestOfEvent data with
      | .ok _ => "verdict: a deposit request"
      | .error error => s!"verdict: no request, {errorName error}")
    label (if data.size < 576 then "size: below 576" else if data.size = 576 then "size: 576"
      else "size: above 576")
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
    (Gen.frequency [(4, Gen.list (.linear 0 20) (Gen.frequency [(2, genBytes (.constant 1 31)),
        (1, genBytes (.constant 32 40))])),
      (1, Gen.list (.constant 126 131) (genBytes (.constant 1 3))),
      -- From the index 256 on, the key of an item has three bytes.
      (1, Gen.list (.constant 254 259) (genBytes (.constant 1 3)))])
  pure do
    let size (n : Nat) : String := if n = 0 then "0" else if n = 1 then "1" else if n ≤ 16 then
      "2 to 16" else if n ≤ 127 then "17 to 127" else if n ≤ 128 then "128" else if n ≤ 256 then
      "129 to 256" else "257+"
    label s!"withdrawals: {size withdrawals.length}"
    label s!"values: {size values.length}"
    coverMin 13 "a value of 32 bytes or more" (values.any (32 ≤ ·.size))
    coverMin 15 "every value is below 32 bytes" (!values.isEmpty && values.all (·.size < 32))
    let words := withdrawals.map fun w =>
      s!"{w.index.toNat}:{w.validatorIndex.toNat}:{hexV w.address}:{w.amount.toNat}"
    orError (hexV <$> withdrawalsRoot withdrawals) === (← oracle.ask ("withdrawalsroot" :: words))
    for w in withdrawals.take 3 do
      ((Codec.encode w).toOption.bind fun bytes =>
        (Codec.decode bytes : Except RlpError Withdrawal).toOption) === some w
    orError (hexV <$> indexedRoot values) === (← oracle.ask ("indexroot" :: values.map hex))

end ExecutionProperty

namespace ExecutionProperty

open EthLib.Execution.State in
/-- The DAO Fork moves the ether of the accounts of EIP-779 to its recovery contract.

Each account of the list and the length of the list are those of execution-specs.

So is the recovery contract.

After the fork an account of the list holds nothing.

The recovery contract then holds what the accounts held, with what it held before. -/
def daoFork (oracle : Oracle) : Property IO := propertyM do
  let index ← forAll (Gen.frequency [(9, Gen.nat (.constant 0 (DAO_ACCOUNTS.length - 1))),
    (1, Gen.element [DAO_ACCOUNTS.length, DAO_ACCOUNTS.length + 1])])
  let funded ← forAll (Gen.list (.linear 0 12)
    (Gen.zip (Gen.nat (.constant 0 (DAO_ACCOUNTS.length - 1))) (Gen.nat (.exponential 0 (2 ^ 80)))))
  let before ← forAll (Gen.nat (.exponential 0 (2 ^ 80)))
  pure do
    label (if index < DAO_ACCOUNTS.length then "index: in the list" else "index: past the list")
    label (if funded.isEmpty then "funded accounts: 0" else if funded.length = 1 then
      "funded accounts: 1" else "funded accounts: 2+")
    coverMin 1 "an account funded twice"
      ((funded.map Prod.fst).eraseDups.length < funded.length)
    coverMin 32 "the recovery contract holds ether before" (0 < before)
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
  let fork ← genWorkFork
  let root ← genRawHeader fork.1
  let root := { root with number := root.number + 1, gasLimit := max root.gasLimit 5000 }
  let holders ← Gen.list (.singleton 9) (Gen.frequency [(1, pure false), (1, pure true)])
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
  let fresh := Pick.uncle <$> Gen.nat (.constant 2 7) <*> mark
  let pick := Gen.frequency [(8, fresh),
    (3, Pick.uncle <$> Gen.element [0, 1, 8] <*> mark), (2, Pick.included <$> block),
    (1, Pick.canonical <$> block), (1, pure (Pick.canonical 0)),
    (1, Pick.bad <$> Gen.nat (.constant 2 7) <*> mark)]
  let picks ← Gen.frequency [(1, pure []), (6, Gen.list (.constant 1 2) pick),
    (1, Gen.list (.singleton 3) pick),
    -- The same ommer twice.
    (1, (fun p => [p, p]) <$> fresh)]
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
    (⟨.empty, .empty, .empty, .empty, 0, 0, 0, 0, 0, .empty, .empty, 0, 0, 0, 0⟩, [])

open EthLib.Execution.Blocks in
/-- EthLib accepts the ommers of a block exactly when execution-specs does, the seal aside.

The candidates are fresh siblings of recent blocks, mostly valid.

The other candidates are:

- Ommers that a recent block holds.
- Blocks of the chain.
- Headers with a wrong difficulty.
- The same header twice.
- Three headers.
- Siblings of the block itself.
- Ommers that are too old. -/
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
      labelFork c.fork.1
      label s!"ommers: {ommers.length}"
      label (match result with
        | .ok _ => "verdict: valid"
        | .error (.invalidHeader error) => s!"verdict: invalid header, {errorName error}"
        | .error error => s!"verdict: invalid, {errorName error}")
      coverMin 7 "valid, with an ommer" (result.isOk && !ommers.isEmpty)
      coverMin 1 "valid, with two ommers" (result.isOk && ommers.length = 2)
      for pick in c.picks do
        label (match pick with
          | .uncle parent _ => if 2 ≤ parent ∧ parent ≤ 7 then "pick: a fresh ommer in range"
            else "pick: a fresh ommer out of range"
          | .included _ => "pick: an ommer of a recent block"
          | .canonical _ => "pick: a block of the chain"
          | .bad _ _ => "pick: a wrong difficulty")
      result.isOk === (expected == "ok")

end ExecutionProperty

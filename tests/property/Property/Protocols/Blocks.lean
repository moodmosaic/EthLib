import Property.Protocols.Transition

/-!
# Whole blocks: every field filled, several operations, a signature and an execution layer

The earlier driver built blocks whose payload was zero but for the fields that validity fixes.

Such a block does not tell a header of the payload that drops or swaps a field from a right one.

It also ran one operation per block, and an execution layer that accepts everything.

Here the oracle fills every field from a seed, puts several operations in one block, and signs it.

The execution layer of both sides answers from a digest of the request that it is given.

So a request with a wrong versioned hash, parent root or list of requests gets another answer.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ProtocolsProperty

variable {preset : Preset} {fork : Fork}

/-- What the test execution layer hashes of a request: every part that a fork passes.

`engine_digest` of `oracle/protocols_blocks.py` is the same function. -/
def engineDigest (request : NewPayloadRequest preset fork) : Except Err ByteArray := do
  let root ← SszType.hashTreeRoot request.executionPayload
  let deneb : ByteArray :=
    if h : .dencun ≤ fork then
      (request.versionedHashes h).data.foldl (fun acc hash => acc ++ ⟨hash.toArray⟩)
        ByteArray.empty ++ ⟨(request.parentBeaconBlockRoot h).toArray⟩
    else ByteArray.empty
  let lists ← request.requestsList
  let electra : ByteArray :=
    if h : .pectra ≤ fork then (lists h).foldl (· ++ ·) ByteArray.empty else ByteArray.empty
  return Cryptography.Hash.sha256 (⟨root.toArray⟩ ++ deneb ++ electra)

/-- An execution layer by its mode: 0 accepts, 1 refuses, 2 answers from the digest. -/
def engineOf (mode : UInt64) : ExecutionEngine preset fork :=
  if mode = 2 then
    { isValidBlockHash := fun _ _ _ => true
      isValidVersionedHashes := fun _ => true
      notifyNewPayload := fun _ _ _ => true
      verifyAndNotifyNewPayload := fun request => do
        return (← engineDigest request)[0]! % 4 != 0 }
  else .constant (mode = 0)

/-- The numbers of a block of either kind, in one word.

The first ten are those of a block before Gloas, the last five those that Gloas adds. -/
def genBlockNumbers : Gen String :=
  (fun fields => ",".intercalate fields) <$> genFields [
    num (Gen.frequency [(19, pure 0), (1, pure 1)]),
    num (Gen.frequency [(19, pure 0), (1, pure 1)]),
    num (Gen.frequency [(19, pure 1), (1, pure 0)]),
    num (Gen.frequency [(19, pure 1), (1, pure 0)]),
    num (Gen.frequency [(12, pure 0), (1, Gen.nat (.constant 1 3))]),
    num (Gen.frequency [(4, Gen.nat (.linear 0 6)), (1, Gen.element [9, 10, 12, 13, 21, 22])]),
    num (Gen.nat (.linear 0 3)), num (Gen.nat (.linear 0 60)),
    num (Gen.frequency [(19, pure 1), (1, pure 0)]),
    num (Gen.frequency [(6, pure 0), (1, pure 1)]),
    num (Gen.frequency [(4, pure 0), (4, pure 1), (1, pure 2), (1, pure 3)]),
    num (Gen.nat (.constant 0 4)),
    num (Gen.frequency [(19, pure 0), (1, pure 1)]),
    num (Gen.frequency [(2, pure 0), (3, pure 1), (2, pure 2), (1, Gen.element [4, 5])]),
    num (Gen.frequency [(12, pure 1), (1, pure 0), (1, pure 2), (1, pure 3)])]

/-- The number of operations of one kind: none or a few, rarely more than a block may hold. -/
def genCount : Gen String :=
  num (Gen.frequency [(5, pure 0), (5, Gen.nat (.linear 0 3)), (1, Gen.nat (.linear 0 20))])

/-- The counts of a block: its operations, its transactions, a seed, and the execution layer. -/
def genCounts : Gen String :=
  (fun fields => ",".intercalate fields) <$> genFields [
    genCount, genCount, genCount, genCount, genCount, genCount, genCount, genCount, genCount,
    num (Gen.nat (.linear 0 6)), num (Gen.nat (.linear 0 1000)),
    num (Gen.frequency [(5, pure 2), (2, pure 0), (1, pure 1)])]

/-- The mode of the execution layer among the counts. -/
def modeOf (words : List String) : UInt64 :=
  (((words.getD 1 "").splitOn ",").getD 11 "0").toNat!.toUInt64

/-- A signed block: how many slots ahead, its signature, its state root, and whether to check. -/
def genSigned (shape : Shape) : Gen String :=
  (fun fields => ",".intercalate fields) <$> genFields [
    num (Gen.frequency [(8, Gen.nat (.linear 1 3)), (4, Gen.nat (.linear 1 (2 * shape.slots))),
      (2, pure shape.slots), (1, pure 0)]),
    num (Gen.frequency [(9, pure 1), (1, pure 0)]),
    num (Gen.frequency [(9, pure 1), (1, pure 0)]),
    num (Gen.frequency [(5, pure 1), (1, pure 0)])]

/-- The calls on a whole block. -/
def wholeBlocks (world : World) (checks : SignatureChecks) : List (Call world.preset) :=
  let shape := world.shape
  let config := world.config
  let block := Gen.sequence [genBlockNumbers, genCounts] 2
  [⟨"process_block_full", allForks, block, fun fork s words bytes =>
      withArgument (BeaconBlock world.preset fork) bytes fun block =>
        .ofState (processBlock config checks (engineOf (modeOf words)) s block)⟩,
    ⟨"process_operations", allForks, block, fun fork s _ bytes =>
      withArgument (BeaconBlockBody world.preset fork) bytes fun body =>
        .ofState (processOperations config checks s body s.latestBlockHeader.slot)⟩,
    ⟨"process_execution_payload", (forksFrom .bellatrix).filter (·.2 < .glamsterdam), block,
      fun fork s words bytes =>
      if h : .bellatrix ≤ fork ∧ fork < .glamsterdam then
        withArgument (BeaconBlockBody world.preset fork) bytes fun body =>
          .ofState (processExecutionPayload config (engineOf (modeOf words)) s body h)
      else .absent⟩,
    ⟨"state_transition", allForks, Gen.sequence [genBlockNumbers, genCounts, genSigned shape] 3,
      fun fork s words bytes =>
      withArgument (SignedBeaconBlock world.preset fork) bytes fun signed =>
        let validate := (((words.getD 2 "").splitOn ",").getD 3 "1") != "0"
        .ofState (stateTransition config checks (engineOf (modeOf words)) s signed validate)⟩]

/-- A state that a whole block is likely to fit: settled validators, and little that is pending.

A block is refused when any of its parts is, so a state of `genOperationState` refuses most. -/
def genBlockState (shape : Shape) : Gen (List String) :=
  Gen.frequency [
    (3, do
      let slot ← genLateSlot shape
      let count ← Gen.frequency [(5, Gen.nat (.constant 8 24)),
        (1, Gen.nat (.constant shape.crowd (shape.crowd + 8)))]
      let registry ← Gen.list (.singleton count) (genSettledValidator shape)
      let rest ← genFields [
        (fun n => s!"bits={n}") <$> Gen.nat (.constant 0 15),
        (fun n => s!"fin=c-{n}") <$> Gen.nat (.linear 1 4),
        (fun n => s!"pj=c-{n}") <$> Gen.nat (.linear 1 3),
        (fun n => s!"cj=c-{n}") <$> Gen.nat (.linear 0 2),
        (fun a b => s!"wd={a},{b}") <$> Gen.nat (.linear 0 50) <*> Gen.nat (.linear 0 (count - 1)),
        (fun n => s!"sync={n}") <$> Gen.frequency [(1, pure 0), (1, pure 1)],
        pure "drsi=0", pure "lookahead", pure "ptc"]
      let builders ← Gen.list (.linear 0 3) (genBuilder shape)
      pure (s!"slot={slot}" :: registry ++ rest ++ builders)),
    (1, genOperationState shape)]

/-- A state with the fields filled that the other words leave at their default.

Some have two validators of one key. -/
def filled (genWords : Shape → Gen (List String)) (shape : Shape) : Gen (List String) := do
  let words ← genWords shape
  let fill ← Gen.frequency [(1, pure []),
    (4, (fun n => [s!"fill={n}"]) <$> Gen.nat (.linear 0 999))]
  let twins ← Gen.frequency [(5, pure []),
    (1, (fun a b => [s!"dup={a},{b}"]) <$> Gen.nat (.linear 0 12) <*> Gen.nat (.linear 0 12))]
  let window ← Gen.frequency [(1, pure []), (1, pure ["ptc"])]
  pure (words ++ fill ++ twins ++ window)

end ProtocolsProperty

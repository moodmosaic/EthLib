import Property.Consensus.State
import EthLib.Consensus.Transition.Upgrade

/-!
# Operations, mutators and accessors on a state

Each call takes a state and an argument that the oracle builds from a few numbers: an exit of
validator 3 signed or not, an attestation of a committee with one bit too many.
EthLib must refuse what consensus-specs refuses and reach the same state otherwise.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ConsensusProperty

/-- A call on a state: its name in consensus-specs, its forks, its argument and EthLib's. -/
structure Call where
  /-- The name of the function in consensus-specs. -/
  name : String
  /-- The forks that have the call. -/
  forks : List (String × Fork)
  /-- The words of the argument. -/
  arguments : Gen (List String)
  /-- EthLib's function, given the state, the words and the SSZ bytes of the argument. -/
  run : (fork : Fork) → State fork → List String → ByteArray → Outcome fork

/-- The numbers of the first word of an argument. -/
def firstNumbers {fork : Fork} (state : State fork) (words : List String) : List UInt64 :=
  numbersOf state (words.headD "")

/-- One word of numbers from generators of each. -/
def genWord (gens : List (Gen String)) : Gen (List String) :=
  (fun fields => [",".intercalate fields]) <$> genFields gens

/-- A number as a word field. -/
def num (gen : Gen Nat) : Gen String := toString <$> gen

/-- A flag that is mostly set: whether a signature is valid, a root right. -/
def genOk : Gen String := num (Gen.frequency [(5, pure 1), (1, pure 0)])

/-- An epoch of an operation: mostly the current one. -/
def genOperationEpoch : Gen String :=
  Gen.frequency [(4, pure "c-0"), (2, genNear), (1, pure "0"), (1, pure (toString far))]

/-- A list of validator indices as one word, sorted or not, with or without repeats. -/
def genIndices : Gen String :=
  (fun xs => ",".intercalate (xs.map toString)) <$>
    Gen.list (.linear 0 6) (Gen.frequency [(8, Gen.nat (.linear 0 6)), (1, genIndex)])

/-- The 64-bit amounts of a request: none, a few increments, or anything. -/
def genAmount : Gen Nat :=
  Gen.frequency [(3, pure 0), (3, (· * increment) <$> Gen.nat (.linear 0 5)), (2, genGwei),
    (1, Gen.nat (.linear 0 increment))]

/-- The words of a deposit: key, credentials, amount, signature. -/
def genDepositFields : List (Gen String) := [
  num (Gen.nat (.linear 0 60)),
  num (Gen.frequency [(3, pure 1), (3, pure 2), (2, pure 0), (1, Gen.element [3, 0xB0])]),
  num (Gen.nat (.linear 0 5)),
  num (Gen.frequency [(3, pure (32 * increment)), (2, pure increment), (2, genGwei),
    (1, Gen.element [0, 1, 2048 * increment, 2049 * increment])]),
  num (Gen.frequency [(5, pure 1), (1, pure 0), (1, pure 2)])]

/-- The words of an attestation: how far back, which committee, and what is wrong with it. -/
def genAttestationWord : Gen (List String) :=
  Gen.frequency [(1, genWord [num (Gen.nat (.linear 1 8)),
    num (Gen.frequency [(4, pure 0), (1, pure 1)]),
    num (Gen.nat (.linear 0 60)), pure "1", pure "1", genOk, pure "1", pure "1", pure "0",
    num (Gen.nat (.constant 0 1))]),
  (1, genWord [
    num (Gen.frequency [(6, Gen.nat (.linear 1 8)), (2, Gen.nat (.linear 0 20)),
      (1, Gen.element [0, 8, 9, 16, 17, 32, 33, 64, 65])]),
    num (Gen.frequency [(6, Gen.nat (.linear 0 1)), (1, Gen.nat (.linear 0 5))]),
    num (Gen.nat (.linear 0 60)),
    num (Gen.frequency [(6, pure 1), (1, pure 0), (1, pure 2)]),
    num (Gen.frequency [(6, pure 1), (1, pure 0), (1, pure 2)]),
    genOk,
    genOk,
    num (Gen.frequency [(8, pure 1), (1, pure 0), (1, pure 2)]),
    num (Gen.frequency [(6, pure 0), (2, pure 2), (1, pure 3)]),
    num (Gen.frequency [(6, pure 0), (2, pure 1), (1, pure 2)])])]

/-- The slot of the parent block, which Gloas reads for an attestation. -/
def genParentSlot : Gen (List String) :=
  (fun n => [toString n]) <$> Gen.frequency [(2, Gen.nat (.linear 0 900)), (1, pure 0)]

/-- The operations of a block, each with a near-valid argument. -/
def operations : List Call := [
  ⟨"process_voluntary_exit", allForks,
    genWord [num genIndex, genOperationEpoch, genOk], fun _ s _ bytes =>
    withArgument SignedVoluntaryExit bytes fun exit =>
      .ofState (processVoluntaryExit Config.minimal checks s exit)⟩,
  ⟨"process_proposer_slashing", allForks,
    genWord [num genIndex, num (Gen.nat (.linear 0 900)),
      num (Gen.frequency [(5, pure 0), (1, pure 1)]),
      genOk, genOk, num (Gen.frequency [(8, pure 0), (1, pure 1)]),
      num (Gen.frequency [(8, pure 0), (1, pure 1)])], fun _ s _ bytes =>
    withArgument ProposerSlashing bytes fun slashing =>
      .ofState (processProposerSlashing Config.minimal checks s slashing)⟩,
  ⟨"process_attester_slashing", allForks,
    (fun head a b => head ++ [a, b]) <$>
      genWord [num (Gen.nat (.constant 0 5)), genOk, genOk,
        num (Gen.frequency [(5, pure 1), (1, pure 0)]),
        num (Gen.frequency [(5, pure 1), (1, pure 0)])] <*> genIndices <*>
      -- `=` stands for the indices of the first attestation.
      Gen.frequency [(2, pure "="), (1, genIndices)],
    fun fork s _ bytes =>
    withArgument (AttesterSlashing Preset.minimal fork) bytes fun slashing =>
      .ofState (processAttesterSlashing Config.minimal checks s slashing)⟩,
  ⟨"process_attestation", allForks,
    (· ++ ·) <$> genAttestationWord <*> genParentSlot, fun fork s words bytes =>
    withArgument (Attestation Preset.minimal fork) bytes fun attestation =>
      let parent := (numbersOf s (words.getD 1 "0")).headD 0
      .ofState (processAttestation Config.minimal checks s parent attestation)⟩,
  ⟨"process_bls_to_execution_change", forksFrom .shapella,
    -- A key of 9 stands for the key that the credentials of the validator commit to.
    genWord [num genIndex, num (Gen.frequency [(3, pure 9), (1, Gen.nat (.linear 0 5))]),
      num (Gen.nat (.linear 0 5)), genOk],
    fun _ s _ bytes =>
    withArgument SignedBLSToExecutionChange bytes fun change =>
      .ofState (processBlsToExecutionChange Config.minimal checks s change)⟩,
  ⟨"process_deposit", forksBefore .fusaka,
    genWord (genDepositFields ++ [num (Gen.nat (.linear 1 6)), num (Gen.nat (.linear 0 6)),
      num (Gen.frequency [(5, pure 0), (1, pure 1), (1, pure 2)])]), fun fork s _ bytes =>
    if h : fork < .hegota then
      withArgument Deposit bytes fun deposit =>
        .ofState (processDeposit Config.minimal checks h s deposit)
    else .absent⟩,
  ⟨"process_deposit_request", forksFrom .pectra,
    genWord (genDepositFields ++
      [num (Gen.frequency [(3, Gen.nat (.linear 0 20)), (1, pure far)])]),
    fun fork s _ bytes =>
    if h : .pectra ≤ fork then
      withArgument DepositRequest bytes fun request => .ofState (processDepositRequest s h request)
    else .absent⟩,
  ⟨"process_withdrawal_request", forksFrom .pectra,
    -- An address of 9 stands for the address of the credentials of the validator.
    genWord [num (Gen.frequency [(4, pure 9), (1, Gen.nat (.linear 0 5))]), num genIndex,
      num genAmount],
    fun fork s _ bytes =>
    if h : .pectra ≤ fork then
      withArgument WithdrawalRequest bytes fun request =>
        .ofState (processWithdrawalRequest Config.minimal s h request)
    else .absent⟩,
  ⟨"process_consolidation_request", forksFrom .pectra,
    genWord [num (Gen.frequency [(4, pure 9), (1, Gen.nat (.linear 0 5))]), num genIndex,
      num genIndex],
    fun fork s _ bytes =>
    if h : .pectra ≤ fork then
      withArgument ConsolidationRequest bytes fun request =>
        .ofState (processConsolidationRequest Config.minimal s h request)
    else .absent⟩,
  ⟨"process_builder_deposit_request", forksFrom .glamsterdam,
    -- A signature flag of 2 signs under the domain of builder deposits.
    genWord [num (Gen.nat (.linear 0 8)),
      num (Gen.frequency [(6, pure 0xB0), (1, Gen.element [1, 2, 0])]),
      num (Gen.nat (.linear 0 5)),
      num (Gen.frequency [(3, (· * increment) <$> Gen.nat (.linear 0 5)), (1, genGwei)]),
      num (Gen.frequency [(5, pure 2), (1, pure 1), (1, pure 0)])], fun fork s _ bytes =>
    if h : .glamsterdam ≤ fork then
      withArgument BuilderDepositRequest bytes fun request =>
        .ofState (processBuilderDepositRequest Config.minimal checks s h request)
    else .absent⟩,
  ⟨"process_builder_exit_request", forksFrom .glamsterdam,
    genWord [num (Gen.frequency [(4, pure 9), (1, Gen.nat (.linear 0 5))]),
      num (Gen.nat (.linear 0 6))],
    fun fork s _ bytes =>
    if h : .glamsterdam ≤ fork then
      withArgument BuilderExitRequest bytes fun request =>
        .ofState (processBuilderExitRequest Config.minimal s h request)
    else .absent⟩,
  ⟨"process_execution_payload_bid", forksFrom .glamsterdam,
    -- The far future index is a self-build, which signs with the point at infinity (2).
    Gen.frequency [
      (1, genWord [pure (toString far), num (Gen.frequency [(5, pure 0), (1, pure 1)]),
        num (Gen.frequency [(5, pure 2), (1, pure 1)]), pure "0", genOk, genOk, genOk, genOk,
        num (Gen.frequency [(4, Gen.nat (.linear 0 6)), (1, Gen.element [9, 10, 4096])])]),
      (2, genWord [num (Gen.nat (.linear 0 5)),
        num (Gen.frequency [(1, pure 0), (3, (· * increment) <$> Gen.nat (.linear 0 40)),
          (1, genGwei)]),
        num (Gen.frequency [(6, pure 1), (1, pure 0), (1, pure 2)]),
        num (Gen.frequency [(8, pure 0), (1, pure 1)]), genOk, genOk, genOk, genOk,
        num (Gen.frequency [(4, Gen.nat (.linear 0 6)), (1, Gen.element [9, 10, 4096])])])],
    fun fork s _ bytes =>
    if h : .glamsterdam ≤ fork then
      withArgument (SignedExecutionPayloadBid Preset.minimal fork) bytes fun bid =>
        .ofState (processExecutionPayloadBid Config.minimal checks s h bid)
    else .absent⟩,
  ⟨"process_sync_aggregate", forksFrom .altair,
    genWord [num (Gen.nat (.linear 0 60)), genOk], fun fork s _ bytes =>
    if h : .altair ≤ fork then
      withArgument (SyncAggregate Preset.minimal) bytes fun aggregate =>
        .ofState (processSyncAggregate Config.minimal checks s h aggregate)
    else .absent⟩,
  ⟨"process_withdrawals", forksFrom .shapella,
    genWord [num (Gen.frequency [(4, pure 0), (1, Gen.nat (.constant 1 4))])], fun fork s _ bytes =>
    if h : .shapella ≤ fork then
      if gloas : .glamsterdam ≤ fork then
        .ofState (processWithdrawals s h fun before => absurd gloas (Nat.not_le_of_lt before))
      else
        withArgument (ExecutionPayload Preset.minimal fork) bytes fun payload =>
          .ofState (processWithdrawals s h fun _ => payload)
    else .absent⟩,
  ⟨"process_slots", allForks,
    genWord [num (Gen.frequency [(4, Gen.nat (.linear 1 9)), (1, Gen.nat (.linear 0 40))])],
    fun _ s words _ =>
    match firstNumbers s words with
    | [count] => .ofState (processSlots Config.minimal checks s (s.slot + count))
    | _ => .broken "process_slots takes one number"⟩]

/-- A block before Gloas, whole: header, payload, RANDAO, deposit vote, operations, sync aggregate.

The numbers say what is wrong with it, mostly nothing. -/
def blocks : List Call := [
  ⟨"process_block", forksBefore .glamsterdam,
    genWord [num (Gen.frequency [(9, pure 0), (1, pure 1)]),
      num (Gen.frequency [(9, pure 0), (1, pure 1)]), genOk, genOk,
      num (Gen.frequency [(6, pure 0), (1, Gen.nat (.constant 1 3))]),
      num (Gen.frequency [(4, Gen.nat (.linear 0 6)), (1, Gen.element [9, 10, 12, 13, 21, 22])]),
      num (Gen.nat (.linear 0 3)), num (Gen.nat (.linear 0 60)), genOk,
      num (Gen.frequency [(6, pure 0), (1, pure 1)])],
    fun fork s _ bytes =>
    withArgument (BeaconBlock Preset.minimal fork) bytes fun block =>
      .ofState (processBlock Config.minimal checks (ExecutionEngine.constant true) s block)⟩]

/-- The properties of a list of calls: each agrees with consensus-specs at each of its forks. -/
def callProperties (oracle : Oracle) (cases : Nat) (genWords : Gen (List String))
    (calls : List Call) : List (String × Property IO) :=
  calls.map fun call =>
    let words :=
      (fun state arguments => state ++ ["|"] ++ arguments) <$> genWords <*> call.arguments
    (call.name, (agrees oracle call.forks call.name words call.run).withTests cases)

end ConsensusProperty

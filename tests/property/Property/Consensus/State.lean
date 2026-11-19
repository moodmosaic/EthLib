import Hedgehog
import Support
import EthLib.Consensus.Transition.StateTransition
import EthLib.Cryptography.Hash.Sha256

/-!
# States of the beacon chain, described in words

A generator makes a description of a state: a list of words such as `slot=23` and `v=1,0,...`.
The oracle builds the state of the minimal preset from the words and returns its SSZ bytes, so
the driver and the reference start from the same state, and a failure shrinks to few words.

The reference then applies a function of consensus-specs, and the driver applies EthLib's.
They must agree on refusal, and on the root of the state after.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ConsensusProperty

/-- A state of the minimal preset. -/
abbrev State (fork : Fork) := BeaconState Preset.minimal fork

/-- The forks of the consensus layer, by the name of consensus-specs. -/
def allForks : List (String × Fork) :=
  [("phase0", .phase0), ("altair", .altair), ("bellatrix", .bellatrix), ("capella", .shapella),
    ("deneb", .dencun), ("electra", .pectra), ("fulu", .fusaka), ("gloas", .glamsterdam),
    ("heze", .hegota)]

/-- The forks from one on. -/
def forksFrom (first : Fork) : List (String × Fork) :=
  allForks.filter fun (_, fork) => first ≤ fork

/-- The forks before one. -/
def forksBefore (limit : Fork) : List (String × Fork) :=
  allForks.filter fun (_, fork) => fork < limit

/-- The signature that the test takes as valid: the hash of the keys and the message. -/
def fakeSignature (pubkeys : Array Cryptography.Bls.BLSPubkey) (message : ByteArray) : ByteArray :=
  let keys := pubkeys.foldl (fun acc key => acc ++ ⟨key.toArray⟩) ByteArray.empty
  Cryptography.Hash.sha256 (keys ++ message) ++ ⟨Array.replicate 64 0⟩

/-- Signature checks that need no pairing and still depend on every key and on the message. -/
def checks : SignatureChecks where
  verify pubkey message signature := fakeSignature #[pubkey] message == ⟨signature.toArray⟩
  fastAggregateVerify pubkeys message signature :=
    fakeSignature pubkeys message == ⟨signature.toArray⟩

/-! ## Generators -/

/-- The far future epoch. -/
def far : Nat := 2 ^ 64 - 1

/-- A balance increment of the minimal preset, in Gwei. -/
def increment : Nat := 10 ^ 9

/-- One value from each generator, all kept under shrinking.

`Gen.sequence` drops elements as it shrinks unless it is told how many must stay. -/
def genFields {α : Type} (gens : List (Gen α)) : Gen (List α) := Gen.sequence gens gens.length

/-- An epoch near the current one, written relative to it. -/
def genNear : Gen String :=
  Gen.choice [
    (fun n => s!"c-{n}") <$> Gen.nat (.linear 0 5),
    (fun n => s!"c+{n}") <$> Gen.nat (.linear 0 6)]

/-- An epoch: `usual` most of the time, else near the current one, far away, or anywhere. -/
def genEpoch (usual : String) : Gen String :=
  Gen.frequency [
    (6, pure usual),
    (4, genNear),
    (1, (fun n => s!"c+{n}") <$> Gen.element [31, 32, 33, 255, 256, 257]),
    (1, pure (toString far)),
    (1, pure "0"),
    (1, toString <$> Gen.nat (.exponential 0 far))]

/-- An effective balance: a whole number of increments, mostly at the two maxima. -/
def genEffective : Gen Nat :=
  Gen.frequency [
    (5, pure (32 * increment)),
    (3, (· * increment) <$> Gen.nat (.linear 0 34)),
    (2, (· * increment) <$> Gen.nat (.linear 32 2049)),
    (1, pure (2048 * increment)),
    (1, Gen.nat (.linear 0 (40 * increment)))]

/-- A balance at a distance from an effective balance that sits on a hysteresis threshold. -/
def genBalance (effective : Nat) : Gen Nat :=
  let step := increment / 4
  Gen.frequency [
    (3, pure effective),
    (6, do
      let steps ← Gen.element [0, 1, 2, 4, 5, 6]
      let nudge ← Gen.element [0, 1, 2]
      let up ← Gen.bool
      pure (if up then effective + steps * step + nudge - 1
        else effective + 1 - steps * step - nudge)),
    (2, Gen.nat (.linear 0 (40 * increment))),
    (2, Gen.element [0, 1, 16 * increment, 32 * increment, 32 * increment + 1, 2048 * increment,
      2048 * increment + 1, 2049 * increment]),
    (1, (far - ·) <$> Gen.nat (.exponential 0 (64 * increment))),
    (1, Gen.nat (.exponential 0 far))]

/-- One validator and its balance, flags and score, as a word. -/
def genValidator : Gen String := do
  let effective ← genEffective
  let fields ← genFields [
    toString <$> Gen.frequency [(3, pure 1), (3, pure 2), (2, pure 0), (1, Gen.element [3, 0xB0])],
    toString <$> Gen.nat (.linear 0 5),
    pure (toString effective),
    toString <$> genBalance effective,
    toString <$> Gen.frequency [(5, pure 0), (1, pure 1)],
    genEpoch "0",
    genEpoch "0",
    genEpoch (toString far),
    genEpoch (toString far),
    toString <$> Gen.frequency [(3, pure 7), (1, pure 0), (2, Gen.nat (.constant 0 7))],
    toString <$> Gen.frequency [(3, pure 7), (1, pure 0), (2, Gen.nat (.constant 0 7))],
    toString <$> Gen.frequency [(4, pure 0), (3, Gen.nat (.linear 0 40)),
      (1, Gen.nat (.exponential 0 far)), (1, (far - ·) <$> Gen.nat (.linear 0 8))]]
  pure ("v=" ++ ",".intercalate fields)

/-- An amount of Gwei: nothing, a few increments, the churn of the minimal preset, or huge. -/
def genGwei : Gen Nat :=
  Gen.frequency [
    (3, pure 0),
    (3, (· * increment) <$> Gen.nat (.linear 0 300)),
    (2, Gen.nat (.linear 0 (64 * increment))),
    (1, Gen.element [64 * increment, 128 * increment, 256 * increment]),
    (1, (far - ·) <$> Gen.nat (.exponential 0 (64 * increment)))]

/-- A validator index: mostly inside a small registry, sometimes just outside or far away. -/
def genIndex : Gen Nat :=
  Gen.frequency [(12, Gen.nat (.linear 0 12)), (1, Gen.nat (.linear 0 60)),
    (1, Gen.element [far, 2 ^ 40, 2 ^ 32])]

/-- A pending deposit: key, credentials, amount, slot and whether its signature is valid. -/
def genPendingDeposit : Gen String := do
  let fields ← genFields [
    Gen.nat (.linear 0 40),
    Gen.frequency [(3, pure 1), (3, pure 2), (2, pure 0), (1, Gen.element [3, 0xB0])],
    Gen.nat (.linear 0 5),
    Gen.frequency [(3, pure (32 * increment)), (2, pure increment), (2, genGwei),
      (1, Gen.element [0, 1, 2048 * increment, 2049 * increment])],
    Gen.frequency [(2, pure 0), (3, Gen.nat (.linear 0 400))],
    Gen.frequency [(4, pure 1), (1, pure 0)]]
  pure ("pd=" ++ ",".intercalate (fields.map toString))

/-- A pending partial withdrawal. -/
def genPendingPartial : Gen String := do
  let index ← genIndex
  let amount ← Gen.frequency [(3, (· * increment) <$> Gen.nat (.linear 0 5)), (2, genGwei)]
  let epoch ← genEpoch "c-1"
  pure s!"ppw={index},{amount},{epoch}"

/-- A pending consolidation. -/
def genPendingConsolidation : Gen String := do
  let source ← genIndex
  let target ← genIndex
  pure s!"pc={source},{target}"

/-- A pending attestation of Phase 0. -/
def genPendingAttestation : Gen String := do
  let fields ← genFields [
    Gen.nat (.constant 0 1), Gen.nat (.constant 0 7), Gen.nat (.linear 0 4), Gen.nat (.linear 0 50),
    Gen.frequency [(4, Gen.nat (.linear 1 8)), (1, Gen.element [0, 9, 32, far])],
    genIndex,
    Gen.frequency [(5, pure 1), (1, pure 0)],
    Gen.frequency [(5, pure 1), (1, pure 0)],
    Gen.frequency [(5, pure 1), (1, pure 0)]]
  pure ("pa=" ++ ",".intercalate (fields.map toString))

/-- The slot of a state: mostly the last of an epoch, early epochs and period ends included. -/
def genSlot : Gen Nat := do
  let epoch ← Gen.frequency [(2, Gen.nat (.constant 0 2)), (4, Gen.nat (.linear 0 40)),
    (2, Gen.element [7, 15, 23, 31, 63, 255, 256, 257]), (1, Gen.nat (.linear 0 5000))]
  let offset ← Gen.frequency [(5, pure 7), (2, Gen.nat (.constant 0 7))]
  pure (epoch * 8 + offset)

/-- The words of the state outside its lists. -/
def genScalars (genSlot : Gen Nat) : Gen (List String) := do
  let slot ← genSlot
  let rest ← genFields [
    ("forkepoch=" ++ ·) <$> Gen.frequency [(3, pure "0"), (2, genNear)],
    (fun n => s!"bits={n}") <$> Gen.nat (.constant 0 15),
    ("fin=" ++ ·) <$> Gen.frequency [(5, (fun n => s!"c-{n}") <$> Gen.nat (.linear 1 8)),
      (1, pure "0"), (1, genNear)],
    ("pj=" ++ ·) <$> Gen.frequency [(5, (fun n => s!"c-{n}") <$> Gen.nat (.linear 1 4)),
      (1, pure "0"), (1, genNear)],
    ("cj=" ++ ·) <$> Gen.frequency [(5, (fun n => s!"c-{n}") <$> Gen.nat (.linear 0 3)),
      (1, pure "0"), (1, genNear)],
    (fun a b => s!"eth1={a},{b}") <$> Gen.nat (.linear 0 20) <*> Gen.nat (.linear 0 20),
    (fun n => s!"votes={n}") <$> Gen.frequency [(2, pure 0), (1, Gen.nat (.linear 0 32))],
    (fun a b => s!"wd={a},{b}") <$> Gen.frequency [(4, Gen.nat (.linear 0 50)),
      (1, (far - ·) <$> Gen.nat (.linear 0 20))] <*> genIndex,
    (fun n => s!"hist={n}") <$> Gen.nat (.linear 0 3),
    (fun n => s!"drsi={n}") <$> Gen.frequency [(2, pure far), (2, Gen.nat (.linear 0 20))],
    (fun (d, x) (e, c) (f : String) => s!"churn={d},{x},{e},{c},{f}") <$>
      Gen.zip genGwei genGwei <*> Gen.zip (genEpoch "c+5") genGwei <*> genEpoch "c+5",
    (fun n => s!"sync={n}") <$> Gen.frequency [(5, pure 0), (1, pure 1)]]
  let lookahead ← Gen.frequency [(2, pure []), (1, pure ["lookahead"])]
  pure (s!"slot={slot}" :: rest ++ lookahead)

/-- A slashed balance of one epoch of the vector. -/
def genSlashing : Gen String := do
  let index ← Gen.nat (.constant 0 63)
  let amount ← Gen.frequency [(3, (· * increment) <$> Gen.nat (.linear 0 100)), (1, genGwei)]
  pure s!"slashings={index},{amount}"

/-- From Gloas: a builder, by key, address, balance, deposit epoch and withdrawable epoch. -/
def genBuilder : Gen String := do
  let key ← Gen.nat (.linear 0 8)
  let balance ← Gen.frequency [(3, (· * increment) <$> Gen.nat (.linear 0 40)), (1, genGwei)]
  let deposit ← genEpoch "0"
  let withdrawable ← genEpoch (toString far)
  pure s!"b={key},{key},{balance},{deposit},{withdrawable}"

/-- From Gloas: a pending payment of a slot, by place, weight, amount, builder and proposer. -/
def genBuilderPayment : Gen String := do
  let place ← Gen.nat (.constant 0 15)
  -- The quorum of a small registry is some hundreds of ETH.
  let weight ← Gen.frequency [(3, (· * 32 * increment) <$> Gen.nat (.linear 0 30)), (1, genGwei)]
  let amount ← Gen.frequency [(1, pure 0), (3, (· * increment) <$> Gen.nat (.linear 0 5)),
    (1, genGwei)]
  let builder ← Gen.frequency [(6, Gen.nat (.linear 0 4)), (1, genIndex)]
  let proposer ← genIndex
  pure s!"bpp={place},{weight},{amount},{builder},{proposer}"

/-- From Gloas: a pending withdrawal of a builder. -/
def genBuilderWithdrawal : Gen String := do
  let amount ← Gen.frequency [(3, (· * increment) <$> Gen.nat (.linear 0 5)), (1, genGwei)]
  let builder ← Gen.frequency [(6, Gen.nat (.linear 0 4)), (1, genIndex)]
  pure s!"bpw={amount},{builder}"

/-- The description of a state from a generator of its slot and one of its registry. -/
def genStateOf (genSlot : Gen Nat) (genRegistry : Gen (List String)) : Gen (List String) := do
  let scalars ← genScalars genSlot
  let registry ← genRegistry
  let lists ← genFields [
    Gen.list (.linear 0 4) genBuilder,
    Gen.list (.linear 0 4) genBuilderPayment,
    Gen.list (.linear 0 4) genBuilderWithdrawal,
    (fun next empty => [s!"gloas={next},{empty}"]) <$> Gen.nat (.linear 0 5) <*>
      Gen.frequency [(4, pure 0), (1, pure 1)],
    Gen.list (.linear 0 4) genSlashing,
    Gen.list (.linear 0 6) genPendingDeposit,
    Gen.list (.linear 0 4) genPendingPartial,
    Gen.list (.linear 0 4) genPendingConsolidation,
    Gen.list (.linear 0 8) genPendingAttestation]
  pure (scalars ++ registry ++ lists.flatten)

/-- A slashed validator whose penalty is due: withdrawable half a slashings vector from now.

The independent epochs of `genValidator` almost never meet that one epoch. -/
def genSlashedValidator : Gen String := do
  let prefix_ ← Gen.element [1, 2, 0]
  let effective ← Gen.frequency [(3, pure 32), (2, Gen.nat (.linear 1 64)), (2, pure 2048),
    (1, Gen.nat (.linear 32 2048))]
  let balance ← Gen.frequency [(4, pure (effective * increment)),
    (1, Gen.nat (.linear 0 increment)), (1, pure 0)]
  let due ← Gen.frequency [(6, pure 32), (1, pure 31), (1, pure 33)]
  pure s!"v={prefix_},0,{effective * increment},{balance},1,0,0,c-1,c+{due},7,7,0"

/-- The description of a state: from an empty registry to a few dozen validators. -/
def genState : Gen (List String) :=
  genStateOf genSlot
    (Gen.list (.linear 0 24) (Gen.frequency [(6, genValidator), (1, genSlashedValidator)]))

/-- A validator that has long been active, with a balance near 32 or 2048 ETH. -/
def genSettledValidator : Gen String := do
  let prefix_ ← Gen.element [1, 2, 0]
  let seed ← Gen.nat (.linear 0 5)
  let effective ← Gen.frequency [(4, pure 32), (1, Gen.nat (.linear 16 64)), (2, pure 2048)]
  let extra ← Gen.frequency [(2, pure 0), (2, Gen.nat (.linear 0 (3 * increment)))]
  let flags ← Gen.element [7, 0, 3]
  pure s!"v={prefix_},{seed},{effective * increment},{effective * increment + extra},\
0,0,0,{far},{far},{flags},{flags},0"

/-- A slot late enough for a validator active from genesis to exit, in any place of its epoch. -/
def genLateSlot : Gen Nat := do
  let epoch ← Gen.frequency [(5, Gen.nat (.linear 64 100)),
    (1, Gen.element [62, 63, 255, 256, 257]),
    (1, Gen.nat (.linear 0 5))]
  let offset ← Gen.nat (.constant 0 7)
  pure (epoch * 8 + offset)

/-- The description of a state for an operation: mostly settled validators, at a late slot.

A fully random registry rarely holds a validator that an operation accepts. -/
def genOperationState : Gen (List String) :=
  genStateOf (Gen.frequency [(5, genLateSlot), (1, genSlot)])
    (Gen.frequency [
      (1, Gen.list (.linear 0 3) genValidator),
      (7, Gen.list (.constant 4 24) (Gen.frequency [(3, genSettledValidator), (2, genValidator)])),
      -- Enough active validators for two committees in a slot.
      (1, Gen.list (.constant 64 72)
        (Gen.frequency [(9, genSettledValidator), (1, genValidator)]))])

/-! ## Running a call on both sides -/

/-- What EthLib made of a call. -/
inductive Outcome (fork : Fork) where
  /-- The state after. -/
  | state (post : State fork)
  /-- A value, in the text form of the oracle. -/
  | value (text : String)
  /-- The state after, of another fork: its root and its bytes. -/
  | upgraded (root : String) (bytes : ByteArray)
  /-- A refusal. -/
  | refused (why : String)
  /-- The driver could not run the call, as when the argument does not decode. -/
  | broken (why : String)

/-- The outcome of a function that changes the state. -/
def Outcome.ofState {fork : Fork} {ε : Type} [Repr ε] : Except ε (State fork) → Outcome fork
  | .ok post => .state post
  | .error e => .refused (toString (repr e))

/-- The outcome of a function that returns a value. -/
def Outcome.ofValue {fork : Fork} {ε α : Type} [Repr ε] (show_ : α → String) :
    Except ε α → Outcome fork
  | .ok a => .value (show_ a)
  | .error e => .refused (toString (repr e))

/-- The outcome of a call that the fork does not have: the driver must not have asked. -/
def Outcome.absent {fork : Fork} : Outcome fork := .broken "the fork has no such call"

/-- Read the argument that the oracle built, and go on with it. -/
def withArgument {fork : Fork} (α : Type) [SszType α] (bytes : ByteArray)
    (next : α → Outcome fork) : Outcome fork :=
  match SszType.deserialize α bytes with
  | .ok a => next a
  | .error e => .broken s!"EthLib does not read the argument of the reference: {repr e}"

/-- A number of an argument word, where `c+n` and `c-n` are epochs around the current one. -/
def numberAt (current : Nat) (word : String) : Nat :=
  if word.startsWith "c+" then min (current + (word.drop 2).toNat!) far
  else if word.startsWith "c-" then current - (word.drop 2).toNat!
  else word.toNat!

/-- The numbers of an argument word, as 64-bit words. -/
def numbersOf {fork : Fork} (state : State fork) (word : String) : List UInt64 :=
  if word.isEmpty then []
  else (word.splitOn ",").map fun w => UInt64.ofNat (numberAt (getCurrentEpoch state).toNat w)

/-- A list of numbers in the text form of the oracle. -/
def showList {α : Type} (show_ : α → String) (xs : List α) : String :=
  "[" ++ ",".intercalate (xs.map show_) ++ "]"

/-- A truth value in the text form of the oracle. -/
def showBool (b : Bool) : String := if b then "true" else "false"

/-- Hexadecimal of a fixed number of bytes. -/
def hexVector {n : Nat} (bytes : Vector UInt8 n) : String := hex ⟨bytes.toArray⟩

/-- Compare EthLib's outcome with the answer of the oracle for one state and argument.

The words describe the state, and after a `|` the argument.
`run` receives the state, the words of the argument, and its SSZ bytes as the oracle built it. -/
def compareAnswer (oracle : Oracle) (forkName : String) (fork : Fork) (answer : String)
    (arguments : List String)
    (run : State fork → List String → ByteArray → Outcome fork) :
    TestT IO (Option (State fork)) := do
  match answer.splitOn " " with
  | [pre, argument, expected] =>
    if expected = "skip" then pure none
    else
      let some preBytes := unhex? pre | failWith "the oracle sent no hexadecimal state"
      let some argBytes := unhex? argument | failWith "the oracle sent no hexadecimal argument"
      match SszType.deserialize (State fork) preBytes with
      | .error e => failWith s!"EthLib does not read the state of the reference: {repr e}"
      | .ok state =>
        let differ (root : String) (bytes : ByteArray) : TestT IO Unit := do
          if s!"ok:{root}" = expected then pure ()
          else if expected.startsWith "error:" then
            failWith s!"EthLib accepts, the reference refuses: {expected}"
          else
            let difference ← oracle.ask ["diff", forkName, hex bytes]
            failWith s!"the states after differ: {difference}"
        match run state arguments argBytes with
        | .broken why => failWith why
        -- The report says how the cases divide: a call that is mostly refused tests little.
        | .refused why =>
          label "refused"
          ensure (expected.startsWith "error:")
            s!"EthLib refuses ({why}), the reference answers {expected}"
          pure (some state)
        | .value text =>
          label "a value"
          s!"val:{text}" === expected
          pure (some state)
        | .upgraded root bytes =>
          label "upgraded"
          differ root bytes
          pure (some state)
        | .state post =>
          match SszType.hashTreeRoot post, SszType.serialize post with
          | .ok root, .ok bytes =>
            label (if bytes == preBytes then "the state unchanged" else "the state changed")
            differ (hexVector root) bytes
            pure (some post)
          | _, _ => failWith "EthLib cannot hash or write its own state"
  | _ => failWith s!"the oracle answered: {answer.take 300}"

/-- Compare EthLib's outcome with the reference's on the state that the words describe.

After a `|` the words describe the argument. -/
def compare (oracle : Oracle) (forkName : String) (fork : Fork) (call : String)
    (words : List String) (run : State fork → List String → ByteArray → Outcome fork) :
    TestT IO Unit := do
  let answer ← oracle.ask (["st", forkName, call] ++ words)
  let arguments := (words.dropWhile (· ≠ "|")).drop 1
  let _ ← compareAnswer oracle forkName fork answer arguments run

/-- A property of one call at the forks given: EthLib and the reference agree on every state. -/
def agrees (oracle : Oracle) (forks : List (String × Fork)) (call : String)
    (genWords : Gen (List String))
    (run : (fork : Fork) → State fork → List String → ByteArray → Outcome fork) :
    Property IO := propertyM do
  let (forkName, fork) ← forAllWith (·.1) (Gen.element forks)
  let words ← forAllWith " ".intercalate genWords
  pure (compare oracle forkName fork call words (run fork))

end ConsensusProperty

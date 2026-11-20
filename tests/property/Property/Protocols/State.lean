import Property.Protocols.World
import EthLib.Consensus.Transition.StateTransition
import EthLib.Cryptography.Hash.Sha256

/-!
# States of the beacon chain at any preset, described in words

A generator makes a description of a state: a list of words such as `slot=23` and `v=1,0,...`.

The oracle builds the state at the preset of the case from the words and returns its SSZ bytes.

So the driver and the reference start from the same state, and a failure shrinks to few words.

The words are those of `Property/Consensus/State.lean`, which ran the minimal preset alone.

Here every edge that a generator aims at is read from the preset and the configuration.

One such edge is the end of an epoch, another is half the vector of slashings.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ProtocolsProperty

/-- A state at a preset. -/
abbrev State (preset : Preset) (fork : Fork) := BeaconState preset fork

/-- The forks of the consensus layer, by the name of consensus-specs. -/
def allForks : List (String × Fork) :=
  [("phase0", .phase0), ("altair", .altair), ("bellatrix", .bellatrix), ("capella", .shapella),
    ("deneb", .dencun), ("electra", .pectra), ("fulu", .fusaka), ("gloas", .glamsterdam),
    ("heze", .hegota)]

/-- The forks of the execution layer and of the blob schedule that lie between consensus forks.

`Fork` is one order of all of them, and a definition of the consensus layer takes any fork.

Each is paired with the consensus fork in force at it, whose rules consensus-specs then gives. -/
def forksBetween : List (String × Fork) :=
  [("phase0", .berlin), ("phase0", .london), ("altair", .arrowGlacier), ("altair", .grayGlacier),
    ("bellatrix", .paris), ("fulu", .bpo1), ("fulu", .bpo2), ("fulu", .bpo3), ("fulu", .bpo4),
    ("fulu", .bpo5)]

/-- The forks from one on. -/
def forksFrom (first : Fork) : List (String × Fork) :=
  allForks.filter fun (_, fork) => first ≤ fork

/-- The forks before one. -/
def forksBefore (limit : Fork) : List (String × Fork) :=
  allForks.filter fun (_, fork) => fork < limit

/-- The forks between consensus forks at which a call of some forks is defined.

A call is defined at such a fork when it is at the consensus fork in force there. -/
def betweenOf (forks : List (String × Fork)) : List (String × Fork) :=
  forksBetween.filter fun (name, _) => forks.any (·.1 == name)

/-- The signature that the stand-in takes as valid: the hash of the keys and the message. -/
def fakeSignature (pubkeys : Array Cryptography.Bls.BLSPubkey) (message : ByteArray) : ByteArray :=
  let keys := pubkeys.foldl (fun acc key => acc ++ ⟨key.toArray⟩) ByteArray.empty
  Cryptography.Hash.sha256 (keys ++ message) ++ ⟨Array.replicate 64 0⟩

/-- Signature checks that need no pairing and still depend on every key and on the message. -/
def standIn : SignatureChecks where
  verify pubkey message signature := fakeSignature #[pubkey] message == ⟨signature.toArray⟩
  fastAggregateVerify pubkeys message signature :=
    fakeSignature pubkeys message == ⟨signature.toArray⟩

/-! ## Generators -/

/-- The far future epoch. -/
def far : Nat := 2 ^ 64 - 1

/-- What the generators read of a world: the edges that a state is aimed at. -/
structure Shape where
  /-- The slots of an epoch. -/
  slots : Nat
  /-- A balance increment, in Gwei. -/
  increment : Nat
  /-- The activation balance, in increments. -/
  low : Nat
  /-- The largest effective balance of a compounding validator, in increments. -/
  high : Nat
  /-- The steps of hysteresis in one increment. -/
  quotient : Nat
  /-- The steps of hysteresis at and around which a balance moves its effective balance. -/
  steps : List Nat
  /-- The epochs of the vector of slashings. -/
  slashings : Nat
  /-- The epochs at whose ends something happens: periods of sync committees, votes, vectors. -/
  periods : List Nat
  /-- The epochs before a validator may exit. -/
  shard : Nat
  /-- The validators that give a slot two committees, as far as a test registry goes. -/
  crowd : Nat
  /-- The most votes on the deposit chain that a state holds. -/
  votes : Nat

/-- The shape of a world. -/
def World.shape (world : World) : Shape :=
  let p := world.preset
  let increment := max p.EFFECTIVE_BALANCE_INCREMENT.toNat 1
  let slots := max p.SLOTS_PER_EPOCH.toNat 1
  let down := p.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat
  let up := p.HYSTERESIS_UPWARD_MULTIPLIER.toNat
  { slots, increment,
    low := p.MIN_ACTIVATION_BALANCE.toNat / increment,
    high := p.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / increment,
    quotient := max p.HYSTERESIS_QUOTIENT.toNat 1,
    steps := [0, down, down + 1, up - 1, up, up + 1],
    slashings := max p.EPOCHS_PER_SLASHINGS_VECTOR.toNat 1,
    periods := [p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat, p.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat,
      p.EPOCHS_PER_HISTORICAL_VECTOR.toNat, p.SLOTS_PER_HISTORICAL_ROOT.toNat / slots,
      p.EPOCHS_PER_SLASHINGS_VECTOR.toNat].map (max · 1),
    shard := world.config.SHARD_COMMITTEE_PERIOD.toNat,
    crowd := min (2 * slots * p.TARGET_COMMITTEE_SIZE.toNat) 120,
    votes := p.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * slots }

/-- One value from each generator, all kept under shrinking.

`Gen.sequence` drops elements as it shrinks unless it is told how many must stay. -/
def genFields {α : Type} (gens : List (Gen α)) : Gen (List α) := Gen.sequence gens gens.length

/-- An epoch near the current one, written relative to it. -/
def genNear : Gen String :=
  Gen.choice [
    (fun n => s!"c-{n}") <$> Gen.nat (.linear 0 5),
    (fun n => s!"c+{n}") <$> Gen.nat (.linear 0 6)]

/-- An epoch: `usual` most of the time, else near the current one, far away, or anywhere. -/
def genEpoch (shape : Shape) (usual : String) : Gen String :=
  let half := shape.slashings / 2
  Gen.frequency [
    (6, pure usual),
    (4, genNear),
    (1, (fun n => s!"c+{n}") <$> Gen.element [half - 1, half, half + 1, 255, 256, 257]),
    (1, pure (toString far)),
    (1, pure "0"),
    (1, toString <$> Gen.nat (.exponential 0 far))]

/-- An effective balance: a whole number of increments, mostly at the two maxima. -/
def genEffective (shape : Shape) : Gen Nat :=
  Gen.frequency [
    (5, pure (shape.low * shape.increment)),
    (3, (· * shape.increment) <$> Gen.nat (.linear 0 (shape.low + 2))),
    (2, (· * shape.increment) <$> Gen.nat (.linear shape.low (shape.high + 1))),
    (1, pure (shape.high * shape.increment)),
    (1, Gen.nat (.linear 0 ((shape.low + 8) * shape.increment)))]

/-- A balance at a distance from an effective balance that sits on a hysteresis threshold. -/
def genBalance (shape : Shape) (effective : Nat) : Gen Nat :=
  let step := shape.increment / shape.quotient
  let increment := shape.increment
  Gen.frequency [
    (3, pure effective),
    (6, do
      let steps ← Gen.element shape.steps
      let nudge ← Gen.element [0, 1, 2]
      let up ← Gen.bool
      pure (if up then effective + steps * step + nudge - 1
        else effective + 1 - steps * step - nudge)),
    (2, Gen.nat (.linear 0 ((shape.low + 8) * increment))),
    (2, Gen.element [0, 1, shape.low / 2 * increment, shape.low * increment,
      shape.low * increment + 1, shape.high * increment, shape.high * increment + 1,
      (shape.high + 1) * increment]),
    (1, (far - ·) <$> Gen.nat (.exponential 0 (64 * increment))),
    (1, Gen.nat (.exponential 0 far))]

/-- One validator and its balance, flags and score, as a word. -/
def genValidator (shape : Shape) : Gen String := do
  let effective ← genEffective shape
  let fields ← genFields [
    toString <$> Gen.frequency [(3, pure 1), (3, pure 2), (2, pure 0), (1, Gen.element [3, 0xB0])],
    toString <$> Gen.nat (.linear 0 5),
    pure (toString effective),
    toString <$> genBalance shape effective,
    toString <$> Gen.frequency [(5, pure 0), (1, pure 1)],
    genEpoch shape "0",
    genEpoch shape "0",
    genEpoch shape (toString far),
    genEpoch shape (toString far),
    toString <$> Gen.frequency [(3, pure 7), (1, pure 0), (2, Gen.nat (.constant 0 7))],
    toString <$> Gen.frequency [(3, pure 7), (1, pure 0), (2, Gen.nat (.constant 0 7))],
    toString <$> Gen.frequency [(4, pure 0), (3, Gen.nat (.linear 0 40)),
      (1, Gen.nat (.exponential 0 far)), (1, (far - ·) <$> Gen.nat (.linear 0 8))]]
  pure ("v=" ++ ",".intercalate fields)

/-- An amount of Gwei: nothing, a few increments, a churn, or huge. -/
def genGwei (shape : Shape) : Gen Nat :=
  let increment := shape.increment
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
def genPendingDeposit (shape : Shape) : Gen String := do
  let increment := shape.increment
  let fields ← genFields [
    -- With real BLS a key from 900 on is no valid public key: see `oracle/protocols_real.py`.
    Gen.frequency [(8, Gen.nat (.linear 0 40)), (1, Gen.nat (.constant 900 903))],
    Gen.frequency [(3, pure 1), (3, pure 2), (2, pure 0), (1, Gen.element [3, 0xB0])],
    Gen.nat (.linear 0 5),
    Gen.frequency [(3, pure (shape.low * increment)), (2, pure increment), (2, genGwei shape),
      (1, Gen.element [0, 1, shape.high * increment, (shape.high + 1) * increment])],
    Gen.frequency [(2, pure 0), (3, Gen.nat (.linear 0 (50 * shape.slots)))],
    Gen.frequency [(4, pure 1), (1, pure 0)]]
  pure ("pd=" ++ ",".intercalate (fields.map toString))

/-- A pending partial withdrawal. -/
def genPendingPartial (shape : Shape) : Gen String := do
  let index ← genIndex
  let amount ← Gen.frequency [(3, (· * shape.increment) <$> Gen.nat (.linear 0 5)),
    (2, genGwei shape)]
  let epoch ← genEpoch shape "c-1"
  pure s!"ppw={index},{amount},{epoch}"

/-- A pending consolidation. -/
def genPendingConsolidation : Gen String := do
  let source ← genIndex
  let target ← genIndex
  pure s!"pc={source},{target}"

/-- A pending attestation of Phase 0. -/
def genPendingAttestation (shape : Shape) : Gen String := do
  let fields ← genFields [
    Gen.nat (.constant 0 1), Gen.nat (.constant 0 (shape.slots - 1)), Gen.nat (.linear 0 4),
    Gen.nat (.linear 0 50),
    Gen.frequency [(4, Gen.nat (.linear 1 shape.slots)),
      (1, Gen.element [0, shape.slots + 1, 4 * shape.slots, far])],
    genIndex,
    Gen.frequency [(5, pure 1), (1, pure 0)],
    Gen.frequency [(5, pure 1), (1, pure 0)],
    Gen.frequency [(5, pure 1), (1, pure 0)]]
  pure ("pa=" ++ ",".intercalate (fields.map toString))

/-- The epochs just before, at and after the end of a period of the preset. -/
def periodEdges (shape : Shape) : List Nat :=
  shape.periods.flatMap fun period => [period - 1, period, period + 1, 2 * period - 1]

/-- The slot of a state: mostly the last of an epoch, early epochs and period ends included. -/
def genSlot (shape : Shape) : Gen Nat := do
  let epoch ← Gen.frequency [(2, Gen.nat (.constant 0 2)), (4, Gen.nat (.linear 0 40)),
    (2, Gen.element (periodEdges shape)), (1, Gen.nat (.linear 0 5000))]
  let offset ← Gen.frequency [(5, pure (shape.slots - 1)),
    (2, Gen.nat (.constant 0 (shape.slots - 1)))]
  pure (epoch * shape.slots + offset)

/-- The words of the state outside its lists. -/
def genScalars (shape : Shape) (genSlot : Gen Nat) : Gen (List String) := do
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
    (fun n => s!"votes={n}") <$>
      Gen.frequency [(2, pure 0), (1, Gen.nat (.linear 0 (min shape.votes 40)))],
    (fun a b => s!"wd={a},{b}") <$> Gen.frequency [(4, Gen.nat (.linear 0 50)),
      (1, (far - ·) <$> Gen.nat (.linear 0 20))] <*> genIndex,
    (fun n => s!"hist={n}") <$> Gen.nat (.linear 0 3),
    (fun n => s!"drsi={n}") <$> Gen.frequency [(2, pure far), (2, Gen.nat (.linear 0 20))],
    (fun (d, x) (e, c) (f : String) => s!"churn={d},{x},{e},{c},{f}") <$>
      Gen.zip (genGwei shape) (genGwei shape) <*>
      Gen.zip (genEpoch shape "c+5") (genGwei shape) <*> genEpoch shape "c+5",
    (fun n => s!"sync={n}") <$> Gen.frequency [(5, pure 0), (1, pure 1)]]
  let lookahead ← Gen.frequency [(2, pure []), (1, pure ["lookahead"])]
  pure (s!"slot={slot}" :: rest ++ lookahead)

/-- A slashed balance of one epoch of the vector. -/
def genSlashing (shape : Shape) : Gen String := do
  let index ← Gen.nat (.constant 0 (shape.slashings - 1))
  let amount ← Gen.frequency [(3, (· * shape.increment) <$> Gen.nat (.linear 0 100)),
    (1, genGwei shape)]
  pure s!"slashings={index},{amount}"

/-- From Gloas: a builder, by key, address, balance, deposit epoch and withdrawable epoch. -/
def genBuilder (shape : Shape) : Gen String := do
  let key ← Gen.nat (.linear 0 8)
  let balance ← Gen.frequency [(3, (· * shape.increment) <$> Gen.nat (.linear 0 40)),
    (1, genGwei shape)]
  let deposit ← genEpoch shape "0"
  let withdrawable ← genEpoch shape (toString far)
  pure s!"b={key},{key},{balance},{deposit},{withdrawable}"

/-- From Gloas: a pending payment of a slot, by place, weight, amount, builder and proposer. -/
def genBuilderPayment (shape : Shape) : Gen String := do
  let place ← Gen.nat (.constant 0 (2 * shape.slots - 1))
  -- The quorum of a small registry is some hundreds of ETH.
  let weight ← Gen.frequency [
    (3, (· * shape.low * shape.increment) <$> Gen.nat (.linear 0 30)), (1, genGwei shape)]
  let amount ← Gen.frequency [(1, pure 0), (3, (· * shape.increment) <$> Gen.nat (.linear 0 5)),
    (1, genGwei shape)]
  let builder ← Gen.frequency [(6, Gen.nat (.linear 0 4)), (1, genIndex)]
  let proposer ← genIndex
  pure s!"bpp={place},{weight},{amount},{builder},{proposer}"

/-- From Gloas: a pending withdrawal of a builder. -/
def genBuilderWithdrawal (shape : Shape) : Gen String := do
  let amount ← Gen.frequency [(3, (· * shape.increment) <$> Gen.nat (.linear 0 5)),
    (1, genGwei shape)]
  let builder ← Gen.frequency [(6, Gen.nat (.linear 0 4)), (1, genIndex)]
  pure s!"bpw={amount},{builder}"

/-- The description of a state from a generator of its slot and one of its registry. -/
def genStateOf (shape : Shape) (genSlot : Gen Nat) (genRegistry : Gen (List String)) :
    Gen (List String) := do
  let scalars ← genScalars shape genSlot
  let registry ← genRegistry
  let lists ← genFields [
    Gen.list (.linear 0 4) (genBuilder shape),
    Gen.list (.linear 0 4) (genBuilderPayment shape),
    Gen.list (.linear 0 4) (genBuilderWithdrawal shape),
    (fun next empty => [s!"gloas={next},{empty}"]) <$> Gen.nat (.linear 0 5) <*>
      Gen.frequency [(4, pure 0), (1, pure 1)],
    Gen.list (.linear 0 4) (genSlashing shape),
    Gen.list (.linear 0 6) (genPendingDeposit shape),
    Gen.list (.linear 0 4) (genPendingPartial shape),
    Gen.list (.linear 0 4) genPendingConsolidation,
    Gen.list (.linear 0 8) (genPendingAttestation shape)]
  pure (scalars ++ registry ++ lists.flatten)

/-- A slashed validator whose penalty is due: withdrawable half a slashings vector from now.

The independent epochs of `genValidator` almost never meet that one epoch. -/
def genSlashedValidator (shape : Shape) : Gen String := do
  let prefix_ ← Gen.element [1, 2, 0]
  let effective ← Gen.frequency [(3, pure shape.low), (2, Gen.nat (.linear 1 (2 * shape.low))),
    (2, pure shape.high), (1, Gen.nat (.linear shape.low shape.high))]
  let balance ← Gen.frequency [(4, pure (effective * shape.increment)),
    (1, Gen.nat (.linear 0 shape.increment)), (1, pure 0)]
  let half := shape.slashings / 2
  let due ← Gen.frequency [(6, pure half), (1, pure (half - 1)), (1, pure (half + 1))]
  pure s!"v={prefix_},0,{effective * shape.increment},{balance},1,0,0,c-1,c+{due},7,7,0"

/-- The description of a state: from an empty registry to a few dozen validators. -/
def genState (shape : Shape) : Gen (List String) :=
  genStateOf shape (genSlot shape)
    (Gen.list (.linear 0 24)
      (Gen.frequency [(6, genValidator shape), (1, genSlashedValidator shape)]))

/-- A validator that has long been active, with a balance near the two maxima. -/
def genSettledValidator (shape : Shape) : Gen String := do
  let prefix_ ← Gen.element [1, 2, 0]
  let seed ← Gen.nat (.linear 0 5)
  let effective ← Gen.frequency [(4, pure shape.low),
    (1, Gen.nat (.linear (shape.low / 2) (2 * shape.low))), (2, pure shape.high)]
  let extra ← Gen.frequency [(2, pure 0), (2, Gen.nat (.linear 0 (3 * shape.increment)))]
  let flags ← Gen.element [7, 0, 3]
  pure s!"v={prefix_},{seed},{effective * shape.increment},\
{effective * shape.increment + extra},0,0,0,{far},{far},{flags},{flags},0"

/-- A slot late enough for a validator active from genesis to exit, in any place of its epoch. -/
def genLateSlot (shape : Shape) : Gen Nat := do
  let epoch ← Gen.frequency [(5, (shape.shard + ·) <$> Gen.nat (.linear 0 36)),
    (1, Gen.element ((shape.shard - 2) :: (shape.shard - 1) :: periodEdges shape)),
    (1, Gen.nat (.linear 0 5))]
  let offset ← Gen.nat (.constant 0 (shape.slots - 1))
  pure (epoch * shape.slots + offset)

/-- The description of a state for an operation: mostly settled validators, at a late slot.

A fully random registry rarely holds a validator that an operation accepts. -/
def genOperationState (shape : Shape) : Gen (List String) :=
  genStateOf shape (Gen.frequency [(5, genLateSlot shape), (1, genSlot shape)])
    (Gen.frequency [
      (1, Gen.list (.linear 0 3) (genValidator shape)),
      (7, Gen.list (.constant 4 24)
        (Gen.frequency [(3, genSettledValidator shape), (2, genValidator shape)])),
      -- Enough active validators for two committees in a slot, where a registry can hold them.
      (1, Gen.list (.constant shape.crowd (shape.crowd + 8))
        (Gen.frequency [(9, genSettledValidator shape), (1, genValidator shape)]))])

/-! ## Running a call on both sides -/

/-- What EthLib made of a call. -/
inductive Outcome (preset : Preset) (fork : Fork) where
  /-- The state after. -/
  | state (post : State preset fork)
  /-- A value, in the text form of the oracle. -/
  | value (text : String)
  /-- The state after, of another fork: its root and its bytes, and the label of the case. -/
  | upgraded (root : String) (bytes : ByteArray) (what : String := "upgraded")
  /-- A refusal. -/
  | refused (why : String)
  /-- The driver could not run the call, as when the argument does not decode. -/
  | broken (why : String)

variable {preset : Preset} {fork : Fork}

/-- The outcome of a function that changes the state. -/
def Outcome.ofState {ε : Type} [Repr ε] : Except ε (State preset fork) → Outcome preset fork
  | .ok post => .state post
  | .error e => .refused (toString (repr e))

/-- The outcome of a function that returns a value. -/
def Outcome.ofValue {ε α : Type} [Repr ε] (show_ : α → String) :
    Except ε α → Outcome preset fork
  | .ok a => .value (show_ a)
  | .error e => .refused (toString (repr e))

/-- The outcome of a call that the fork does not have: the driver must not have asked. -/
def Outcome.absent : Outcome preset fork := .broken "the fork has no such call"

/-- Read the argument that the oracle built, and go on with it. -/
def withArgument (α : Type) [SszType α] (bytes : ByteArray)
    (next : α → Outcome preset fork) : Outcome preset fork :=
  match SszType.deserialize α bytes with
  | .ok a => next a
  | .error e => .broken s!"EthLib does not read the argument of the reference: {repr e}"

/-- A number of an argument word, where `c+n` and `c-n` are epochs around the current one. -/
def numberAt (current : Nat) (word : String) : Nat :=
  if word.startsWith "c+" then min (current + (word.drop 2).toNat!) far
  else if word.startsWith "c-" then current - (word.drop 2).toNat!
  else word.toNat!

/-- The numbers of an argument word, as 64-bit words. -/
def numbersOf (state : State preset fork) (word : String) : List UInt64 :=
  if word.isEmpty then []
  else (word.splitOn ",").map fun w => UInt64.ofNat (numberAt (getCurrentEpoch state).toNat w)

/-- A list of numbers in the text form of the oracle. -/
def showList {α : Type} (show_ : α → String) (xs : List α) : String :=
  "[" ++ ",".intercalate (xs.map show_) ++ "]"

/-- A truth value in the text form of the oracle. -/
def showBool (b : Bool) : String := if b then "true" else "false"

/-- Hexadecimal of a fixed number of bytes. -/
def hexVector {n : Nat} (bytes : Vector UInt8 n) : String := hex ⟨bytes.toArray⟩

/-- Bytes from hexadecimal, read from the bytes of the text.

A state of mainnet is six million digits, too many for a list of characters. -/
def unhexFast (text : String) : Option ByteArray :=
  if text = "-" then some ByteArray.empty
  else
    let raw := text.toUTF8
    if raw.size % 2 = 1 then none
    else
      let digit (b : UInt8) : UInt8 :=
        if 48 ≤ b && b ≤ 57 then b - 48 else if 97 ≤ b && b ≤ 102 then b - 87 else 255
      let rec go (i : Nat) (fuel : Nat) (acc : ByteArray) : Option ByteArray :=
        match fuel with
        | 0 => some acc
        | fuel + 1 =>
          let hi := digit raw[i]!
          let lo := digit raw[i + 1]!
          if hi = 255 || lo = 255 then none else go (i + 2) fuel (acc.push (hi * 16 + lo))
      go 0 (raw.size / 2) (ByteArray.emptyWithCapacity (raw.size / 2))

/-- Bytes in hexadecimal, built as bytes. -/
def hexFast (bytes : ByteArray) : String :=
  if bytes.isEmpty then "-"
  else
    let digit (n : UInt8) : UInt8 := if n < 10 then n + 48 else n + 87
    let out := bytes.foldl (fun acc b => (acc.push (digit (b >>> 4))).push (digit (b &&& 15)))
      (ByteArray.emptyWithCapacity (2 * bytes.size))
    (String.fromUTF8? out).getD ""

/-- The words that name a case to the oracle: the fork, the world and the signatures. -/
def caseWords (forkName : String) (world : World) (signatures : String) : List String :=
  [forkName, world.presetKey, world.configKey, signatures]

/-- Compare EthLib's outcome with the answer of the oracle for one state and argument.

The words describe the state, and after a `|` the argument.

`run` receives the state, the words of the argument, and its SSZ bytes as the oracle built it. -/
def compareAnswer (oracle : Oracle) (forkName : String) (world : World) (fork : Fork)
    (answer : String) (arguments : List String)
    (run : State world.preset fork → List String → ByteArray → Outcome world.preset fork) :
    TestT IO (Option (State world.preset fork)) := do
  match answer.splitOn " " with
  | [pre, argument, expected] =>
    if expected = "skip" then
      label "skipped"
      pure none
    else
      let some preBytes := unhexFast pre | failWith "the oracle sent no hexadecimal state"
      let some argBytes := unhexFast argument | failWith "the oracle sent no hexadecimal argument"
      match SszType.deserialize (State world.preset fork) preBytes with
      | .error e => failWith s!"EthLib does not read the state of the reference: {repr e}"
      | .ok state =>
        let differ (root : String) (bytes : ByteArray) : TestT IO Unit := do
          if s!"ok:{root}" = expected then pure ()
          else if expected.startsWith "error:" then
            failWith s!"EthLib accepts, the reference refuses: {expected}"
          else
            let difference ←
              oracle.ask ["diff", forkName, world.presetKey, hexFast bytes]
            failWith s!"the states after differ: {difference}"
        match run state arguments argBytes with
        | .broken why => failWith why
        -- The report says how the cases divide: a call that is mostly refused tests little.
        | .refused why =>
          label "refused"
          ensure (expected.startsWith "error:")
            s!"EthLib refuses ({why}), the reference answers {expected.take 200}"
          pure (some state)
        | .value text =>
          label "a value"
          -- A short answer in words is a verdict, so the report counts each one.
          if text.length ≤ 16 && !text.any Char.isDigit then label s!"answers {text}"
          s!"val:{text}" === expected
          pure (some state)
        | .upgraded root bytes what =>
          label what
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
def compare (oracle : Oracle) (forkName : String) (world : World) (fork : Fork)
    (signatures call : String) (words : List String)
    (run : State world.preset fork → List String → ByteArray → Outcome world.preset fork) :
    TestT IO Unit := do
  let answer ← oracle.ask (["st"] ++ caseWords forkName world signatures ++ [call] ++ words)
  let arguments := (words.dropWhile (· ≠ "|")).drop 1
  let _ ← compareAnswer oracle forkName world fork answer arguments run

end ProtocolsProperty

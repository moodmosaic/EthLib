import Property.Engine.NewPayload
import EthLib.Engine.ForkchoiceUpdated

/-!
# `engine_forkchoiceUpdated`: the choice of the head, as a state machine

The model is a tree of blocks by index.

It is written from steps 1 to 5, 7 and 9 of `engine_forkchoiceUpdatedV1`.

It is also written from the payload validation of `paris.md`.

A sequence adds blocks to the tree and sends updates.

After each update, four values of EthLib must be those of the model.

They are the status, the latest valid hash, the head and the known finalized block.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Engine

namespace EngineProperty

/-- The terminal total difficulty of the tests. -/
def testTransition : TransitionConfiguration := ⟨100, Vector.replicate 32 0, 0⟩

/-- A block of the model. -/
structure ModelBlock where
  /-- The index of the parent, or none for a parent that the node does not hold. -/
  parent : Option Nat
  /-- Whether the block passes its own validation. -/
  ownValid : Bool
  /-- For a block of proof of work, its total difficulty and its parent's. -/
  pow : Option (Nat × Nat)
  number : Nat
  timestamp : Nat
  deriving Repr, BEq

/-- A block that an update names: one of the tree, one that the node lacks, or the zero hash. -/
inductive BlockRef where
  | known (index : Nat)
  | unknown
  | zero
  deriving Repr, BEq

/-- What the specification answers to an update. -/
inductive Answer where
  | syncing
  /-- Invalid, with the latest valid ancestor: a block, the zero hash, or none. -/
  | invalid (latestValid : Option BlockRef)
  /-- Valid; `applied` says whether the update took effect. -/
  | valid (applied : Bool)
  | invalidState
  deriving Repr, BEq

/-- The model: the blocks, the head, the known finalized block, and the last answer. -/
structure ForkchoiceModel where
  blocks : Array ModelBlock := #[]
  head : Option Nat := none
  finalized : Option Nat := none
  last : Option Answer := none
  deriving Repr

/-- A step of a sequence. -/
inductive ForkchoiceStep where
  | add (block : ModelBlock)
  | update (head safe finalized : BlockRef)
  deriving Repr, BEq

namespace ForkchoiceModel

/-- The indices from a block back to the first ancestor that the node holds no parent of. -/
def chain (m : ForkchoiceModel) (index : Nat) : List Nat :=
  go m.blocks.size index
where
  go : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, i =>
      match m.blocks[i]? with
      | some b => i :: (match b.parent with
        | some p => go fuel p
        | none => [])
      | none => []

/-- Whether a block and each ancestor that the node holds pass their own validation. -/
def isValid (m : ForkchoiceModel) (index : Nat) : Bool :=
  (m.chain index).all fun i => (m.blocks[i]?.map (·.ownValid)).getD false

/-- Point 2 of payload validation: the most recent block of proof of work is terminal.

EIP-3675: its total difficulty reaches the terminal one, and that of its parent does not. -/
def terminalHolds (m : ForkchoiceModel) (index : Nat) : Bool :=
  match (m.chain index).findSome? fun i => m.blocks[i]? >>= (·.pow) with
  | some (total, parentTotal) => 100 ≤ total && parentTotal < 100
  | none => true

/-- Point 3 of payload validation: the latest valid ancestor, zero for one of proof of work. -/
def latestValid (m : ForkchoiceModel) (index : Nat) : Option BlockRef :=
  ((m.chain index).find? m.isValid).map fun i =>
    if (m.blocks[i]? >>= (·.pow)).isSome then .zero else .known i

/-- Whether a block named by an update is the zero hash, or the head or an ancestor of it. -/
def onChain (m : ForkchoiceModel) (head : Nat) : BlockRef → Bool
  | .zero => true
  | .known i => (m.chain head).contains i
  | .unknown => false

/-- The answer to an update, by steps 1 to 5 and 9 of the method. -/
def answer (m : ForkchoiceModel) (head safe finalized : BlockRef) : Answer :=
  match head with
  | .unknown | .zero => .syncing
  | .known h =>
    if h ≥ m.blocks.size then .syncing
    else if !m.terminalHolds h then .invalid (some .zero)
    else if !m.isValid h then .invalid (m.latestValid h)
    else if (m.finalized.map fun f => h != f && (m.chain f).contains h).getD false then
      .valid false
    else
      -- The note of ForkchoiceStateV1: no zero hash once the transition block is finalized.
      let transitionFinalized :=
        (m.finalized.bind fun f => m.blocks[f]?.map (·.pow.isNone)).getD false
      if transitionFinalized && (safe == .zero || finalized == .zero) then .invalidState
      else if m.onChain h safe && m.onChain h finalized then .valid true
      else .invalidState

/-- The state after a step. -/
def step (m : ForkchoiceModel) : ForkchoiceStep → ForkchoiceModel
  | .add block => { m with blocks := m.blocks.push block, last := none }
  | .update head safe finalized =>
    let answer := m.answer head safe finalized
    match answer, head, finalized with
    | .valid true, .known h, .known f =>
      { m with head := some h, finalized := some f, last := answer }
    | .valid true, .known h, _ => { m with head := some h, last := answer }
    | _, _, _ => { m with last := answer }

end ForkchoiceModel

/-- The block hash of the block at an index of the model: never zero. -/
def hashOfIndex (index : Nat) : Hash32 :=
  Vector.ofFn fun j => if j.val == 0 then 0xb1 else if j.val == 31 then UInt8.ofNat index
    else if j.val == 30 then UInt8.ofNat (index / 256) else 0

/-- A hash that no block of the model has. -/
def unknownHash : Hash32 := Vector.replicate 32 0xff

/-- The hash that a reference names. -/
def BlockRef.hash : BlockRef → Hash32
  | .known i => hashOfIndex i
  | .unknown => unknownHash
  | .zero => ZERO_HASH

/-- A block for the tree: on a block of the tree mostly, valid mostly.

A block of proof of work sits on one of proof of work, or on no known block.

Its totals are near the terminal total difficulty of 100. -/
def genModelBlock (m : ForkchoiceModel) : Gen ModelBlock := do
  let size := m.blocks.size
  let parent ← if size == 0 then pure none else
    Gen.frequency [(1, pure none), (3, some <$> Gen.nat (.constant 0 (size - 1))),
      (6, pure (some (size - 1)))]
  let parentBlock := parent.bind (m.blocks[·]?)
  let powAllowed := match parentBlock with
    | some b => b.pow.isSome
    | none => true
  let parentTotal := (parentBlock.bind (·.pow)).map (·.1)
  let genPow : Gen (Option (Nat × Nat)) := do
    let below ← match parentTotal with
      | some t => pure t
      | none => Gen.element [0, 50, 99, 100, 101]
    let difficulty ← Gen.element [0, 1, 2, 50]
    pure (some (below + difficulty, below))
  let pow ← if powAllowed then Gen.frequency [(1, pure none), (2, genPow)] else pure none
  let ownValid ← Gen.frequency [(5, pure true), (1, pure false)]
  let number := (parentBlock.map (·.number + 1)).getD 10
  let timestamp ← (((parentBlock.map (·.timestamp)).getD 0) + ·) <$> Gen.nat (.linear 1 1200)
  pure ⟨parent, ownValid, pow, number, timestamp⟩

/-- A reference for an update: a block of the tree mostly, the newest ones most of all. -/
def genRef (m : ForkchoiceModel) (zeroWeight : Nat) : Gen BlockRef :=
  let size := m.blocks.size
  if size == 0 then Gen.element [.unknown, .zero] else
  Gen.frequency [(4, BlockRef.known <$> Gen.nat (.constant 0 (size - 1))),
    (4, pure (.known (size - 1))), (zeroWeight, pure .zero), (1, pure .unknown)]

/-- A step: a new block, or an update whose safe and finalized blocks are often on the chain. -/
def genForkchoiceStep (m : ForkchoiceModel) : Gen ForkchoiceStep :=
  let update : Gen ForkchoiceStep := do
    let head ← genRef m 1
    let ancestor : Gen BlockRef := match head with
      | .known h =>
        let chain := m.chain h
        if chain.isEmpty then genRef m 3 else
        Gen.frequency [(6, BlockRef.known <$> Gen.element chain), (2, genRef m 3)]
      | _ => genRef m 3
    let (safe, finalized) ← Gen.zip ancestor ancestor
    pure (.update head safe finalized)
  Gen.frequency [(2, ForkchoiceStep.add <$> genModelBlock m), (3, update)]

/-- The reference of the choice of the head. -/
def forkchoiceModel : Model ForkchoiceModel ForkchoiceStep where
  initState := pure {}
  transitions := genForkchoiceStep
  apply := ForkchoiceModel.step
  preconditions m
    | .add block => m.blocks.size < 60000 &&
      (block.parent.all (· < m.blocks.size)) &&
      -- A block of proof of work never sits on a payload.
      (block.pow.isNone || (block.parent.bind (m.blocks[·]?)).all (·.pow.isSome))
    | .update _ _ _ => true

/-- The node as EthLib sees it: the tree, the head and the known finalized block. -/
structure ForkchoiceSut where
  tree : PayloadTree := []
  head : Option Hash32 := none
  finalized : Option Hash32 := none
  /-- How many blocks the tree holds, which names the next one. -/
  count : Nat := 0

/-- An answer of the model, as a status and a latest valid hash. -/
def Answer.status : Answer → Option PayloadStatus
  | .syncing => some ⟨.syncing, none⟩
  | .invalid latest => some ⟨.invalid, latest.map (·.hash)⟩
  | .valid _ => none
  | .invalidState => none

/-- The choice of the head against its model. -/
def forkchoiceMachine : StateMachine ForkchoiceModel ForkchoiceStep ForkchoiceSut IO where
  toModel := forkchoiceModel
  initSut _ := pure {}
  applySut sut m
    | .add block =>
      -- The model holds the block already, so its validity with its ancestors can be read.
      let known : KnownPayload := {
        parentHash := (block.parent.map hashOfIndex).getD unknownHash
        valid := m.isValid sut.count
        number := UInt64.ofNat block.number, timestamp := UInt64.ofNat block.timestamp
        powTotalDifficulty := block.pow }
      pure { sut with tree := sut.tree ++ [(hashOfIndex sut.count, known)], count := sut.count + 1 }
    | .update head safe finalized => do
      let state : ForkchoiceState := ⟨head.hash, safe.hash, finalized.hash⟩
      let got := forkchoiceUpdated testTransition sut.tree sut.finalized state
      let some expected := m.last | failWith "the model has no answer"
      annotate s!"the model answers {repr expected}"
      match expected, got with
      | .invalidState, .error (.invalidForkchoiceState s f) =>
        s === safe.hash
        f === finalized.hash
        pure sut
      | .valid applied, .ok (status, newHead) =>
        status === ⟨.valid, some head.hash⟩
        newHead === (if applied then some head.hash else none)
        if applied then
          pure { sut with head := some head.hash,
                          finalized := if finalized == .zero then sut.finalized
                            else some finalized.hash }
        else pure sut
      | other, .ok (status, newHead) =>
        some status === other.status
        newHead === none
        pure sut
      | _, .error e => failWith s!"EthLib answers the error {e.code}"
  invariants sut m := do
    sut.head === m.head.map hashOfIndex
    sut.finalized === m.finalized.map hashOfIndex

end EngineProperty

/-! ## The payload attributes of an update -/

namespace EngineProperty

open Lean (Json)

/-- The forks of the test chain whose attributes a version of the method takes.

Version 1 is of Paris and version 2 of Paris and Shanghai, before Cancun by `cancun.md`.

Version 3 takes Cancun and Prague by `prague.md`.

It also takes Osaka with its blob forks, which no later version takes.

`amsterdam.md` ends version 3 at Amsterdam, which version 4 takes. -/
def attributesTaken (version : Nat) (time : Nat) : Bool :=
  match version with
  | 1 => time < 1000
  | 2 => time < 2000
  | 3 => 2000 ≤ time && time < 7000
  | _ => 7000 ≤ time && time < 8000

/-- The version of the structure of the attributes at a time: the one of the fork of the time. -/
def structureAt (time : Nat) : Nat :=
  if time < 1000 then 1 else if time < 2000 then 2 else if time < 7000 then 3 else 4

/-- Another spelling of hexadecimal text: one that names the same value, or none at all. -/
def respell (how : String) (text : String) : Json :=
  let digits := String.ofList (text.toList.drop 2)
  match how with
  | "upper" => .str ("0x" ++ digits.toUpper)
  | "leadingZero" => .str ("0x0" ++ digits)
  | _ => .num 1

/-- Apply the damage of a case to the fields of an object. -/
def damageFields (fields : List (String × Json)) (drop nulls extra : List String)
    (replace : List (String × String)) : Json :=
  let fields := fields.filter fun (name, _) => !drop.contains name
  let fields := fields.map fun (name, value) =>
    if nulls.contains name then (name, Json.null)
    else match replace.lookup name, value with
      | some how, .str text => (name, respell how text)
      | _, _ => (name, value)
  Json.mkObj (fields ++ (extra.filter fun name => !fields.any (·.1 == name)).map (·, .str "0x1"))

/-- An update with payload attributes, on a node that holds one valid payload. -/
structure AttributesCase where
  version : Nat
  /-- The time of the head. -/
  headTime : Nat
  /-- Whether the node holds the head. -/
  headKnown : Bool
  /-- The parameters. -/
  params : Json
  /-- The attributes, as the second parameter holds them. -/
  attributes : Json
  /-- The forkchoice state, as the first parameter holds it. -/
  state : Json
  /-- The time of the attributes, when they are an object that names one. -/
  time : Nat

instance : Repr AttributesCase where
  reprPrec c _ := s!"version {c.version} head time {c.headTime} known {c.headKnown} " ++
    s!"params {c.params.compress}"

/-- The hash of the one payload of the node. -/
def headHash : Hash32 := hashOfIndex 7

/-- A case: attributes of the structure of the version at a time near a fork, or a near miss. -/
def genAttributesCase : Gen AttributesCase := do
  let version ← Gen.element [1, 2, 3, 4]
  let time ← Gen.frequency [(3, genTimeOf (if version == 4 then 5 else if version == 3 then 4
    else version)), (2, genForkTime), (1, Gen.nat (.constant 2000 2999))]
  let headTime ← Gen.frequency [(6, (time - ·) <$> Gen.nat (.linear 1 50)), (1, pure time),
    (1, pure (time + 1)), (1, Gen.nat (.linear 0 9000))]
  let own := if version == 2 then structureAt time else version
  let sv ← Gen.frequency [(8, pure own), (1, Gen.element [1, 2, 3, 4])]
  let word := genNatBits 64
  let (randao, root) ← Gen.zip genHash genHash
  let recipient ← genVector 20
  let withdrawals ← Gen.list (.linear 0 2)
    (Gen.zip word (Gen.zip word (Gen.zip (genVector 20) word)))
  let (slot, target) ← Gen.zip word word
  let quantity (n : Nat) : Json := .str ("0x" ++ String.ofList (Nat.toDigits 16 n))
  let fields : List (String × Json) :=
    [("timestamp", quantity time), ("prevRandao", .str (hex0x randao.toList)),
      ("suggestedFeeRecipient", .str (hex0x recipient.toList))] ++
    (if sv ≥ 2 then [("withdrawals", .arr (withdrawals.toArray.map fun (i, v, a, g) =>
      Json.mkObj [("index", quantity i), ("validatorIndex", quantity v),
        ("address", .str (hex0x a.toList)), ("amount", quantity g)]))] else []) ++
    (if sv ≥ 3 then [("parentBeaconBlockRoot", .str (hex0x root.toList))] else []) ++
    (if sv ≥ 4 then [("slotNumber", quantity slot), ("targetGasLimit", quantity target)] else [])
  let name := Gen.element EthLib.Engine.attributesFieldsV4
  let some1 (g : Gen String) : Gen (List String) :=
    Gen.frequency [(20, pure []), (1, List.singleton <$> g)]
  let (drop, nulls) ← Gen.zip (some1 name) (some1 name)
  let extra ← some1 (Gen.element ["foo", "slotNumber", "withdrawals", "parentBeaconBlockRoot"])
  let replace ← Gen.frequency [(15, pure []), (2, List.singleton <$>
    Gen.zip name (Gen.element ["upper", "upper", "leadingZero", "number"]))]
  let attributes ← Gen.frequency [(12, pure (damageFields fields drop nulls extra replace)),
    (2, pure Json.null), (1, Gen.element [Json.arr #[], .str "0x", .num 0, .bool false])]
  let headKnown ← Gen.frequency [(8, pure true), (1, pure false)]
  let head := if headKnown then headHash else unknownHash
  let hashJson (h : Hash32) : Json := .str (hex0x h.toList)
  let other ← Gen.frequency [(3, pure ZERO_HASH), (3, pure head)]
  let stateFields := [("headBlockHash", hashJson head), ("safeBlockHash", hashJson other),
    ("finalizedBlockHash", hashJson other)]
  let stateName := Gen.element ["headBlockHash", "safeBlockHash", "finalizedBlockHash"]
  let (sDrop, sNulls) ← Gen.zip (some1 stateName) (some1 stateName)
  let sReplace ← Gen.frequency [(25, pure []), (1, List.singleton <$>
    Gen.zip stateName (Gen.element ["upper", "leadingZero", "number"]))]
  let sExtra ← some1 (pure "foo")
  let state := damageFields stateFields sDrop sNulls sExtra sReplace
  let custody ← Gen.frequency [(4, pure []), (2, pure [Json.null]),
    (3, (fun (v : Vector UInt8 16) => [Json.str (hex0x v.toList)]) <$> genVector 16),
    (1, Gen.element [[Json.str "0x"], [.str ("0x" ++ String.ofList (List.replicate 30 '0'))],
      [.str ("0x" ++ String.ofList (List.replicate 34 '0'))], [.num 1], [.null, .null]])]
  let custody ← if version == 4 then pure custody else
    Gen.frequency [(15, pure []), (1, pure custody)]
  let shapeOk ← Gen.frequency [(25, pure true), (1, pure false)]
  let params := if shapeOk then Json.arr (#[state, attributes] ++ custody.toArray)
    else Json.arr #[state]
  pure { version, headTime, headKnown, params, attributes, state, time }

/-- The answer of EthLib to an update, as a word: an error code, or a status and whether an ID. -/
def attributesOutcome (c : AttributesCase) : String :=
  let known : KnownPayload := ⟨unknownHash, true, 20, UInt64.ofNat c.headTime, none⟩
  match forkchoiceUpdatedCall testConfig testTransition c.version [(headHash, known)] none
      c.params with
  | .error e => s!"E{e.code}"
  | .ok result =>
    let (status, id) := forkchoiceUpdatedResponse result
    s!"{status.status.name}{if id.isSome then "+id" else ""}"

/-- The answers that the specification allows to an update with payload attributes.

`stateShape` and `attributesShape` are the versions of the structures that the two values have.

The oracle gives each version, or 0. -/
def attributesAllowed (c : AttributesCase) (stateShape attributesShape : Nat) : List String :=
  let items := match c.params with
    | .arr items => items.toList
    | _ => []
  let custodyOk := match items.drop 2 with
    | [] => true
    | [.null] => c.version == 4
    | [.str text] => c.version == 4 && text.length == 34 && text.toList.take 2 == ['0', 'x'] &&
      (text.toList.drop 2).all fun ch => ch.isDigit || ('a' ≤ ch && ch ≤ 'f')
    | _ => false
  let attributesForm := match c.attributes with
    | .null | .obj _ => true
    | _ => false
  if items.length < 2 || !custodyOk || stateShape == 0 || !attributesForm then ["E32602"]
  else if !c.headKnown then ["SYNCING"]
  else if c.attributes.isNull then ["VALID"]
  else
    let structures := if c.version == 2 then [1, 2] else [c.version]
    if !structures.contains attributesShape then
      -- Versions 3 and 4 check the structure first; versions 1 and 2 give no order.
      if c.version ≥ 3 || attributesShape == 0 || attributesTaken c.version c.time then ["E38003"]
      else ["E38003", "E38005"]
    else
      let late := c.time ≤ c.headTime
      if !attributesTaken c.version c.time then
        if late then ["E38005", "E38003"] else ["E38005"]
      else if attributesShape != structureAt c.time && c.version == 2 then ["E38003"]
      else if late then ["E38003"]
      else ["VALID+id"]

/-- `engine_forkchoiceUpdated` answers payload attributes as its specification says.

Parameters that are not of the method are `-32602`.

Attributes count only for a valid head that is applied:

- A structure that the version does not take is `-38003`.
- A time in a fork that the version does not take is `-38005`.
- A time not above the head's is `-38003`.

Attributes that pass begin a build, and the answer names it. -/
def forkchoiceAttributes (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genAttributesCase
  pure do
    let stateShape := (← oracle.ask ["shape", "state", jsonHex c.state]).toNat!
    let attributesShape := (← oracle.ask ["shape", "attributes", jsonHex c.attributes]).toNat!
    let allowed := attributesAllowed c stateShape attributesShape
    let got := attributesOutcome c
    annotate s!"EthLib answers {got}; the specification allows {allowed}"
    ensure (allowed.contains got) "an answer that the specification does not allow"

end EngineProperty

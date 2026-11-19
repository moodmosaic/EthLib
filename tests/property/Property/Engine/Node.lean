import Property.Engine.Stores
import EthLib.Engine.GetPayload

/-!
# A node, driven by the methods of the Engine API

Each method is a command: `engine_newPayload`, `engine_forkchoiceUpdated` and `engine_getPayload`.

The state is the node.

It is the tree of payloads that EthLib reads, the builds, and the model beside them.

The model is the tree by index of the forkchoice state machine.

EthLib gives each method as a function of what the node holds.

So the commands hold the node together the way a client would:

- A payload that passes the checks enters the tree.
- An update moves the head.
- Attributes that pass begin a build.

The oracle writes every payload and its block hash.

So a build returned by `engine_getPayload` is compared with JSON that EthLib did not write.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Engine
open Lean (Json)

namespace EngineProperty

/-- A build of the node. -/
structure Build where
  id : PayloadId
  /-- The head and the attributes of the build, which name it in the model. -/
  key : String
  /-- The time of the payload. -/
  time : Nat
  /-- The index of the parent in the model. -/
  parent : Nat
  stored : StoredPayload
  /-- The parameters of `engine_newPayload` for the payload, as the oracle wrote them. -/
  params : Json
  /-- The version of `engine_newPayload` that takes the payload. -/
  version : Nat
  value : Nat
  requests : List (List UInt8)

/-- The node: the model, and what EthLib reads. -/
structure Node where
  model : ForkchoiceModel := {}
  /-- The block hash of each block of the model. -/
  hashes : Array Hash32 := #[]
  tree : PayloadTree := []
  head : Option Hash32 := none
  finalized : Option Hash32 := none
  builds : List Build := []
  deriving Inhabited

/-- The version of `engine_newPayload` for a payload at a time on the test chain. -/
def newPayloadVersionAt (time : Nat) : Nat :=
  if time < 1000 then 1 else if time < 2000 then 2 else if time < 3000 then 3
  else if time < 7000 then 4 else 5

/-- The version of `engine_forkchoiceUpdated` for attributes at a time on the test chain. -/
def forkchoiceVersionAt (time : Nat) : Nat :=
  if time < 1000 then 1 else if time < 2000 then 2 else if time < 7000 then 3 else 4

/-- The versions of `engine_getPayload` that return a payload built at a time on the test chain.

By `paris.md` to `amsterdam.md`, version 1 is for Paris, 2 for Paris and Shanghai, and 3 for Cancun.

Version 4 is for Prague, 5 for Osaka, and 6 for Amsterdam. -/
def getPayloadVersionsAt (time : Nat) : List Nat :=
  if time < 1000 then [1, 2] else if time < 2000 then [2] else if time < 3000 then [3]
  else if time < 4000 then [4] else if time < 7000 then [5] else if time < 8000 then [6] else []

/-- A version moved by a shift, within the versions that a method has. -/
def shifted (own : Nat) (shift : Int) (last : Nat) : Nat :=
  min last (max 1 (own + shift)).toNat

/-- The shift of a version: none mostly, so that most calls use the version of their fork. -/
def genShift : Gen Int := Gen.frequency [(8, pure 0), (1, pure (-1)), (1, pure 1), (1, pure 2)]

/-- A hash from a JSON string of the oracle. -/
def hashOfJson (j : Json) : Option Hash32 := (Serialization.JsonRpc.fixed "hash" 32 j).toOption

/-- The payload that the oracle writes for a case, with the answers allowed to the call. -/
def askPayload (oracle : Oracle) (c : NewPayloadCase) : TestT IO (List String × Json) := do
  let words := (← oracle.ask ["newpayload", jsonHex c.toJson]).splitOn " "
  match jsonOfHex (words.getD 1 "") with
  | .ok params => pure (words[0]!.splitOn "|", params)
  | .error e => failWith s!"{words}: {e}"

/-- A plain case: a payload at a time on a parent, with the structure of its fork, undamaged. -/
def plainCase (version time number : Nat) (parent : Hash32) (seeds : List Hash32)
    (txs : List String) (requests : List (List UInt8)) : NewPayloadCase :=
  { version, sv := structureAt time, number, timestamp := time
    gasLimit := 30000000, gasUsed := 0, baseFee := 7, blobGasUsed := 0, excessBlobGas := 0
    slot := number + 3, hashes := parent :: seeds
    feeRecipient := Vector.replicate 20 0xfe, bloomByte := 0, extraData := [1, 2, 3]
    txs, withdrawals := [], requests, accessList := "0xc0", expectedHashes := "match"
    hashDamage := false, drop := [], nulls := [], extra := [], replace := [], params := "ok" }

/-- Add a block that passed the checks to the node, unless the node holds it. -/
def Node.addBlock (node : Node) (hash : Hash32) (parent : Option Nat) (ownValid : Bool)
    (number time : Nat) : Node :=
  if node.hashes.contains hash then node else
  let model := { node.model with
    blocks := node.model.blocks.push ⟨parent, ownValid, none, number, time⟩ }
  let index := node.hashes.size
  let known : KnownPayload := {
    parentHash := (parent.bind (node.hashes[·]?)).getD unknownHash
    valid := model.isValid index
    number := UInt64.ofNat number, timestamp := UInt64.ofNat time, powTotalDifficulty := none }
  { node with model, hashes := node.hashes.push hash, tree := node.tree ++ [(hash, known)] }

/-- The block of the model that a selector names: the newest ones most often. -/
def Node.pick (node : Node) (selector : Nat) : Option Nat :=
  if node.hashes.isEmpty then none else some (node.hashes.size - 1 - selector % node.hashes.size)

/-! ## `engine_newPayload` -/

/-- A payload sent to the node, on a block that it holds or on one that it lacks. -/
structure NewPayloadCmd where
  oracle : Oracle
  /-- The parent: a selector of a block of the node, or none for a block that it lacks. -/
  parent : Option Nat
  /-- How far the time of the payload is above that of its parent. -/
  delta : Nat
  /-- The time below a payload on a parent that the node lacks: just before a fork, mostly. -/
  origin : Nat
  shift : Int
  txs : List String
  hashDamage : Bool
  /-- Whether the payload would pass its execution. -/
  ownValid : Bool
  seeds : List Hash32
  requests : List (List UInt8)

/-- A time step of a chain: a slot, or far enough to cross a fork of the test chain. -/
def genDelta : Gen Nat :=
  Gen.frequency [(4, Gen.nat (.constant 1 12)), (3, Gen.nat (.constant 300 700)),
    (2, Gen.element [999, 1000, 1001])]

instance : Command NewPayloadCmd Node Oracle IO where
  label c := s!"NEW_PAYLOAD(parent {c.parent}, origin {c.origin}, +{c.delta}s, " ++
    s!"shift {c.shift}, txs {c.txs}, " ++
    s!"hash damage {c.hashDamage}, valid {c.ownValid})"
  build oracle := do
    let parent ← Gen.frequency [(8, some <$> Gen.nat (.linear 0 6)), (1, pure none)]
    let (delta, shift) ← Gen.zip genDelta genShift
    let origin ← Gen.element [0, 990, 1990, 2990, 3990, 4990, 5990, 6990, 7990]
    let txs ← Gen.list (.linear 0 2)
      (Gen.element ["legacy", "dynamicFee", "accessList", "blob1", "setCode"])
    let (hashDamage, ownValid) ← Gen.zip (Gen.frequency [(12, pure false), (1, pure true)])
      (Gen.frequency [(6, pure true), (1, pure false)])
    let seeds ← Gen.list (.singleton 4) genHash
    let requests ← genRequests
    pure { oracle, parent, delta, origin, shift, txs, hashDamage, ownValid, seeds, requests }
  apply _ c node := do
    let parent := c.parent.bind node.pick
    let parentBlock := parent.bind (node.model.blocks[·]?)
    let number := (parentBlock.map (·.number + 1)).getD 10
    let time := (parentBlock.map (·.timestamp)).getD c.origin + c.delta
    let version := shifted (newPayloadVersionAt time) c.shift 5
    let parentHash := (parent.bind (node.hashes[·]?)).getD unknownHash
    let case := { plainCase version time number parentHash c.seeds c.txs c.requests with
      hashDamage := c.hashDamage }
    let (allowed, params) ← askPayload c.oracle case
    let got := newPayloadOutcome version params
    annotate s!"  version {version} at time {time}: {got}, allowed {allowed}"
    ensure (allowed.contains got) "newPayload: an answer that the specification does not allow"
    -- A payload that passes the checks is held.
    --
    -- Its execution, which the node of the tests does not run, says whether it is valid.
    if got != "SYNCING" then pure node else
    match params.getArrVal? 0 >>= (·.getObjVal? "blockHash") with
    | .ok hash =>
      let some hash := hashOfJson hash | failWith "the oracle wrote no block hash"
      pure (node.addBlock hash parent c.ownValid number time)
    | .error e => failWith e

/-! ## `engine_forkchoiceUpdated` -/

/-- A block that an update names. -/
inductive Selector where
  /-- A block of the node, by selector. -/
  | pick (selector : Nat)
  /-- The block some steps back on the chain of the head. -/
  | back (steps : Nat)
  | unknown
  | zero
  deriving Repr

/-- The payload attributes of an update, before the head fixes their time. -/
structure AttributesSpec where
  /-- The time of the attributes less that of the head. -/
  delta : Int
  /-- The shift of the version of the structure. -/
  structureShift : Int
  randao : Hash32
  root : Hash32
  withdrawals : List Nat
  deriving Repr

/-- A forkchoice update, with or without payload attributes. -/
structure ForkchoiceCmd where
  oracle : Oracle
  head : Selector
  safe : Selector
  finalized : Selector
  attributes : Option AttributesSpec
  shift : Int
  requests : List (List UInt8)

/-- The reference that a selector names on a node, for a head at an index. -/
def Node.resolve (node : Node) (head : Option Nat) : Selector → BlockRef
  | .pick selector => (node.pick selector).elim .unknown .known
  | .back steps =>
    match head with
    | some h =>
      let chain := node.model.chain h
      (chain[min steps (chain.length - 1)]?).elim .unknown .known
    | none => .unknown
  | .unknown => .unknown
  | .zero => .zero

/-- The hash that a reference names on a node. -/
def Node.hashOf (node : Node) : BlockRef → Hash32
  | .known i => node.hashes.getD i unknownHash
  | .unknown => unknownHash
  | .zero => ZERO_HASH

/-- The attributes of a specification at a time, as JSON of a version of their structure. -/
def AttributesSpec.json (a : AttributesSpec) (time sv : Nat) : Json :=
  Json.mkObj ([("timestamp", quantityText time), ("prevRandao", .str (hex0x a.randao.toList)),
      ("suggestedFeeRecipient", .str (hex0x (List.replicate 20 0xfe)))] ++
    (if sv ≥ 2 then [("withdrawals", .arr (a.withdrawals.toArray.map fun amount =>
      Json.mkObj [("index", quantityText amount), ("validatorIndex", quantityText (amount + 1)),
        ("address", .str (hex0x (List.replicate 20 (UInt8.ofNat amount)))),
        ("amount", quantityText amount)]))] else []) ++
    (if sv ≥ 3 then [("parentBeaconBlockRoot", .str (hex0x a.root.toList))] else []) ++
    (if sv ≥ 4 then [("slotNumber", quantityText (time / 12)),
      ("targetGasLimit", quantityText 30000000)] else []))
where
  quantityText (n : Nat) : Json := .str ("0x" ++ String.ofList (Nat.toDigits 16 n))

/-- The answers allowed to attributes on an applied head: step 8 of version 1 and its updates.

It is the table of `attributesAllowed`, for attributes that are well formed. -/
def attributesAnswers (version sv time headTime : Nat) : List String :=
  let structures := if version == 2 then [1, 2] else [version]
  let taken := attributesTaken version time
  if !structures.contains sv then
    if version ≥ 3 || taken then ["E38003"] else ["E38003", "E38005"]
  else
    let late := time ≤ headTime
    if !taken then (if late then ["E38005", "E38003"] else ["E38005"])
    else if sv != structureAt time && version == 2 then ["E38003"]
    else if late then ["E38003"]
    else ["VALID+id"]

/-- The empty state, which a stored build carries and `engine_getPayload` does not read. -/
def emptyState : Execution.State.State := ⟨∅, ∅, ∅⟩

instance : Command ForkchoiceCmd Node Oracle IO where
  label c := s!"FORKCHOICE_UPDATED(head {repr c.head}, safe {repr c.safe}, finalized " ++
    s!"{repr c.finalized}, attributes {repr c.attributes}, shift {c.shift})"
  build oracle := do
    let head ← Gen.frequency [(10, Selector.pick <$> Gen.nat (.linear 0 4)), (1, pure .unknown),
      (1, pure .zero)]
    let other := Gen.frequency [(6, Selector.back <$> Gen.nat (.linear 0 4)), (3, pure .zero),
      (1, Selector.pick <$> Gen.nat (.linear 0 4)), (1, pure .unknown)]
    let (safe, finalized) ← Gen.zip other other
    let spec : Gen AttributesSpec := do
      let delta ← Gen.frequency [(6, Gen.int (.constant 1 12)), (2, Gen.int (.constant 300 1100)),
        (1, pure 0), (1, pure (-1))]
      let structureShift ← Gen.frequency [(10, pure 0), (1, pure (-1)), (1, pure 1)]
      let (randao, root) ← Gen.zip genHash genHash
      let withdrawals ← Gen.list (.linear 0 2) (Gen.nat (.constant 0 200))
      pure { delta, structureShift, randao, root, withdrawals }
    let attributes ← Gen.frequency [(2, pure none), (5, some <$> spec)]
    let (shift, requests) ← Gen.zip genShift genRequests
    pure { oracle, head, safe, finalized, attributes, shift, requests }
  apply _ c node := do
    let head := node.resolve none c.head
    let headIndex := match head with
      | .known i => some i
      | _ => none
    let safe := node.resolve headIndex c.safe
    let finalized := node.resolve headIndex c.finalized
    let headBlock := headIndex.bind (node.model.blocks[·]?)
    let headTime := (headBlock.map (·.timestamp)).getD 0
    let time := (headTime + (c.attributes.map (·.delta)).getD 0).toNat
    let version := shifted (forkchoiceVersionAt time) c.shift 4
    let sv := shifted (structureAt time) ((c.attributes.map (·.structureShift)).getD 0) 4
    let attributes := c.attributes.map (·.json time sv)
    let hashJson (r : BlockRef) : Json := .str (hex0x (node.hashOf r).toList)
    let params := Json.arr #[Json.mkObj [("headBlockHash", hashJson head),
      ("safeBlockHash", hashJson safe), ("finalizedBlockHash", hashJson finalized)],
      attributes.getD .null]
    -- The model.
    let answer := node.model.answer head safe finalized
    let showHash (h : Option Hash32) : String := (h.map fun h => hex0x h.toList).getD "null"
    let allowed := match answer with
      | .syncing => ["SYNCING"]
      | .invalid latest => [s!"INVALID {showHash (latest.map node.hashOf)}"]
      | .invalidState => ["E38002"]
      | .valid false => ["VALID"]
      | .valid true => if attributes.isSome then attributesAnswers version sv time headTime
        else ["VALID"]
    -- EthLib.
    let result := forkchoiceUpdatedCall testConfig testTransition version node.tree node.finalized
      params
    let got := match result with
      | .error e => s!"E{e.code}"
      | .ok r =>
        let (status, id) := forkchoiceUpdatedResponse r
        match status.status with
        | .valid => if status.latestValidHash == some (node.hashOf head) then
            s!"VALID{if id.isSome then "+id" else ""}" else "VALID with another hash"
        | .invalid => s!"INVALID {showHash status.latestValidHash}"
        | other => other.name ++ (if id.isSome then "+id" else "")
    annotate s!"  version {version}, attributes {(attributes.map (·.compress)).getD "null"}"
    annotate s!"  the model answers {repr answer}: {got}, allowed {allowed}"
    ensure (allowed.contains got) "forkchoiceUpdated: an answer the specification does not allow"
    -- Step 8.3: an update with invalid attributes is not rolled back.
    let knownFinalized := match finalized with
      | .known f => some f
      | _ => node.model.finalized
    let node := match answer, headIndex with
      | .valid true, some h =>
        { node with
          model := { node.model with head := some h, finalized := knownFinalized }
          head := some (node.hashOf head)
          finalized := if finalized == .zero then node.finalized else some (node.hashOf finalized) }
      | _, _ => node
    node.head === node.model.head.map fun h => node.hashes.getD h unknownHash
    node.finalized === node.model.finalized.map fun f => node.hashes.getD f unknownHash
    -- A build begins: its ID names the head and the attributes, and no other build.
    match result, c.attributes, headIndex with
    | .ok r, some spec, some parent =>
      let some id := (forkchoiceUpdatedResponse r).2 | pure node
      let key := s!"{parent} {(attributes.map (·.compress)).getD ""}"
      match node.builds.find? (·.key == key) with
      | some build =>
        build.id === id
        pure node
      | none =>
        ensure (node.builds.all (·.id != id)) "two builds share a payload ID"
        -- The builder of the tests: the oracle writes the payload of the attributes.
        let number := (headBlock.map (·.number + 1)).getD 10
        let payloadVersion := newPayloadVersionAt time
        let case := { plainCase payloadVersion time number (node.hashOf head)
            [spec.randao, spec.randao, spec.randao, spec.root] [] c.requests with
          slot := time / 12
          withdrawals := spec.withdrawals.map fun amount =>
            (amount, amount + 1, Vector.replicate 20 (UInt8.ofNat amount), amount) }
        let (_, payloadParams) ← askPayload c.oracle case
        match checkNewPayload testConfig payloadVersion payloadParams with
        | .ok (.ok checked) =>
          let requests := if time ≥ 3000 then c.requests else []
          let value := time * 1000000007
          let stored : StoredPayload := {
            fork := checked.fork
            built := { block := checked.block, state := emptyState
                       requests := requests.map fun r => ⟨r.toArray⟩, blockValue := value }
            bundle := ⟨[], [], []⟩
            shouldOverrideBuilder := time % 2 == 0
            blockAccessList := fun _ => ⟨#[0xc0]⟩ }
          let build : Build := { id, key, time, parent, stored, params := payloadParams
                                 version := payloadVersion, value, requests }
          pure { node with builds := node.builds ++ [build] }
        | .ok (.error (status, _)) =>
          -- Requests that the generator damaged give no build; the build is then left out.
          annotate s!"  no build: the payload is {status.status.name}"
          pure node
        | .error e =>
          annotate s!"  no build: the payload gives the error {e.code}"
          pure node
    | _, _, _ => pure node

/-! ## `engine_getPayload` -/

/-- A request for the payload of a build of the node, or of no build. -/
structure GetPayloadCmd where
  /-- A selector of a build, or none for an ID that names no build. -/
  build : Option Nat
  shift : Int

/-- A trusted setup that the checks of an empty bundle do not read. -/
def emptySetup : Cryptography.Kzg.TrustedSetup :=
  ⟨Vector.replicate _ default, Vector.replicate _ default, Vector.replicate _ default⟩

/-- The fields of the result of a version, by `shanghai.md`, `cancun.md` and `prague.md`. -/
def resultFields (version : Nat) : List String :=
  if version == 1 then [] else
  ["blockValue", "executionPayload"] ++
    (if version ≥ 3 then ["blobsBundle", "shouldOverrideBuilder"] else []) ++
    (if version ≥ 4 then ["executionRequests"] else [])

instance : Command GetPayloadCmd Node Oracle IO where
  label c := s!"GET_PAYLOAD(build {c.build}, shift {c.shift})"
  build _ := do
    let build ← Gen.frequency [(10, some <$> Gen.nat (.linear 0 5)), (1, pure none)]
    let shift ← Gen.frequency [(6, pure 0), (1, pure (-1)), (1, pure 1), (1, pure (-2))]
    pure { build, shift }
  apply _ c node := do
    let build := c.build.bind fun selector =>
      if node.builds.isEmpty then none else node.builds[selector % node.builds.length]?
    let id : PayloadId := (build.map (·.id)).getD (Vector.replicate 8 0xee)
    let own := ((build.map fun b => getPayloadVersionsAt b.time).getD []).getLast?.getD 3
    let version := shifted own c.shift 6
    let store : PayloadStore := fun id => (node.builds.find? (·.id == id)).map (·.stored)
    let result := getPayload testConfig emptySetup store version id
    match build, result with
    | none, .error (.engine e) =>
      -- `paris.md`: `-38001: Unknown payload` if no build has the ID.
      s!"E{e.code}" === "E38001"
      pure node
    | none, _ => failWith "a payload of no build"
    | some b, result =>
      let taken := (getPayloadVersionsAt b.time).contains version
      annotate s!"  version {version}, built at time {b.time}"
      match result with
      | .error (.engine e) =>
        ensure (!taken) s!"the error {e.code} for a build that the version returns"
        s!"E{e.code}" === "E38005"
        pure node
      | .error _ => failWith "the stored build is refused"
      | .ok response =>
        ensure taken "a payload of a fork that the version does not return"
        let json := getPayloadResultJson (response.result version)
        annotate s!"  the result {json.compress}"
        let payload := if version == 1 then json else
          (json.getObjVal? "executionPayload").toOption.getD .null
        let expected := (b.params.getArrVal? 0).toOption.getD .null
        let text (name : String) : String :=
          ((json.getObjVal? name).toOption.map (·.compress)).getD "absent"
        payload.compress === expected.compress
        if version ≥ 2 then
          let fields : List String := match json with
            | Json.obj kvs => kvs.toList.map fun (p : String × Json) => p.1
            | _ => []
          fields.toArray.qsort (· < ·) === (resultFields version).toArray.qsort (· < ·)
          text "blockValue" === (quantityText b.value).compress
        if version ≥ 3 then
          text "shouldOverrideBuilder" === (Json.bool (b.time % 2 == 0)).compress
          text "blobsBundle" === "{\"blobs\":[],\"commitments\":[],\"proofs\":[]}"
        if version ≥ 4 then
          text "executionRequests" ===
            (Json.arr (b.requests.toArray.map fun r => .str (hex0x r))).compress
        -- The consensus node reads what the execution node wrote.
        match getPayloadResultOfJson version response.stored.fork json with
        | .ok _ => pure ()
        | .error e => failWith s!"the result does not read back: {e.code}"
        -- The payload goes back to the node, which must take it and hold it as a valid block.
        let got := newPayloadOutcome b.version b.params
        got === "SYNCING"
        let some hash := ((expected.getObjVal? "blockHash").toOption.bind hashOfJson)
          | failWith "the oracle wrote no block hash"
        let number := ((node.model.blocks[b.parent]?).map (·.number + 1)).getD 10
        pure (node.addBlock hash (some b.parent) true number b.time)

/-- The methods of the node, with a weight each: a list that names a command more than once. -/
def nodeCommands : List (Oracle → Node → Gen (CommandWrapper Node IO)) :=
  [Command.gen NewPayloadCmd, Command.gen NewPayloadCmd, Command.gen ForkchoiceCmd,
    Command.gen ForkchoiceCmd, Command.gen ForkchoiceCmd, Command.gen GetPayloadCmd,
    Command.gen GetPayloadCmd]

/-- The node answers every sequence of calls as the specification says: the madhouse scenario. -/
def nodeScenario (oracle : Oracle) : Property IO := scenario .madhouse oracle nodeCommands

/-- The same commands in sequences of up to 60 calls, which a chain needs to cross its forks. -/
def nodeLongScenario (oracle : Oracle) : Property IO :=
  scenario .madhouse oracle nodeCommands (.linear 1 60)

end EngineProperty

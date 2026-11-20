import Property.Engine.Forkchoice
import EthLib.Engine.PayloadBodies
import EthLib.Engine.GetBlobs
import EthLib.Engine.Capabilities

/-!
# The methods that read a store: payload bodies, blobs, capabilities

The bodies are a state machine: a chain that grows and is pruned, read by range and by hash.

Its model is a list of blocks by number, with the rules of `shanghai.md` and `amsterdam.md`.

The blob pool is read against a list, with the rules of `cancun.md`, `osaka.md` and `amsterdam.md`.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Engine
open Lean (Json)

namespace EngineProperty

/-! ## Payload bodies -/

/-- A quantity as the Engine API writes it, written here by hand. -/
def quantityText (n : Nat) : Json := .str ("0x" ++ String.ofList (Nat.toDigits 16 n))

/-- A block of the model of the body store. -/
structure ModelBody where
  /-- 0 for Paris, 1 for Shanghai, 2 for Amsterdam. -/
  era : Nat
  transactions : List (List UInt8)
  /-- The amount of each withdrawal. -/
  withdrawals : List Nat
  accessList : List UInt8
  /-- Whether the node still holds the body. -/
  held : Bool := true
  /-- Whether the node still holds the block access list. -/
  listHeld : Bool := true
  deriving Repr, BEq

/-- A step on the body store. -/
inductive BodyStep where
  | append (body : ModelBody)
  | prune (number : Nat)
  | pruneList (number : Nat)
  | byRange (version start count : Nat)
  /-- Bodies by hash: each a block by number, or a hash that the node lacks. -/
  | byHash (version : Nat) (blocks : List (Option Nat))
  deriving Repr, BEq

/-- The model: the canonical chain from block 0, and what the last request must answer. -/
structure BodyModel where
  chain : Array ModelBody
  /-- The answers that the specification allows to the last request. -/
  last : List String := []
  deriving Repr

/-- The most bodies that the node of the tests takes at once: the least the source allows. -/
def bodyLimit : Nat := 32

/-- The body of a block as the method of a version answers it, or `null` when not held.

`shanghai.md`: withdrawals are `null` before Shanghai.

`amsterdam.md`: the block access list is `null` before Amsterdam, or when pruned. -/
def ModelBody.json (version : Nat) (b : ModelBody) : Json :=
  if !b.held then .null else
  Json.mkObj ([("transactions", Json.arr (b.transactions.toArray.map fun t => .str (hex0x t))),
    ("withdrawals", if b.era == 0 then .null else .arr (b.withdrawals.toArray.map fun amount =>
      Json.mkObj [("index", quantityText amount), ("validatorIndex", quantityText (amount + 1)),
        ("address", .str (hex0x (List.replicate 20 (UInt8.ofNat amount)))),
        ("amount", quantityText amount)]))] ++
    if version == 2 then
      [("blockAccessList", if b.era == 2 && b.listHeld then .str (hex0x b.accessList) else .null)]
    else [])

namespace BodyModel

/-- The answers allowed to a request by range: `shanghai.md`, steps 1 to 4 of the method. -/
def rangeAnswers (m : BodyModel) (version start count : Nat) : List String :=
  let faults := (if start < 1 || count < 1 then ["E32602"] else []) ++
    (if count > bodyLimit then ["E38004"] else [])
  if !faults.isEmpty then faults else
  -- No entry past the latest known block, so no trailing null.
  let numbers := (List.range count).map (start + ·) |>.filter (· < m.chain.size)
  [(Json.arr (numbers.toArray.map fun n => (m.chain[n]?.map (·.json version)).getD .null)).compress]

/-- The answers allowed to a request by hash: `shanghai.md`, steps 1 to 3 of the method. -/
def hashAnswers (m : BodyModel) (version : Nat) (blocks : List (Option Nat)) : List String :=
  if blocks.length > bodyLimit then ["E38004"] else
  [(Json.arr (blocks.toArray.map fun
    | some n => (m.chain[n]?.map (·.json version)).getD .null
    | none => .null)).compress]

/-- The state after a step. -/
def step (m : BodyModel) : BodyStep → BodyModel
  | .append body => { chain := m.chain.push body }
  | .prune n => { chain := m.chain.modify n ({ · with held := false }) }
  | .pruneList n => { chain := m.chain.modify n ({ · with listHeld := false }) }
  | .byRange version start count => { m with last := m.rangeAnswers version start count }
  | .byHash version blocks => { m with last := m.hashAnswers version blocks }

end BodyModel

/-- A body for the chain, of an era no earlier than that of the block before it. -/
def genModelBody (m : BodyModel) : Gen ModelBody := do
  let era ← (max ((m.chain.back?.map (·.era)).getD 0) ·) <$> Gen.frequency [(3, pure 0),
    (1, pure 1), (1, pure 2)]
  let transactions ← Gen.list (.linear 0 3) (genByteList (.linear 1 4))
  let withdrawals ← Gen.list (.linear 0 2) (Gen.nat (.constant 0 200))
  let accessList ← Gen.frequency [(1, pure [0xc0]), (1, genByteList (.linear 0 5))]
  pure { era, transactions, withdrawals, accessList }

/-- A count or a start: small, at the limit of a request, at the end of the chain, or huge. -/
def genRangeNumber (m : BodyModel) : Gen Nat :=
  Gen.frequency [(6, Gen.nat (.constant 0 (m.chain.size + 2))),
    (2, Gen.element [0, 1, bodyLimit - 1, bodyLimit, bodyLimit + 1, m.chain.size - 1,
      m.chain.size]),
    (1, (2 ^ 64 - 1 - ·) <$> Gen.nat (.constant 0 2))]

/-- A step: the chain grows, a body or a list is pruned, or a request reads it. -/
def genBodyStep (m : BodyModel) : Gen BodyStep :=
  let number := Gen.nat (.constant 0 (m.chain.size - 1))
  let version := Gen.element [1, 2]
  Gen.frequency [(4, BodyStep.append <$> genModelBody m), (1, BodyStep.prune <$> number),
    (1, BodyStep.pruneList <$> number),
    (4, Gen.zipWith (fun v (s, c) => BodyStep.byRange v s c) version
      (Gen.zip (genRangeNumber m) (genRangeNumber m))),
    (2, Gen.zipWith BodyStep.byHash version (Gen.frequency [
      (8, Gen.list (.linear 0 6) (Gen.frequency [(4, some <$> number), (1, pure none)])),
      (1, Gen.list (.constant 32 33) (some <$> number))]))]

/-- The reference of the body store. -/
def bodyModel : Model BodyModel BodyStep where
  initState := (fun body => { chain := #[{ body with era := 0 }] }) <$>
    genModelBody { chain := #[] }
  transitions := genBodyStep
  apply := BodyModel.step
  preconditions m
    -- The node holds the body of its latest known block.
    | .prune n => n + 1 < m.chain.size
    | .pruneList n => n < m.chain.size
    | .append body => (m.chain.back?.map (·.era)).getD 0 ≤ body.era && body.held && body.listHeld
    | .byRange _ start count => start < 2 ^ 64 && count < 2 ^ 64
    | .byHash _ blocks => blocks.all fun b => b.all (· < m.chain.size)

/-- The fork of an era of the model. -/
def eraFork : Nat → Fork
  | 0 => .paris
  | 1 => .shapella
  | _ => .glamsterdam

/-- A body of the model as the store of EthLib holds it. -/
def ModelBody.stored (b : ModelBody) : StoredBody where
  fork := eraFork b.era
  transactions := b.transactions.map fun t => ⟨t.toArray⟩
  withdrawals := fun _ => b.withdrawals.map fun amount =>
    ⟨UInt64.ofNat amount, UInt64.ofNat (amount + 1), Vector.replicate 20 (UInt8.ofNat amount),
      UInt64.ofNat amount⟩
  blockAccessList := fun _ => if b.listHeld then some ⟨b.accessList.toArray⟩ else none

/-- The store of EthLib over the bodies that a node holds, when it holds the latest one. -/
def bodyStore (bodies : Array (Option StoredBody)) : Option BodyStore :=
  let canonical (n : Nat) : Option StoredBody := bodies[n]?.join
  let byHash (h : Hash32) : Option StoredBody :=
    ((List.range bodies.size).find? fun n => hashOfIndex n == h).bind canonical
  if held : (canonical (bodies.size - 1)).isSome then
    some { byHash, canonical, latest := bodies.size - 1, latest_held := held,
           maxRequest := bodyLimit, le_maxRequest := Nat.le_refl _ }
  else none

/-- An answer of EthLib, as a word: an error code, or the JSON of the bodies. -/
def bodiesWord {α : Type} (toJson : α → Json) : Except EngineError α → String
  | .ok bodies => (toJson bodies).compress
  | .error e => s!"E{e.code}"

/-- The body store against its model: the system is the array of the bodies that the node holds. -/
def bodyMachine : StateMachine BodyModel BodyStep (Array (Option StoredBody)) IO where
  toModel := bodyModel
  initSut m := pure (m.chain.map fun b => some b.stored)
  applySut sut _ m
    | .append body => pure (sut.push (some body.stored))
    | .prune n => pure (sut.set! n none)
    | .pruneList n => pure (sut.modify n (·.map fun b =>
        { b with blockAccessList := fun _ => none }))
    | step => do
      let some store := bodyStore sut | failWith "the node lacks its latest body"
      let got := match step with
        | .byRange 1 start count =>
          bodiesWord payloadBodiesV1Json
            (getPayloadBodiesByRangeV1 store (UInt64.ofNat start) (UInt64.ofNat count))
        | .byRange _ start count =>
          bodiesWord payloadBodiesV2Json
            (getPayloadBodiesByRangeV2 store (UInt64.ofNat start) (UInt64.ofNat count))
        | .byHash 1 blocks =>
          bodiesWord payloadBodiesV1Json (getPayloadBodiesByHashV1 store
            (blocks.map fun b => (b.map hashOfIndex).getD unknownHash))
        | .byHash _ blocks =>
          bodiesWord payloadBodiesV2Json (getPayloadBodiesByHashV2 store
            (blocks.map fun b => (b.map hashOfIndex).getD unknownHash))
        | _ => ""
      annotate s!"EthLib answers {got}; the specification allows {m.last}"
      ensure (m.last.contains got) "an answer that the specification does not allow"
      pure sut

end EngineProperty

/-! ## The blob pool -/

namespace EngineProperty

open EthLib.Cryptography.Kzg EthLib.Cryptography.Kzg.Constants

/-- What the model of the pool holds for a versioned hash. -/
inductive PoolEntry where
  /-- The blob, its proof, and each cell with its proof. -/
  | full
  /-- The blob with the proof of the whole blob only: the form before Osaka. -/
  | blobProofOnly
  /-- The blob and each cell, without the proof of the whole blob. -/
  | cellsOnly
  /-- No blob, and the cells whose index divides by `step`. -/
  | someCells (step : Nat)
  /-- A blob, and nothing with it. -/
  | bareBlob
  deriving Repr, BEq

/-- The byte that fills the blob of the entry at an index. -/
def blobByte (index : Nat) : UInt8 := UInt8.ofNat (index + 1)

/-- The byte that fills a cell of the entry at an index. -/
def cellByte (index cell : Nat) : UInt8 := UInt8.ofNat (16 * (index + 1) + cell % 16)

/-- Whether an entry holds the cell at an index. -/
def PoolEntry.holdsCell : PoolEntry → Nat → Bool
  | .full, _ | .cellsOnly, _ => true
  | .someCells step, i => i % step == 0
  | .blobProofOnly, _ | .bareBlob, _ => false

/-- Whether an entry holds its blob. -/
def PoolEntry.holdsBlob : PoolEntry → Bool
  | .someCells _ => false
  | _ => true

/-- Whether an entry holds the proof of its whole blob. -/
def PoolEntry.holdsBlobProof : PoolEntry → Bool
  | .full | .blobProofOnly => true
  | _ => false

/-- An entry of the model as the pool of EthLib holds it. -/
def PoolEntry.pooled (e : PoolEntry) (index : Nat) : PooledBlob where
  blob := if e.holdsBlob then some (Vector.replicate _ (blobByte index)) else none
  blobProof := if e.holdsBlobProof then some (Vector.replicate 48 (blobByte index)) else none
  cells := Vector.ofFn fun i => if e.holdsCell i.val then
    some (Vector.replicate _ (cellByte index i.val), Vector.replicate 48 (cellByte index i.val))
    else none

/-- The pool of EthLib over the entries of the model, with the least limit the source allows. -/
def blobPool (entries : Array PoolEntry) (serving : Bool) : BlobPool where
  lookup h := ((List.range entries.size).find? fun i => hashOfIndex i == h).bind fun i =>
    entries[i]?.map (·.pooled i)
  serving
  maxRequest := 128
  le_maxRequest := Nat.le_refl _

/-- A request for blobs: the pool, the fork of the node, the hashes and the cells asked for. -/
structure BlobsCase where
  entries : Array PoolEntry
  serving : Bool
  /-- Whether the node is at Osaka or later. -/
  osaka : Bool
  /-- Each hash: an entry by index, or a hash that the pool lacks. -/
  hashes : List (Option Nat)
  bits : Vector UInt8 16
  deriving Repr

/-- A pool of a few entries, and a request that names some of them, or 128 or 129 hashes. -/
def genBlobsCase : Gen BlobsCase := do
  let entries ← Gen.array (.linear 0 4) (Gen.frequency [(4, pure PoolEntry.full),
    (1, pure .blobProofOnly), (1, pure .cellsOnly),
    (1, PoolEntry.someCells <$> Gen.element [2, 3, 64, 127, 200]),
    (1, pure .bareBlob)])
  let one : Gen (Option Nat) := if entries.isEmpty then pure none else
    Gen.frequency [(6, some <$> Gen.nat (.constant 0 (entries.size - 1))), (1, pure none)]
  let hashes ← Gen.frequency [(12, Gen.list (.linear 0 5) one),
    (1, Gen.list (.constant 128 129) one)]
  let bits ← Gen.frequency [(2, genVector 16), (1, pure (Vector.replicate 16 0)),
    (1, pure (Vector.replicate 16 0xff)),
    (2, (fun (i, b) => (Vector.replicate 16 (0 : UInt8)).setIfInBounds i b) <$>
      Gen.zip (Gen.nat (.constant 0 15)) (Gen.element [1, 2, 0x80, 0x81]))]
  let (serving, osaka) ← Gen.zip (Gen.frequency [(5, pure true), (1, pure false)]) Gen.bool
  pure { entries, serving, osaka, hashes, bits }

/-- The entry that a requested hash names, with its index, when the pool serves and holds it. -/
def BlobsCase.entry (c : BlobsCase) (hash : Option Nat) : Option (Nat × PoolEntry) :=
  if c.serving then hash.bind fun i => c.entries[i]?.map (i, ·) else none

/-- The cells that a bitarray selects: bit `i` is bit `i % 8` of byte `i / 8`, from the least. -/
def BlobsCase.selected (c : BlobsCase) : List Nat :=
  (List.range 128).filter fun i => (c.bits.toList.getD (i / 8) 0).toNat / 2 ^ (i % 8) % 2 == 1

/-- An answer as a word: an error code, or what it shows. -/
def blobsWord {α : Type} (shown : α → String) : Except EngineError α → String
  | .ok x => shown x
  | .error e => s!"E{e.code}"

/-- `engine_getBlobs`, versions 1 to 4, reads the pool as the specification says.

Version 1 answers a blob and its proof or `null` for each hash, and `-38005` from Osaka.

Version 2 answers every blob with its cell proofs.

It answers `null` alone when one is missing or has only the proof of the whole blob.

Version 3 answers `null` at the place of each missing blob.

Version 4 answers the cells that the bitarray selects, and `null` for a cell that the pool lacks.

It answers `null` for a blob of which it holds no cell.

More hashes than the limit are `-38004`, and a pool that does not serve answers `null`. -/
def blobsRead : Property IO := pureIO do
  let c ← forAll genBlobsCase
  let pool := blobPool c.entries c.serving
  let hashes := c.hashes.map fun h => (h.map hashOfIndex).getD unknownHash
  let tooMany := c.hashes.length > 128
  let withProofs (e : Nat × PoolEntry) : Bool := e.2.holdsBlob && (List.range 128).all e.2.holdsCell
  -- Version 1.
  let expected1 := if c.osaka then "E38005" else if tooMany then "E38004" else
    toString (c.hashes.map fun h => (c.entry h).bind fun (i, e) =>
      if e.holdsBlob && e.holdsBlobProof then some (blobByte i) else none)
  blobsWord (fun r => toString (r.map (·.map fun (x : BlobAndProofV1) => x.blob[0]!)))
    (getBlobsV1 pool (if c.osaka then .fusaka else .pectra) hashes) === expected1
  -- Versions 2 and 3.
  let each := c.hashes.map fun h => (c.entry h).bind fun e =>
    if withProofs e then some (blobByte e.1, cellByte e.1 127) else none
  let expected2 := if tooMany then "E38004" else if !c.serving then "none" else
    toString (if each.all (·.isSome) then some (each.filterMap id) else none)
  blobsWord (fun r => toString (r.map (·.map fun (x : BlobAndProofV2) =>
      (x.blob[0]!, x.proofs[127][0]!))))
    (getBlobsV2 pool hashes) === expected2
  let expected3 := if tooMany then "E38004" else if !c.serving then "none" else toString (some each)
  blobsWord (fun r => toString (r.map (·.map (·.map fun (x : BlobAndProofV2) =>
      (x.blob[0]!, x.proofs[127][0]!)))))
    (getBlobsV3 pool hashes) === expected3
  -- Version 4.
  let cells := c.hashes.map fun h => (c.entry h).bind fun (i, e) =>
    if (List.range 128).any e.holdsCell then
      some (c.selected.map fun n => if e.holdsCell n then some (cellByte i n) else none)
    else none
  let expected4 := if tooMany then "E38004" else if !c.serving then "none" else
    toString (some cells)
  blobsWord (fun r => toString (r.map (·.map (·.map fun (x : BlobCellsAndProofsV1) =>
      x.cells.map (·.map fun (cell, proof) => if cell[0]! == proof[0]! then cell[0]! else 0)))))
    (getBlobsV4 pool hashes c.bits) === expected4

/-! ## Capabilities -/

/-- A name that is almost a method with its version. -/
def genMethodName : Gen String := do
  let method ← Gen.frequency [(4, Gen.element ["newPayload", "getBlobs", "x", "forkchoiceUpdated"]),
    (1, Gen.string (.linear 0 4) (Gen.frequency [(6, Gen.alpha), (1, Gen.element "_1 é".toList)]))]
  let version ← Gen.frequency [(4, toString <$> Gen.nat (.linear 1 120)),
    (1, Gen.element ["0", "01", "", "10", "1a", "١", "-1", "1 "])]
  let (prefix_, mark) ← Gen.zip
    (Gen.frequency [(8, pure "engine_"), (1, Gen.element ["Engine_", "engine", "eth_", ""])])
    (Gen.frequency [(8, pure "V"), (1, Gen.element ["v", "", "VV", "_V"])])
  pure (prefix_ ++ method ++ mark ++ version)

/-- A name is a method with its version exactly when it is `engine_`, letters, `V` and a version.

`common.md` asks that each name of the capability list carries its version. -/
def methodNames (oracle : Oracle) : Property IO := propertyM do
  let name ← forAll genMethodName
  pure do
    (if isVersionedMethod name then "ok" else "error") === (← oracle.ask ["method", textHex name])

/-- The methods that EthLib defines are those that the specification has a heading for.

`engine_exchangeCapabilities` is not one of them, as `common.md` asks of the answer. -/
def methodList (oracle : Oracle) : Property IO := propertyM do
  pure do
    let names := specifiedMethods.toArray.qsort (· < ·) |>.toList
    " ".intercalate names === (← oracle.ask ["methods"])
    ensure (specifiedMethods.all isVersionedMethod) "a name without its version"
    for (method, last) in methodVersions do
      for version in List.range (last + 2) do
        let name := s!"engine_{method}V{version}"
        methodVersion method name === (if 1 ≤ version && version ≤ last then some version else none)

end EngineProperty

/-! ## Structures of the responses, and the errors -/

namespace EngineProperty

/-- A structure that is almost one of a response: a status, a configuration, a client version. -/
def genResponse : Gen (String × Json) := do
  let (hash, word) ← Gen.zip genHash (genNatBits 64)
  let total ← genNatBits 256
  let status ← Gen.frequency [(5, Gen.element ["VALID", "INVALID", "SYNCING", "ACCEPTED",
    "INVALID_BLOCK_HASH"]), (1, Gen.element ["valid", "", "VALID ", "INVALID_BLOCKHASH"])]
  let code ← Gen.frequency [(4, Gen.string (.singleton 2) Gen.alpha),
    (1, Gen.string (.linear 0 3) Gen.alphaNum), (1, Gen.element ["G1", "é", "ÀB", "ge "])]
  let (name, fields) ← Gen.element [
    ("status", [("status", Json.str status), ("latestValidHash", .str (hex0x hash.toList)),
      ("validationError", .str "bad block")]),
    ("transition", [("terminalTotalDifficulty", quantityText total),
      ("terminalBlockHash", .str (hex0x hash.toList)), ("terminalBlockNumber", quantityText word)]),
    ("client", [("code", .str code), ("name", .str "client"), ("version", .str "v1.0.0+7"),
      ("commit", .str (hex0x (hash.toList.take 4)))])]
  let field := Gen.element (fields.map (·.1))
  let some1 (g : Gen String) : Gen (List String) :=
    Gen.frequency [(8, pure []), (1, List.singleton <$> g)]
  let (drop, nulls) ← Gen.zip (some1 field) (some1 field)
  let extra ← if name == "status" then pure [] else some1 (pure "foo")
  let replace ← Gen.frequency [(6, pure []), (1, List.singleton <$>
    Gen.zip field (Gen.element ["upper", "leadingZero", "number"]))]
  -- The validation error of a status is free text, which no spelling of hexadecimal changes.
  let replace := replace.filter fun (f, how) =>
    !(["validationError", "name", "version", "status", "code"].contains f && how != "number")
  pure (name, damageFields fields drop nulls extra replace)

/-- A structure of a response reads exactly when it has its fields, each of its type.

The structures:

- `PayloadStatusV1` and `TransitionConfigurationV1` of `paris.md`.
- `ClientVersionV1` of `identification.md`. -/
def responsesRead (oracle : Oracle) : Property IO := propertyM do
  let (name, value) ← forAllWith (fun (n, j) => s!"{n} {j.compress}") genResponse
  pure do
    let got := match name with
      | "status" => verdict (Json.payloadStatusOfJson value)
      | "transition" => verdict (transitionConfigurationOfJson value)
      | _ => verdict (clientVersionOfJson value)
    got === (← oracle.ask ["reads", name, jsonHex value])

/-- One error of each kind that a method of EthLib can return. -/
def errorSamples : List EngineError :=
  [.invalidParams "", .unsupportedFork none, .invalidForkchoiceState ZERO_HASH ZERO_HASH,
    .tooLargeRequest 0 0, .invalidPayloadAttributes, .unknownPayload (Vector.replicate 8 0),
    .tooDeepReorg]

/-- The table of Errors of `common.md`, for the codes that the Engine API adds and `-32602`. -/
def errorTable : List (Int × String) :=
  [(-32602, "Invalid params"), (-38001, "Unknown payload"), (-38002, "Invalid forkchoice state"),
    (-38003, "Invalid payload attributes"), (-38004, "Too large request"),
    (-38005, "Unsupported fork"), (-38006, "Too deep reorg")]

/-- Each error of EthLib has the code and the message of the table, and `null` data. -/
def errorsOfTable : Property IO := pureIO do
  for e in errorSamples do
    let rpc := e.toRpcError
    ensure (errorTable.contains (rpc.code, rpc.message)) s!"{rpc.code} {rpc.message}"
    ensure (rpc.data.any (·.isNull)) "data that is not null"
  UNDECIDED_TERMINAL_TOTAL_DIFFICULTY.toNat ===
    115792089237316195423570985008687907853269984665640564039457584007913129638912

/-- Each code that the table of `common.md` gives to the Engine API is an error of EthLib.

`-38006: Too deep reorg` is step 6 of `engine_forkchoiceUpdatedV1`. -/
def errorsComplete : Property IO := pureIO do
  for (code, message) in errorTable do
    ensure (errorSamples.any fun e => e.toRpcError.code == code) s!"no error {code}: {message}"

end EngineProperty

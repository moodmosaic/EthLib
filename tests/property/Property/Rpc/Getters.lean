import Property.Rpc.Chain

/-!
# The getters of a node: logs, receipts, blocks, transactions and raw forms

A request is JSON text, and goes through `ChainView.call`, so the readers of its parameters run.

The reference is `oracle/rpc_logs.py`, written from the schemas and the texts of execution-apis.

A request names a block or a transaction of the chain by a placeholder.

The test puts the hash in its place, once the oracle has signed the transactions.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Blocks EthLib.Execution.Transactions EthLib.Execution.Rpc
open Lean (Json)
open EthLib.Serialization.JsonRpc (RpcError)

namespace RpcProperty

/-! ## Requests with placeholders -/

/-- The text of a hash of 32 bytes as JSON. -/
def hashText (hash : String) : String := s!"\"0x{hash}\""

/-- A hash that no block and no transaction has. -/
def unknownHash : String := hashText (hexVec (Vector.replicate 32 0xab : Hash32))

/-- The hash of the transaction at an index of a block, or an unknown one. -/
def txHashText (built : Built) (block index : Nat) : String :=
  match built.records[block]? with
  | some r =>
    match r.block.transactions[index]? with
    | some tx =>
      match transactionHash tx with
      | .ok hash => hashText (hexVec hash)
      | .error _ => unknownHash
    | none => unknownHash
  | none => unknownHash

/-- The text of a request with the hashes of the chain in the place of its placeholders.

`@B3@` is the hash of the fourth block, and `@T3.1@` that of its second transaction.

A block or a transaction that the chain lacks gives an unknown hash. -/
def resolve (built : Built) (text : String) : String :=
  let parts := text.splitOn "@"
  String.join (parts.zipIdx.map fun (part, i) =>
    if i % 2 = 0 then part
    else if part.startsWith "B" then
      match (part.drop 1).toString.toNat? with
      | some n => ((built.hashes[n]?).map hashText).getD unknownHash
      | none => unknownHash
    else
      match (part.drop 1).toString.splitOn "." with
      | [b, t] => txHashText built b.toNat! t.toNat!
      | _ => unknownHash)

/-- A block of the chain by its number or a tag, as the text of JSON. -/
def genNumberOrTag (c : ChainSpec) : Gen String :=
  let low := (c.blocks.head?.map (·.header.number)).getD 0
  let head := (c.blocks.getLast?.map (·.header.number)).getD 0
  Gen.frequency [
    (5, (fun n => s!"\"0x{hexNat n}\"") <$> Gen.nat (.constant low head)),
    (3, (fun t => s!"\"{t}\"") <$> Gen.element ["latest", "earliest", "safe", "finalized",
      "pending"]),
    (1, (fun n => s!"\"0x{hexNat n}\"") <$> Gen.element [head + 1, head + 2, low - 1])]

/-- A block of the chain by a placeholder of its hash: canonical, off the chain, or unknown. -/
def genBlockHash (c : ChainSpec) : Gen String :=
  let held := c.blocks.length + c.side.length + (if c.pending.isSome then 1 else 0)
  Gen.frequency [(8, (fun i => s!"@B{i}@") <$> Gen.nat (.constant 0 (held - 1))),
    (1, pure "@B999@")]

/-- A transaction of the chain by a placeholder of its hash, or an unknown one. -/
def genTxHash (c : ChainSpec) : Gen String := do
  let held := c.blocks.length + c.side.length
  let block ← Gen.nat (.constant 0 (held - 1))
  let count := (((c.blocks ++ c.side)[block]?).map (·.txs.length)).getD 0
  let index ← Gen.frequency [(8, Gen.nat (.constant 0 (count - 1))), (1, pure count)]
  pure s!"@T{block}.{index}@"

/-! ## Logs -/

/-- The text of an address as JSON. -/
def addressText (a : Address) : String := s!"\"0x{hexVec a}\""

/-- The text of a topic as JSON. -/
def topicText (t : Nat) : String := hashText (hexVec (word32 t))

/-- The addresses of a filter: none, one, a list, and sometimes a text that is no address. -/
def genAddressFilter : Gen (Option String) :=
  let known := Gen.element (logAddresses ++ [addressOf 0x99 0x99])
  Gen.frequency [
    (4, pure none),
    (1, pure (some "null")),
    (3, (fun a => some (addressText a)) <$> known),
    (3, (fun l => some s!"[{", ".intercalate (l.map addressText)}]") <$>
      Gen.list (.constant 0 3) known),
    -- An address may be in upper case, by its pattern in base-types.yaml.
    (1, pure (some "\"0xC505C505C505C505C505C505C505C505C505C505\"")),
    (1, Gen.frequency [(3, pure none), (1, Gen.element [some "\"0xc505\"", some "5",
      some "[null]", some "\"c505c505c505c505c505c505c505c505c505c505\""])])]

/-- What a filter takes at one position of the topics. -/
def genTopicEntry : Gen String :=
  let known := Gen.element (logTopics ++ [9])
  Gen.frequency [
    (5, pure "null"),
    (3, topicText <$> known),
    (2, pure "[]"),
    (4, (fun l => s!"[{", ".intercalate (l.map topicText)}]") <$> Gen.list (.constant 1 4) known)]

/-- The topics of a filter: none, a list of up to five positions, or a text that is no topic. -/
def genTopicsFilter : Gen (Option String) :=
  Gen.frequency [
    (4, pure none),
    (1, pure (some "null")),
    (5, (fun l => some s!"[{", ".intercalate l}]") <$> Gen.list (.constant 0 2) genTopicEntry),
    (3, (fun l => some s!"[{", ".intercalate l}]") <$> Gen.list (.constant 3 5) genTopicEntry),
    (1, Gen.frequency [(3, pure none), (1, Gen.element [some "[\"0x01\"]", some "[[null]]",
      some s!"{topicText 1}",
      some "[\"0x000000000000000000000000000000000000000000000000000000000000000A\"]"])])]

/-- A number as the text of a JSON quantity. -/
def quantityText (n : Nat) : String := s!"\"0x{hexNat n}\""

/-- The bounds of a range: mostly in order and within the chain, sometimes not. -/
def genBounds (c : ChainSpec) : Gen (Option String × Option String) := do
  let low := (c.blocks.head?.map (·.header.number)).getD 0
  let head := (c.blocks.getLast?.map (·.header.number)).getD 0
  let a ← Gen.nat (.constant low head)
  let b ← Gen.nat (.constant low head)
  let tag ← Gen.element ["latest", "earliest", "safe", "finalized"]
  let odd ← Gen.element ["null", "\"pending\"", "\"0x00\"", "7", quantityText (head + 1),
    quantityText (head + 5), quantityText (low - 1)]
  Gen.frequency [
    (6, pure (some (quantityText (min a b)), some (quantityText (max a b)))),
    (2, pure (some (quantityText low), none)),
    (2, pure (none, none)),
    (1, pure (some (quantityText a), some (quantityText b))),
    (1, pure (some (quantityText a), some s!"\"{tag}\"")),
    (1, pure (some s!"\"{tag}\"", some (quantityText b))),
    (1, pure (some s!"\"{tag}\"", none)),
    (1, pure (some odd, some (quantityText b))),
    (1, pure (some (quantityText a), some odd))]

/-- A filter as the text of JSON, with a placeholder for the hash of a block. -/
def genFilter (c : ChainSpec) : Gen String := do
  let address ← genAddressFilter
  let topics ← genTopicsFilter
  let byHash ← Gen.frequency [(3, pure none), (1, some <$> genBlockHash c)]
  let (fromBlock, toBlock) ← genBounds c
  -- A filter by hash has no bound, but for one in eight.
  let bounded ← Gen.frequency [(7, pure false), (1, pure true)]
  let range := [("fromBlock", fromBlock), ("toBlock", toBlock)]
  let members := [("address", address), ("topics", topics)] ++
    (match byHash with
      | some hash => [("blockHash", some hash)] ++ (if bounded then range else [])
      | none => range)
  let written := members.filterMap fun (name, value) => value.map fun v => s!"\"{name}\": {v}"
  pure ("{" ++ ", ".intercalate written ++ "}")

/-- The logs of a filter are those that a scan of the receipts selects.

A range that reaches past the head or runs backwards gets the code of invalid parameters.

So does a filter by hash with a bound, and a field that does not read. -/
def getLogs (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genChainSpec
  let filter ← forAll (genFilter c)
  pure do
    let built ← c.build oracle
    let text := resolve built filter
    let params ← orFail (Json.parse s!"[{text}]")
    let got := built.view.call "eth_getLogs" (params.getArr?.toOption.getD #[]).toList
    let want ← oracle.ask (["rpc"] ++ c.words ++ ["eth_getLogs", s!"[{text}]"])
    let ended ← sameAnswer got want
    let logs := (c.blocks.map fun b => (b.txs.map (·.logs.length)).sum).sum
    classify "the chain has a log" (logs > 0)
    classify "the chain has three blocks or more" (c.blocks.length ≥ 3)
    if ended ≠ "ok" then classify s!"refused: {ended}" true
    let count := match got with
      | .ok (.arr items) => items.size
      | _ => 0
    cover 50 "answered" (ended = "ok")
    cover 15 "the filter selects a log" (count > 0)
    classify "the filter selects some logs of its blocks and leaves others"
      (0 < count ∧ count < logs)
    classify "the filter selects two logs or more" (count ≥ 2)
    classify "a filter by hash is answered" (ended = "ok" ∧ (filter.splitOn "blockHash").length > 1)
    classify "a filter with topics selects a log"
      (count > 0 ∧ (filter.splitOn "\"topics\": [").length > 1 ∧
        (filter.splitOn "\"topics\": []").length = 1)
    classify "a filter with addresses selects a log"
      (count > 0 ∧ (filter.splitOn "\"address\": [\"").length > 1)

/-! ## Receipts, blocks, transactions and raw forms -/

/-- A request of a getter: its method, and its parameters as text with placeholders. -/
def genGetter (c : ChainSpec) : Gen (String × String) := do
  let block ← genNumberOrTag c
  let hash ← genBlockHash c
  let tx ← genTxHash c
  let full ← Gen.element ["true", "false"]
  let index ← (fun n => s!"\"0x{hexNat n}\"") <$> Gen.nat (.constant 0 4)
  let canonical ← Gen.element ["true", "false"]
  let either ← Gen.element [block, hash, s!"\{\"blockHash\": {hash}}",
    s!"\{\"blockHash\": {hash}, \"requireCanonical\": {canonical}}",
    s!"\{\"blockNumber\": {block}}"]
  Gen.element [
    ("eth_getTransactionReceipt", s!"[{tx}]"),
    ("eth_getTransactionReceipt", s!"[{tx}]"),
    ("eth_getBlockReceipts", s!"[{either}]"),
    ("eth_getBlockReceipts", s!"[{either}]"),
    ("eth_getTransactionByHash", s!"[{tx}]"),
    ("eth_getTransactionByBlockHashAndIndex", s!"[{hash}, {index}]"),
    ("eth_getTransactionByBlockNumberAndIndex", s!"[{block}, {index}]"),
    ("eth_getBlockByNumber", s!"[{block}, {full}]"),
    ("eth_getBlockByNumber", s!"[{block}, true]"),
    ("eth_getBlockByHash", s!"[{hash}, {full}]"),
    ("eth_getHeaderByNumber", s!"[{block}]"),
    ("eth_getHeaderByHash", s!"[{hash}]"),
    ("eth_getBlockTransactionCountByNumber", s!"[{block}]"),
    ("eth_getBlockTransactionCountByHash", s!"[{hash}]"),
    ("debug_getRawHeader", s!"[{block}]"),
    ("debug_getRawBlock", s!"[{block}]"),
    ("debug_getRawReceipts", s!"[{either}]"),
    ("debug_getRawTransaction", s!"[{tx}]"),
    ("eth_blockNumber", "[]")]

/-- A getter answers the object that the schemas of execution-apis give.

A block, a header, a transaction and a receipt have the fields of their fork and their type.

A raw form is the consensus encoding.

A block or a transaction that the node lacks gives `null`, or an error for a raw form. -/
def getters (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genChainSpec
  let (method, params) ← forAll (genGetter c)
  pure do
    let built ← c.build oracle
    let text := resolve built params
    let json ← orFail (Json.parse text)
    let got := built.view.call method (json.getArr?.toOption.getD #[]).toList
    let want ← oracle.ask (["rpc"] ++ c.words ++ [method, text])
    let ended ← sameAnswer got want
    let found := ended = "ok" ∧ want ≠ "null"
    cover 40 "the getter finds what it asks for" found
    classify "the getter answers null" (want = "null")
    if ended ≠ "ok" then classify s!"refused: {ended}" true
    if found then classify s!"found: {method}" true
    let forksOf := (c.blocks.map (·.fork)).eraseDups
    classify "a chain before Byzantium" (forksOf.any (· < .byzantium))
    classify "a chain before London" (forksOf.any (· < .london))
    classify "a chain from Dencun" (forksOf.any (· ≥ .dencun))
    classify "a chain of two forks" (forksOf.length > 1)

end RpcProperty

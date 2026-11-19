import Property.Engine.Common
import EthLib.Engine.NewPayload

/-!
# `engine_newPayload`, versions 1 to 5, before execution

A case names a version of the method, a payload at a time on a test chain, and what is done to the
request.
The oracle writes the parameters, with the block hash that it computes, and the answers that the
specification allows.
So the matrix of version, fork and structure, the forms of the fields, and the header hash at
each fork are checked against a reference that shares no code with EthLib.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Engine
open Lean (Json)

namespace EngineProperty

/-- The chain of the tests: London from block 0, Paris from block 10, then a fork each 1000 s.

`oracle/engine_payload.py` holds the same table. -/
def testConfig : ChainConfig where
  chainId := 1
  depositContractAddress := Vector.replicate 20 0
  activations := [(.london, .block 0), (.paris, .block 10), (.shapella, .time 1000),
    (.dencun, .time 2000), (.pectra, .time 3000), (.fusaka, .time 4000), (.bpo1, .time 5000),
    (.bpo2, .time 6000), (.glamsterdam, .time 7000), (.hegota, .time 8000)]

/-- The time from which each fork of the test chain is active. -/
def forkTimes : List Nat := [1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000]

/-- A time on the test chain: at a fork boundary, one second either side of it, or any. -/
def genForkTime : Gen Nat :=
  Gen.frequency [
    (6, Gen.zipWith (fun t d => t + d - 1) (Gen.element forkTimes) (Gen.nat (.constant 0 2))),
    (3, Gen.nat (.linear 0 9000)), (1, Gen.nat (.exponential 0 (2 ^ 64 - 1)))]

/-- A time in the forks that a version of `engine_newPayload` takes, near their ends. -/
def genTimeOf (version : Nat) : Gen Nat :=
  let (low, high) := match version with
    | 1 => (0, 999) | 2 => (0, 1999) | 3 => (2000, 2999) | 4 => (3000, 6999) | _ => (7000, 7999)
  Gen.frequency [(1, pure low), (1, pure high), (3, Gen.nat (.constant low high))]

/-- A block number: from Paris on mostly, or before it, where no version takes the payload. -/
def genNumber : Gen Nat :=
  Gen.frequency [(12, Gen.nat (.linear 10 1000)), (1, Gen.nat (.constant 0 9)), (1, pure 9),
    (1, pure 10), (1, (2 ^ 64 - 1 - ·) <$> Gen.nat (.linear 0 3))]

/-- `0x` and the digits of bytes. -/
def hex0x (bytes : List UInt8) : String := "0x" ++ digitsOf bytes

/-- A number as the oracle takes it: decimal text, since a JSON number may lose digits. -/
def decimal (n : Nat) : Json := .str (toString n)

/-- The name of a transaction that the oracle signed.

Mostly it is one that the forks of the version take; a blob transaction before Dencun, a set-code
transaction before Pectra, and bytes that are no transaction are the near misses. -/
def genTxName (version : Nat) : Gen String :=
  let early := ["legacy", "accessList", "dynamicFee"]
  let own := early ++ (if version ≥ 3 then ["blob1", "blob2"] else []) ++
    (if version ≥ 4 then ["setCode"] else [])
  Gen.frequency [(20, Gen.element own), (2, Gen.element ["blob1", "blob2", "setCode"]),
    (1, Gen.element ["empty", "unknownType", "truncated"])]

/-- Request lists: types that rise and data of a byte or more, or a near miss of that. -/
def genRequests : Gen (List (List UInt8)) := do
  let types ← Gen.subsequence [0, 1, 2, 3, 127, 255]
  let lists ← types.mapM fun t => (t :: ·) <$> genByteList (.linear 1 3)
  Gen.frequency [(20, pure lists), (1, pure lists.reverse), (1, pure (lists ++ lists.take 1)),
    (1, pure ([0] :: lists.drop 1)), (1, pure (lists ++ [[]])), (1, pure (lists.take 1 ++ lists)),
    (1, pure (lists ++ [[255]]))]

/-- The field names of version 4 of the payload structure. -/
def payloadFieldNames : List String := Json.payloadFieldsV4

/-- A call of `engine_newPayload`: the payload, and what is done to the request. -/
structure NewPayloadCase where
  version : Nat
  /-- The version of the structure whose fields the payload holds, before the damage. -/
  sv : Nat
  number : Nat
  timestamp : Nat
  gasLimit : Nat
  gasUsed : Nat
  baseFee : Nat
  blobGasUsed : Nat
  excessBlobGas : Nat
  slot : Nat
  hashes : List Hash32
  feeRecipient : Vector UInt8 20
  bloomByte : UInt8
  extraData : List UInt8
  txs : List String
  withdrawals : List (Nat × Nat × Vector UInt8 20 × Nat)
  requests : List (List UInt8)
  accessList : String
  expectedHashes : String
  hashDamage : Bool
  drop : List String
  nulls : List String
  extra : List String
  replace : List (String × String)
  params : String
  deriving Repr

/-- The case as the oracle reads it. -/
def NewPayloadCase.toJson (c : NewPayloadCase) : Json :=
  let hash (i : Nat) : Json := .str (hex0x (c.hashes.getD i (Vector.replicate 32 0)).toList)
  let strings (xs : List String) : Json := .arr (xs.toArray.map .str)
  Json.mkObj [
    ("version", c.version), ("sv", c.sv),
    ("common", Json.mkObj [
      ("parentHash", hash 0), ("feeRecipient", .str (hex0x c.feeRecipient.toList)),
      ("stateRoot", hash 1), ("receiptsRoot", hash 2),
      ("logsBloom", .str (hex0x (List.replicate 256 c.bloomByte))), ("prevRandao", hash 3),
      ("blockNumber", decimal c.number), ("gasLimit", decimal c.gasLimit),
      ("gasUsed", decimal c.gasUsed), ("timestamp", decimal c.timestamp),
      ("extraData", .str (hex0x c.extraData)), ("baseFeePerGas", decimal c.baseFee)]),
    ("txs", strings c.txs),
    ("withdrawals", .arr (c.withdrawals.toArray.map fun (i, v, a, g) =>
      .arr #[decimal i, decimal v, .str (hex0x a.toList), decimal g])),
    ("blobGasUsed", decimal c.blobGasUsed), ("excessBlobGas", decimal c.excessBlobGas),
    ("root", hash 4), ("requests", strings (c.requests.map hex0x)),
    ("bal", .str c.accessList), ("slot", decimal c.slot),
    ("hashes", .str c.expectedHashes), ("hashDamage", .bool c.hashDamage),
    ("drop", strings c.drop), ("nulls", strings c.nulls), ("extra", strings c.extra),
    ("replace", .arr (c.replace.toArray.map fun (name, how) => .arr #[.str name, .str how])),
    ("params", .str c.params)]

/-- A call that is valid for its version, or one step from it.

The structure is the one the version takes at the time, mostly, and the time is in a fork that
the version takes, mostly: a call reaches the later checks only when the earlier ones pass. -/
def genNewPayloadCase : Gen NewPayloadCase := do
  let version ← Gen.element [1, 2, 3, 4, 5]
  let timestamp ← Gen.frequency [(3, genTimeOf version), (2, genForkTime)]
  let own := match version with
    | 1 => 1 | 2 => if timestamp < 1000 then 1 else 2 | 3 | 4 => 3 | _ => 4
  let sv ← Gen.frequency [(8, pure own), (1, Gen.element [1, 2, 3, 4])]
  let number ← genNumber
  let word := genNatBits 64
  let ((gasLimit, gasUsed), (blobGasUsed, excessBlobGas), slot, baseFee) ←
    Gen.zip (Gen.zip word word) (Gen.zip (Gen.zip word word) (Gen.zip word (genNatBits 256)))
  let hashes ← Gen.list (.singleton 5) genHash
  let (feeRecipient, bloomByte) ← Gen.zip (genVector 20) (Gen.frequency [(3, pure 0), (1, genByte)])
  let extraData ← Gen.element [0, 1, 31, 32, 32, 33] >>= fun n => genByteList (.singleton n)
  let txs ← Gen.frequency [(2, pure []), (5, Gen.list (.linear 0 4) (genTxName version))]
  let withdrawals ← Gen.list (.linear 0 3)
    (Gen.zip word (Gen.zip word (Gen.zip (genVector 20) word)))
  let requests ← genRequests
  let accessList ← Gen.frequency [(10, pure "0xc0"), (1, Gen.element ["0x", "0xc1", "0xc000",
    "0x80", "0x01"])]
  let expectedHashes ← Gen.frequency [(10, pure "match"),
    (2, Gen.element ["drop", "extra", "reverse", "flip"])]
  let hashDamage ← Gen.frequency [(10, pure false), (1, pure true)]
  let field := Gen.element payloadFieldNames
  let some1 (g : Gen String) : Gen (List String) :=
    Gen.frequency [(15, pure []), (1, List.singleton <$> g)]
  let (drop, nulls) ← Gen.zip (some1 field) (some1 field)
  let extra ← some1 (Gen.element ["foo", "slotNumber", "blockAccessList", "withdrawals",
    "excessBlobGas", "blockhash"])
  let replace ← Gen.frequency [(12, pure []), (2, List.singleton <$>
    Gen.zip field (Gen.element ["upper", "upper", "leadingZero", "number"]))]
  let params ← Gen.frequency [(20, pure "ok"), (1, Gen.element ["short", "long", "nullLast",
    "object"])]
  pure { version, sv, number, timestamp, gasLimit, gasUsed, baseFee, blobGasUsed, excessBlobGas,
         slot, hashes, feeRecipient, bloomByte, extraData, txs, withdrawals, requests, accessList,
         expectedHashes, hashDamage, drop, nulls, extra, replace, params }

/-- What EthLib answers to a call without the parent's state, as the oracle names it. -/
def newPayloadOutcome (version : Nat) (params : Json) : String :=
  match newPayloadWithoutState testConfig version params with
  | .error e => s!"E{e.code}"
  | .ok (status, _) =>
    if status.latestValidHash.isSome then "a latest valid hash" else status.status.name

/-- The JSON that the oracle wrote, from its hexadecimal text. -/
def jsonOfHex (word : String) : Except String Json := do
  let some bytes := unhex? word | throw "the oracle wrote no hexadecimal"
  let some text := String.fromUTF8? bytes | throw "the oracle wrote no UTF-8"
  Json.parse text

/-- `engine_newPayload` answers a call as its specification says.

A request that is not of its version is `-32602`, a payload of a fork that the version does not
take is `-38005`, and a payload that fails a check of the payload alone is `INVALID`, or
`INVALID_BLOCK_HASH` for a wrong block hash in version 1, with no latest valid hash.
A payload that passes them all is `SYNCING` at a node without the parent's state.
So the block hash that EthLib computes at each fork is the one of the reference. -/
def newPayloadMatrix (oracle : Oracle) : Property IO := propertyM do
  let c ← forAllWith (fun c => c.toJson.compress) genNewPayloadCase
  pure do
    let words := (← oracle.ask ["newpayload", jsonHex c.toJson]).splitOn " "
    let allowed := words[0]!.splitOn "|"
    match jsonOfHex (words.getD 1 "") with
    | .error e => failWith s!"{words}: {e}"
    | .ok params =>
      let got := newPayloadOutcome c.version params
      annotate s!"params {params.compress}"
      annotate s!"EthLib answers {got}; the specification allows {allowed}"
      ensure (allowed.contains got) "an answer that the specification does not allow"

end EngineProperty

import Property.Rpc.Chain

/-!
# eth_call and eth_estimateGas

A call runs the message of a request on the state after a block, and commits nothing.

The view here is one to three blocks at one fork, and the block of the call has a state.

The request is the JSON text of a call object, and goes through `ChainView.call`.

The reference is `oracle/rpc_call.py`: the choices that `Call.lean` writes down, and EELS.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Blocks EthLib.Execution.Transactions EthLib.Execution.Rpc
open Lean (Json)
open EthLib.Serialization.JsonRpc (RpcError)

namespace RpcProperty

/-! ## The contracts -/

/-- The contract that returns its call data. -/
def echoAddress : Address := addressOf 0xc1 0x01

/-- The contract that reverts with its call data. -/
def revertAddress : Address := addressOf 0xc2 0x02

/-- The contract that returns what it reads of the transaction and the block. -/
def envAddress : Address := addressOf 0xc3 0x03

/-- The contract that returns the base fee, the chain and its balance, from London. -/
def feeAddress : Address := addressOf 0xc4 0x04

/-- The contract that returns the blob base fee and the first blob hash, from Dencun. -/
def blobAddress : Address := addressOf 0xc5 0x05

/-- The contract that returns the gas it has left. -/
def gasAddress : Address := addressOf 0xc6 0x06

/-- The contract that stores its first two words of call data in slots 0 and 1. -/
def storeAddress : Address := addressOf 0xc7 0x07

/-- The contract that calls the address in its call data with all its gas, and stores the result.
-/
def callerAddress : Address := addressOf 0xc8 0x08

/-- The contract that logs its call data under its first word. -/
def loggerAddress : Address := addressOf 0xc9 0x09

/-- The contract that loops until the gas is gone. -/
def looperAddress : Address := addressOf 0xca 0x0a

/-- The contract whose first byte is the invalid opcode. -/
def invalidAddress : Address := addressOf 0xcb 0x0b

/-- The contract that pops an empty stack. -/
def underflowAddress : Address := addressOf 0xcc 0x0c

/-- The contract that halts when it starts with between 40000 and 60000 gas. -/
def bandAddress : Address := addressOf 0xcd 0x0d

/-- The account whose code delegates to the contract that returns its call data. -/
def delegatedAddress : Address := addressOf 0xde 0x1e

/-- An externally owned account with a balance. -/
def richAddress : Address := addressOf 0xe0 0xa1

/-- The address of a precompile, or of a number. -/
def numberAddress (n : Nat) : Address := toAddressMasked (BitVec.ofNat 256 n)

/-- The code of each contract.

No code uses PUSH0, so each starts at every fork, and halts where the fork lacks an opcode. -/
def zoo : List (Address × ByteArray) := [
  -- CALLDATACOPY(0, 0, CALLDATASIZE), RETURN(0, CALLDATASIZE).
  (echoAddress, bytesOf [0x36, 0x60, 0x00, 0x60, 0x00, 0x37, 0x36, 0x60, 0x00, 0xf3]),
  -- CALLDATACOPY(0, 0, CALLDATASIZE), REVERT(0, CALLDATASIZE).
  (revertAddress, bytesOf [0x36, 0x60, 0x00, 0x60, 0x00, 0x37, 0x36, 0x60, 0x00, 0xfd]),
  -- Eleven words: GASPRICE, ORIGIN, CALLER, NUMBER, BALANCE(CALLER), BLOCKHASH(NUMBER - 1).
  --
  -- Then COINBASE, TIMESTAMP, GASLIMIT, CALLVALUE and DIFFICULTY.
  (envAddress, bytesOf [0x3a, 0x60, 0x00, 0x52, 0x32, 0x60, 0x20, 0x52, 0x33, 0x60, 0x40, 0x52,
    0x43, 0x60, 0x60, 0x52, 0x33, 0x31, 0x60, 0x80, 0x52, 0x60, 0x01, 0x43, 0x03, 0x40, 0x60,
    0xa0, 0x52, 0x41, 0x60, 0xc0, 0x52, 0x42, 0x60, 0xe0, 0x52, 0x45, 0x61, 0x01, 0x00, 0x52,
    0x34, 0x61, 0x01, 0x20, 0x52, 0x44, 0x61, 0x01, 0x40, 0x52, 0x61, 0x01, 0x60, 0x60, 0x00,
    0xf3]),
  -- BASEFEE, CHAINID and SELFBALANCE, each in a word of the output.
  (feeAddress, bytesOf [0x48, 0x60, 0x00, 0x52, 0x46, 0x60, 0x20, 0x52, 0x47, 0x60, 0x40, 0x52,
    0x60, 0x60, 0x60, 0x00, 0xf3]),
  -- BLOBBASEFEE and BLOBHASH(0), each in a word of the output.
  (blobAddress, bytesOf [0x4a, 0x60, 0x00, 0x52, 0x60, 0x00, 0x49, 0x60, 0x20, 0x52, 0x60, 0x40,
    0x60, 0x00, 0xf3]),
  -- MSTORE(0, GAS), RETURN(0, 32).
  (gasAddress, bytesOf [0x5a, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]),
  -- SSTORE(0, CALLDATALOAD(0)), SSTORE(1, CALLDATALOAD(32)).
  (storeAddress, bytesOf [0x60, 0x00, 0x35, 0x60, 0x00, 0x55, 0x60, 0x20, 0x35, 0x60, 0x01, 0x55,
    0x00]),
  -- SSTORE(5, CALL(GAS, CALLDATALOAD(0), CALLDATALOAD(32), 0, 0, 0, 0)).
  (callerAddress, bytesOf [0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x20, 0x35, 0x60,
    0x00, 0x35, 0x5a, 0xf1, 0x60, 0x05, 0x55, 0x00]),
  -- CALLDATACOPY(0, 0, CALLDATASIZE), LOG1(0, CALLDATASIZE, CALLDATALOAD(0)).
  (loggerAddress, bytesOf [0x36, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x35, 0x36, 0x60, 0x00,
    0xa1, 0x00]),
  -- JUMPDEST, JUMP(0).
  (looperAddress, bytesOf [0x5b, 0x60, 0x00, 0x56]),
  (invalidAddress, bytesOf [0xfe]),
  (underflowAddress, bytesOf [0x50]),
  -- INVALID when 40000 < GAS and GAS < 60000, else STOP.
  (bandAddress, bytesOf [0x5a, 0x80, 0x62, 0x00, 0x9c, 0x40, 0x10, 0x90, 0x62, 0x00, 0xea, 0x60,
    0x11, 0x16, 0x60, 0x12, 0x57, 0x00, 0x5b, 0xfe])]

/-- The accounts of every state: the contracts, a delegated account and a rich one. -/
def fixedAccounts : List PreAccount :=
  zoo.map (fun (address, code) => ⟨address, 1, 100, code, [(0, 1)]⟩) ++
  [⟨delegatedAddress, 1, 50, bytesOf [0xef, 0x01, 0x00] ++ ⟨echoAddress.toArray⟩, []⟩,
   ⟨richAddress, 3, 10 ^ 18, .empty, []⟩]

/-! ## A request -/

/-- A call object as its fields, each none when the request leaves it out. -/
structure CallRequest where
  type : Option Nat := none
  sender : Option Address := none
  to : Option Address := none
  /-- Whether a creation writes `"to": null` or leaves the field out. -/
  toNull : Bool := false
  gas : Option Nat := none
  value : Option Nat := none
  input : Option ByteArray := none
  gasPrice : Option Nat := none
  maxFee : Option Nat := none
  priority : Option Nat := none
  blobFee : Option Nat := none
  access : Option (List (Address × List Nat)) := none
  blobs : Option (List Nat) := none
  chain : Option Nat := none
  nonce : Option Nat := none

/-- The request as the text of JSON. -/
def CallRequest.text (r : CallRequest) : String :=
  let quantity (n : Nat) : String := s!"\"0x{hexNat n}\""
  let bytes (b : ByteArray) : String := s!"\"0x{if b.isEmpty then "" else hex b}\""
  let address (a : Address) : String := s!"\"0x{hexVec a}\""
  let access (entries : List (Address × List Nat)) : String :=
    "[" ++ ", ".intercalate (entries.map fun (a, keys) =>
      s!"\{\"address\": {address a}, \"storageKeys\": \
        [{", ".intercalate (keys.map fun k => s!"\"0x{hexVec (word32 k)}\"")}]}") ++ "]"
  let hashes (l : List Nat) : String :=
    "[" ++ ", ".intercalate (l.map fun h => s!"\"0x{hexVec (word32 h)}\"") ++ "]"
  let members : List (String × Option String) := [
    ("type", r.type.map quantity), ("from", r.sender.map address),
    ("to", match r.to with
      | some a => some (address a)
      | none => if r.toNull then some "null" else none),
    ("gas", r.gas.map quantity), ("value", r.value.map quantity), ("input", r.input.map bytes),
    ("gasPrice", r.gasPrice.map quantity), ("maxFeePerGas", r.maxFee.map quantity),
    ("maxPriorityFeePerGas", r.priority.map quantity),
    ("maxFeePerBlobGas", r.blobFee.map quantity), ("accessList", r.access.map access),
    ("blobVersionedHashes", r.blobs.map hashes), ("chainId", r.chain.map quantity),
    ("nonce", r.nonce.map quantity)]
  "{" ++ ", ".intercalate (members.filterMap fun (name, value) =>
    value.map fun v => s!"\"{name}\": {v}") ++ "}"

instance : Repr CallRequest where
  reprPrec r _ := r.text

/-- A case: a fork, the headers of a chain, the block of the call, a state and a request. -/
structure CallCase where
  fork : Fork
  headers : List HeaderSpec
  index : Nat
  accounts : List PreAccount
  request : CallRequest
  /-- Whether the request names its block, or leaves the parameter out for the head. -/
  named : Bool
  deriving Repr

/-- The words of the case in a command of the oracle. -/
def CallCase.words (c : CallCase) : List String :=
  [s!"{c.fork.name}:{referenceName c.fork}", joined ";" (c.headers.map (·.show)),
   toString c.index, joined ";" (c.accounts.map (·.show)), c.request.text]

/-- The view of EthLib: the blocks of the headers, and the state after the block of the call. -/
def CallCase.view (c : CallCase) : Except String ChainView := do
  let records ← c.headers.zipIdx.mapM fun (header, i) =>
    recordOf c.fork (header.toHeader c.fork)
      (if i = c.index then preState c.accounts else ⟨∅, ∅, ∅⟩) [] []
  let activation := if c.fork < .shapella then Activation.block 0 else .time 0
  match viewOf ⟨1, addressOf 0xde 0x90, [(c.fork, activation)], []⟩ records with
  | some view => pure view
  | none => .error "a view has no block"

/-- The parameters of the request: the call object, and the block when the request names it. -/
def CallCase.params (c : CallCase) : Except String (List Json) := do
  let tx ← Json.parse c.request.text
  let number := ((c.headers[c.index]?).map (·.number)).getD 0
  pure ([tx] ++ if c.named then [Json.str s!"0x{hexNat number}"] else [])

/-! ## Generators -/

/-- Call data: a few words, the first often an address or a small number. -/
def genInput : Gen ByteArray := do
  let first ← Gen.element [word32 0, word32 1, word32 7,
    ⟨(Vector.replicate 12 (0 : UInt8)).toArray ++ storeAddress.toArray, by decide⟩,
    ⟨(Vector.replicate 12 (0 : UInt8)).toArray ++ looperAddress.toArray, by decide⟩,
    ⟨(Vector.replicate 12 (0 : UInt8)).toArray ++ echoAddress.toArray, by decide⟩]
  let second ← Gen.element [word32 0, word32 1, word32 5]
  let more ← genBytes (.linear 0 40)
  Gen.element [.empty, ⟨first.toArray⟩, ⟨first.toArray⟩ ++ ⟨second.toArray⟩,
    ⟨first.toArray⟩ ++ ⟨second.toArray⟩ ++ more, more]

/-- Init code: it returns a word as the code, reverts, stops, or is not code. -/
def genInitCode : Gen ByteArray := Gen.element [
  .empty,
  bytesOf [0x60, 0x01, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3],
  bytesOf [0x60, 0x01, 0x60, 0x00, 0x55, 0x60, 0x00, 0x60, 0x00, 0xf3],
  bytesOf [0x60, 0x00, 0x60, 0x00, 0xfd],
  bytesOf [0xfe],
  bytesOf [0x5b, 0x60, 0x00, 0x56]]

/-- The recipient of a call: mostly a contract, sometimes a precompile or no account. -/
def genRecipient (fork : Fork) : Gen Address :=
  Gen.frequency [
    (10, Gen.element (zoo.map (·.1))),
    (2, numberAddress <$> Gen.element [1, 2, 3, 4, 5, 9, 10, 0x100]),
    (1, pure richAddress),
    (1, pure (addressOf 0xab 0x5e)),
    (if fork ≥ .pectra then 2 else 0, pure delegatedAddress)]

/-- A request on a block with a base fee and a gas limit, from one of the senders. -/
def genRequest (fork : Fork) (keys : Array Address) (baseFee gasLimit : Nat) :
    Gen CallRequest := do
  let sender ← Gen.frequency [(3, pure none), (5, some <$> Gen.element keys.toList),
    (1, pure (some richAddress)), (1, pure (some echoAddress))]
  let creates ← Gen.frequency [(5, pure false), (1, pure true)]
  let to ← genRecipient fork
  let toNull ← Gen.bool
  let input ← if creates then some <$> genInitCode else Gen.option genInput
  let gas ← Gen.frequency [(6, pure none),
    (10, some <$> Gen.element [21000, 21064, 25000, 53000, 60000, 70000, 100000, 100000,
      1000000, 1000000, gasLimit]),
    (1, some <$> Gen.element [0, 20999, gasLimit + 1, 2 ^ 24 + 1, 2 ^ 64, 2 ^ 256])]
  -- A request with no sender comes from an address with no balance, so it mostly sends nothing.
  let sends := if sender.isSome then 4 else 1
  let value ← Gen.frequency [(8, pure none), (4, pure (some 0)),
    (sends, some <$> Gen.element [1, 50]),
    (1, some <$> Gen.element [10 ^ 18, 10 ^ 18 + 1, 2 ^ 256 - 1, 2 ^ 256])]
  -- Half of the requests name no fee, and the others name one of each kind.
  let fee := if fork ≥ .london then baseFee else 0
  let price ← Gen.frequency [(6, Gen.element [fee, fee + 1, fee + 1000]),
    (1, Gen.element [fee - 1, 0, 1])]
  let tip ← Gen.frequency [(6, Gen.element [0, 1, 1000]), (1, pure (price + 1))]
  -- A fault in twelve requests: a field that the kind or the fork of the request lacks.
  let odd ← Gen.frequency [(11, pure false), (1, pure true)]
  let (gasPrice, maxFee, priority) ← Gen.frequency [
    (6, pure (none, none, none)),
    (3, pure (some price, none, none)),
    (if fork ≥ .london ∨ odd then 3 else 0, Gen.element [(none, some price, none),
      (none, some price, some tip), (none, none, some tip)]),
    (if odd then 1 else 0, pure (some price, some price, none))]
  let type ← Gen.frequency [(10, pure none),
    (if odd then 2 else 0, some <$> Gen.nat (.constant 0 5)),
    (2, Gen.element (if maxFee.isSome ∨ priority.isSome then
      (typesAt fork).filterMap fun t => if t ≥ 2 then some (some t) else none
      else [some 0] ++ if fork ≥ .berlin ∧ gasPrice.isSome then [some 1] else [])
      |>.map fun t => t)]
  let access ← Gen.frequency [(5, pure none),
    (if fork ≥ .berlin ∨ odd then 1 else 0,
      some <$> Gen.list (.constant 0 2) (Gen.zip (Gen.element [storeAddress, echoAddress])
        (Gen.list (.constant 0 2) (Gen.nat (.constant 0 2)))))]
  let (blobs, blobFee) ← Gen.frequency [(12, pure (none, none)),
    (if (fork ≥ .dencun ∧ gasPrice.isNone ∧ !creates) ∨ odd then 3 else 0, Gen.element [
      (some [2 ^ 248 + 5], some 1000), (some [2 ^ 248 + 5, 2 ^ 248 + 6], none), (none, some 7),
      (some [], some 1)])]
  let chain ← Gen.frequency [(8, pure none), (2, pure (some 1)),
    (if odd then 2 else 0, pure (some 2))]
  let nonce ← Gen.frequency [(4, pure none), (1, some <$> Gen.element [0, 7, 2 ^ 64])]
  pure { type, sender, to := if creates then none else some to, toNull, gas, value, input,
         gasPrice, maxFee, priority, blobFee, access, blobs, chain, nonce }

/-- What a request costs its sender at most, when it names a fee: its gas at its price. -/
def CallRequest.cost (r : CallRequest) (baseFee gasLimit : Nat) : Nat :=
  let gas := r.gas.getD gasLimit
  let price := (r.gasPrice.orElse fun _ => r.maxFee).getD (baseFee + r.priority.getD 0)
  gas * price + r.value.getD 0

/-- A case at a fork: a chain of one to three blocks, a state and a request. -/
def genCallCase (keys : Array Address) (fork : Fork) : Gen CallCase := do
  let number ← Gen.element [0, 1, 5, 1000]
  let count ← Gen.nat (.constant 1 3)
  let baseFee ← Gen.element [7, 1000, 10 ^ 9]
  let gasLimit ← Gen.element [30000000, 30000000, 100000, 2 ^ 25]
  let excess ← Gen.element [0, 5000000, 50000000]
  let randao ← Gen.element [0x11, 0x00]
  let headers := (List.range count).map fun i =>
    ({ number := number + i, time := 1700000000 + 12 * i, gasLimit, gasUsed := 0, baseFee
       excessBlobGas := excess, blobGasUsed := 0
       difficulty := if fork < .paris then 131072 + i else 0, randao } : HeaderSpec)
  let index ← Gen.frequency [(3, pure (count - 1)), (1, Gen.nat (.constant 0 (count - 1)))]
  let request ← genRequest fork keys baseFee gasLimit
  -- A loop burns all its gas, which takes the reference a second per million.
  let loop := bytesOf [0x5b, 0x60, 0x00, 0x56]
  let loops : Bool := request.to == some looperAddress ||
    (request.to.isNone && (request.input.map (·.data == loop.data)).getD false) ||
    (request.to == some callerAddress && (request.input.map fun input =>
      (input.extract 12 32).data == looperAddress.toArray).getD false)
  let request := if loops && decide (request.gas.getD gasLimit > 200000) then
    { request with gas := some 100000 } else request
  -- The balance of a sender: none, plenty, or at the cost of the request and one wei around it.
  let cost := request.cost (if fork ≥ .london then baseFee else 0) gasLimit
  let balances ← Gen.list (.singleton keys.size)
    (Gen.frequency [(1, pure 0), (12, pure (10 ^ 18)), (2, pure (10 ^ 30)),
      (3, (min (2 ^ 256 - 1) ·) <$> Gen.element [cost, cost + 1, cost - 1])])
  let nonces ← Gen.list (.singleton keys.size) (Gen.element [0, 1, 5])
  let senders := (keys.toList.zip (balances.zip nonces)).map fun (address, balance, nonce) =>
    (⟨address, nonce, balance, .empty, []⟩ : PreAccount)
  let named ← if index = count - 1 then Gen.bool else pure true
  pure ⟨fork, headers, index, fixedAccounts ++ senders, request, named⟩

/-- A case for an estimate: three in four are a call that a funded sender can make.

Its recipient is one whose gas says something: storage writes, a nested call, a plain transfer.

The others are a creation, and the contract that halts for a band of gas. -/
def genEstimateCase (keys : Array Address) (fork : Fork) : Gen CallCase := do
  let c ← genCallCase keys fork
  let key ← Gen.nat (.constant 0 (keys.size - 1))
  let sender := keys[key]!
  let baseFee := ((c.headers.head?.map (·.baseFee)).getD 7)
  let fee := if fork ≥ .london then baseFee else 0
  let words (a : Address) (n : Nat) : ByteArray :=
    ⟨(Vector.replicate 12 (0 : UInt8)).toArray ++ a.toArray⟩ ++ ⟨(word32 n).toArray⟩
  let (to, input) ← Gen.element [
    (some storeAddress, some (words echoAddress 5)),
    (some storeAddress, some (words storeAddress 0)),
    (some callerAddress, some (words storeAddress 0)),
    (some callerAddress, some (words echoAddress 0)),
    (some bandAddress, none), (some bandAddress, none), (some richAddress, none),
    (some richAddress, some (bytesOf [1, 0, 2])), (some loggerAddress, some (words echoAddress 1)),
    (some gasAddress, none), (some echoAddress, some (words echoAddress 1)),
    (none, some (bytesOf [0x60, 0x01, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3])),
    (none, some (bytesOf [0x60, 0x01, 0x60, 0x00, 0x55, 0x60, 0x00, 0x60, 0x00, 0xf3]))]
  let gasPrice ← Gen.element [none, some fee, some (fee + 3)]
  let gas ← Gen.element [none, none, some 1000000, some 200000]
  let value ← Gen.element [none, some 0, some 1]
  let plain : CallRequest := { sender := some sender, to, input, gasPrice, gas, value }
  let funded := c.accounts.map fun a =>
    if a.address = sender then { a with balance := 10 ^ 24 } else a
  Gen.frequency [(1, pure c), (3, pure { c with request := plain, accounts := funded })]

/-- A fork that the reference has: half of the draws from London on, where the fee rules are. -/
def genCallFork : Gen Fork :=
  Gen.frequency [(1, Gen.element (forks.map (·.1))), (1, Gen.element ((forks.drop 11).map (·.1)))]

/-! ## The properties -/

/-- How an answer of the oracle ended: `ok`, or the codes of the faults of the request. -/
def codesOf (answer : String) : List String :=
  if answer.startsWith "error " then ((answer.drop 6).toString.splitOn "|").head!.splitOn ","
  else []

/-- The second field of an error answer of the oracle: the data of a revert. -/
def dataOf (answer : String) : String :=
  ((answer.splitOn "|").getD 1 "-")

/-- The labels of a case: the family of its fork, and what its request names. -/
def classifyCase (c : CallCase) : TestT IO Unit := do
  let r := c.request
  classify "a fork before London" (c.fork < .london)
  classify "a fork from Dencun" (c.fork ≥ .dencun)
  classify "the request names a fee" (r.gasPrice.isSome ∨ r.maxFee.isSome ∨ r.priority.isSome)
  classify "the request names no gas" r.gas.isNone
  classify "the request names no sender" r.sender.isNone
  classify "a creation" r.to.isNone
  classify "the call is not on the head" (c.index + 1 < c.headers.length)

/-- eth_call leaves what the message of the request leaves in EELS.

The answer is the output of the message, and a revert gives code 3 with its data.

A request that is refused before its message gets one of the codes of its faults.

The gas left and the number of logs of the message are the reference's too. -/
def ethCall (oracle : Oracle) (keys : Array Address) : Property IO := propertyM do
  let fork ← forAll genCallFork
  let c ← forAll (genCallCase keys fork)
  pure do
    let view ← orFail c.view
    let params ← orFail c.params
    let got := view.call "eth_call" params
    let want ← oracle.ask (["call"] ++ c.words)
    annotate s!"the reference: {want}"
    if want.startsWith "crash" then failWith "the reference failed"
    classifyCase c
    match got with
    | .error e =>
      annotate s!"EthLib: {showError e} {e.message} {(e.data.map (·.compress)).getD ""}"
      classify s!"error {e.code}" true
      ensure ((codesOf want).contains (toString e.code))
        s!"EthLib answers the code {e.code}, the reference {want}"
      classify "a precompile lacks gas, and the code is -32000 where the text says 801"
        (e.code = -32000 ∧ (codesOf want).contains "801")
      if e.code = 3 then
        let data := dataOf want
        (e.data.map (·.compress)) ===
          some (Json.str ("0x" ++ if data = "-" then "" else data)).compress
    | .ok json =>
      annotate s!"EthLib: {json.compress}"
      cover 30 "the call returns" true
      ensure (want.startsWith "ok ") s!"EthLib answers a call that the reference refuses: {want}"
      let fields := (want.drop 3).toString.splitOn "|"
      json.compress === (Json.str ("0x" ++ if fields[0]! = "-" then "" else fields[0]!)).compress
      classify "the call returns data" (fields[0]! ≠ "-")
      -- The gas left and the logs, from the call itself.
      let tx ← orFail ((genericTransaction params.head!).mapError id)
      let number := ((c.headers[c.index]?).map (·.number)).getD 0
      match view.runCall tx (.number number) {} with
      | .ok (_, output) =>
        toString output.gasLeft === fields[1]!
        toString output.logs.size === fields[2]!
        classify "the call writes a log" (output.logs.size > 0)
      | .error e => failWith s!"the call does not run again: {e.code}"

/-- eth_estimateGas answers a gas limit with which the call completes, by a binary search.

A call that fails at its own gas limit fails as eth_call does.

Otherwise the answer is the one of the binary search that the method describes, run on EELS.

The call completes in EELS at that limit, and not one below it unless the limits form no interval.

A signed transaction of the request at that limit succeeds in EELS, when it is valid there. -/
def estimateGas (oracle : Oracle) (keys : Array Address) : Property IO := propertyM do
  let fork ← forAll genCallFork
  let c ← forAll (genEstimateCase keys fork)
  pure do
    let view ← orFail c.view
    let params ← orFail c.params
    let got := view.call "eth_estimateGas" params
    let mine := match got with
      | .ok (.str text) => (text.drop 2).toString.toList.foldl
          (fun acc ch => 16 * acc + (hexDigit? ch).getD 0) 0
      | _ => 0
    let want ← oracle.ask (["estimate"] ++ c.words ++ [if got.isOk then toString mine else "-"])
    annotate s!"the reference: {want}"
    if want.startsWith "crash" then failWith "the reference failed"
    classifyCase c
    match got with
    | .error e =>
      annotate s!"EthLib: {showError e} {e.message} {(e.data.map (·.compress)).getD ""}"
      classify s!"error {e.code}" true
      ensure ((codesOf want).contains (toString e.code))
        s!"EthLib answers the code {e.code}, the reference {want}"
      if e.code = 3 then
        let data := dataOf want
        (e.data.map (·.compress)) ===
          some (Json.str ("0x" ++ if data = "-" then "" else data)).compress
    | .ok json =>
      annotate s!"EthLib: {json.compress}"
      cover 30 "an estimate is given" true
      ensure (want.startsWith "ok ") s!"EthLib estimates a call that the reference refuses: {want}"
      let fields := (want.drop 3).toString.splitOn "|"
      if fields.length ≠ 6 then failWith s!"the oracle answered: {want}"
      -- The search of the method, run on the reference.
      toString mine === fields[0]!
      fields[1]! === "1"
      let least := fields[2]! = "0"
      cover 25 "the limit one below the estimate fails" least
      -- A call that stops for a band of gas is the one case where a lower limit completes.
      let lower := fields[5]! = "1"
      classify "the limits that complete form no interval: a lower one completes" lower
      if !least ∨ lower then
        (c.request.to.map hexVec) === some (hexVec bandAddress)
      classify "the estimate is the intrinsic gas" (mine = 21000)
      classify "the estimate is above 60000" (mine > 60000)
      -- A signed transaction with the limit, where the request is one.
      let real := fields[3]!
      classify "a signed transaction at the estimate succeeds" (real = "success")
      classify "a signed transaction at the estimate is invalid" (real.startsWith "invalid")
      ensure (real ≠ "failed") "a signed transaction at the estimate fails"
      if real = "success" ∧ least then
        ensure (fields[4]! ≠ "success") "a signed transaction one below the estimate succeeds"

/-! ## The state getters -/

/-- A storage key as the text of JSON: few digits, all 64, and texts that are no key. -/
def genKeyText : Gen String :=
  Gen.frequency [
    (6, Gen.element ["\"0x0\"", "\"0x00\"", "\"0x1\"", "\"0x01\"", "\"0x5\"", "\"0x\"", "\"0x7\""]),
    (2, pure s!"\"0x{hexVec (word32 1)}\""),
    (1, pure s!"\"0x{hexVec (word32 (2 ^ 255))}\""),
    (1, Gen.element ["\"0x0A\"", s!"\"0x0{hexVec (word32 1)}\"", "\"1\"", "5", "null"])]

/-- A request of a state method: its name, and its parameters as the text of JSON. -/
def genStateRequest (keys : Array Address) : Gen (String × String) := do
  let address ← Gen.frequency [(6, Gen.element ((zoo.map (·.1)) ++ keys.toList ++
    [richAddress, delegatedAddress])), (1, pure (addressOf 0xab 0x5e))]
  let text := s!"\"0x{hexVec address}\""
  let key ← genKeyText
  let listed ← Gen.list (.constant 0 3) genKeyText
  let block ← Gen.frequency [(4, pure ""), (2, Gen.element [", \"latest\"", ", \"0x5\""]),
    (1, Gen.element [", \"0x6\"", ", \"pending\"", ", \"safe\"", ", null", ", \"latest\", 1"])]
  -- A second member: another address, or the same one in upper case, which is refused.
  let other ← Gen.frequency [
    (4, (fun (a : Address) => hexVec a) <$> Gen.element ((zoo.map (·.1)).filter (· ≠ address))),
    (1, pure (hexVec address).toUpper)]
  Gen.element [
    ("eth_getBalance", s!"[{text}{block}]"),
    ("eth_getTransactionCount", s!"[{text}{block}]"),
    ("eth_getCode", s!"[{text}{block}]"),
    ("eth_getStorageAt", s!"[{text}, {key}{block}]"),
    ("eth_getStorageValues", s!"[\{{text}: [{", ".intercalate listed}]}{block}]"),
    ("eth_getStorageValues",
      s!"[\{{text}: [{key}], \"0x{other}\": [{", ".intercalate listed}]}{block}]"),
    ("eth_getProof", s!"[{text}, [{", ".intercalate listed}]{block}]"),
    ("eth_getProof", s!"[{text}, [{", ".intercalate listed}]{block}]")]

/-- A state method answers what the state holds, and eth_getProof the proof of py-trie.

The balance, the nonce, the code and a storage word are those of the account, or of no account.

A proof is the nodes on the path of the hashed address or key, and its key is a quantity.

The state is that of the one block of the node, and another block is an error. -/
def stateGetters (oracle : Oracle) (keys : Array Address) : Property IO := propertyM do
  let fork ← forAll genCallFork
  let slots ← forAll (Gen.list (.constant 0 4) (Gen.zip (Gen.element [0, 1, 5, 7, 2 ^ 255])
    (Gen.element [0, 1, 2 ^ 200])))
  let (method, params) ← forAll (genStateRequest keys)
  let header : HeaderSpec := { number := 5, time := 1700000000, gasLimit := 30000000, gasUsed := 0
                               baseFee := 7, excessBlobGas := 0, blobGasUsed := 0 }
  let stored := (slots.foldl (fun (kept : List (Nat × Nat)) slot =>
    if kept.any (·.1 = slot.1) then kept else kept ++ [slot]) []).filter (·.2 ≠ 0)
  let accounts := (fixedAccounts.map fun a =>
    if !a.code.isEmpty then { a with storage := stored } else a) ++
    keys.toList.map fun key => (⟨key, 3, 10 ^ 18, .empty, []⟩ : PreAccount)
  let c : CallCase := ⟨fork, [header], 0, accounts, {}, false⟩
  pure do
    let view ← orFail c.view
    let json ← orFail (Json.parse params)
    let got := view.call method (json.getArr?.toOption.getD #[]).toList
    let want ← oracle.ask ["state", joined ";" (accounts.map (·.show)), method, params]
    let ended ← sameAnswer got want
    cover 40 "a state method answers" (ended = "ok")
    if ended = "ok" then classify s!"answered: {method}" true
    else classify s!"refused: {ended}" true
    classify "a proof with a storage slot"
      (ended = "ok" ∧ method = "eth_getProof" ∧ (want.splitOn "\"key\"").length > 1)

/-- Finding: a call to a precompile that lacks gas gets the code of a lack of gas.

`Call.lean` says that a halt for a lack of gas is code 801, and any other halt -32000.

EELS ends such a call with its out-of-gas error, and EthLib answers -32000.

So this property fails, as its group expects. -/
def precompileLacksGas (oracle : Oracle) : Property IO := propertyM do
  let fork ← forAll genCallFork
  let precompile ← forAll (Gen.nat (.constant 1 4))
  let gas ← forAll (Gen.nat (.constant 21000 21010))
  let header : HeaderSpec := { number := 5, time := 1700000000, gasLimit := 30000000, gasUsed := 0
                               baseFee := 7, excessBlobGas := 0, blobGasUsed := 0 }
  let c : CallCase := ⟨fork, [header], 0, fixedAccounts,
    { to := some (numberAddress precompile), gas := some gas }, false⟩
  pure do
    let view ← orFail c.view
    let params ← orFail c.params
    let want ← oracle.ask (["call"] ++ c.words)
    annotate s!"the reference: {want}"
    -- The reference names the lack of gas first.
    ensure ((codesOf want).head? = some "801") "the reference does not run out of gas"
    match view.call "eth_call" params with
    | .error e => e.code === 801
    | .ok _ => failWith "EthLib answers the call"

end RpcProperty

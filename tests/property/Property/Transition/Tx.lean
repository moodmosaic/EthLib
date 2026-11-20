import Property.Transition.World

/-!
# One transaction on a world

A case is a fork, a block, a few accounts and one transaction.

The transaction does one thing, and at most one of its fields sits at the edge of a rule.

Both sides must then agree on whether it may enter the block, and on all that it leaves.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Transactions EthLib.Execution.Blocks EthLib.Execution.Evm
open EvmProperty (PreAccount addressOf hexVec word32 preState assemble genProgram addressNat)

namespace TransitionProperty

/-! ## What a transaction does -/

/-- What a transaction does: its recipient, its data and its value. -/
structure Action where
  name : String
  to : Option Address
  data : ByteArray
  value : Nat
  /-- The gas past the intrinsic gas with which the message ends without running out. -/
  enough : Nat

/-- Call data: mostly short, with zero bytes, since a zero byte has its own price. -/
def genData : Gen ByteArray :=
  bytesOf <$> Gen.list (.linear 0 48) (Gen.frequency [(1, pure 0), (2, genByte)])

/-- Init code, with the gas that lets it end: each rule on created code has its init code. -/
def genInit (large : Bool) : Gen (String × ByteArray × Nat) :=
  let returns (size : List UInt8) : ByteArray := bytesOf ([0x61] ++ size ++ [0x60, 0x00, 0xf3])
  Gen.frequency ([
    (2, pure ("no init code", .empty, 0)),
    (4, (fun (b : UInt8) => (s!"code of one byte {b}",
      bytesOf [0x60, b, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xf3], 1000)) <$>
        Gen.element [0x00, 0xef, 0x5b, 0xfe]),
    (1, pure ("init code that reverts", bytesOf [0x60, 0x00, 0x60, 0x00, 0xfd], 100)),
    (2, pure ("init code that stores",
      bytesOf [0x60, 0x2a, 0x60, 0x01, 0x55, 0x60, 0x01, 0x60, 0x00, 0xf3], 23000)),
    (1, pure ("init code that destroys itself", bytesOf [0x33, 0xff], 35000)),
    (1, pure ("init code that is invalid", bytesOf [0xfe], 0)),
    (2, (fun bytes => ("random init code", bytes, 50000)) <$> genBytes (.linear 0 32))] ++
  (if large then [
    (1, pure ("code at the size limit", returns [0x60, 0x00], 4925000)),
    (1, pure ("code over the size limit", returns [0x60, 0x01], 4925000)),
    (1, (fun (n : Nat) => (s!"init code of {n} bytes", bytesOf (List.replicate n 0), 0)) <$>
      Gen.element [49152, 49153])]
  else []))

/-- The data of a deposit event of EIP-6110, or the same with one offset or the length changed. -/
def genDepositData : Gen (String × ByteArray) := do
  let fill ← genByte
  let part (length padded : Nat) : ByteArray :=
    wordBytes length ++ bytesOf (List.replicate length fill ++ List.replicate (padded - length) 0)
  let offsets (second : Nat) : ByteArray :=
    [160, second, 320, 384, 512].foldl (fun bytes n => bytes ++ wordBytes n) .empty
  let body := part 48 64 ++ part 32 32 ++ part 8 32 ++ part 96 96 ++ part 8 32
  Gen.frequency [
    (4, pure ("deposit", offsets 256 ++ body)),
    (1, pure ("deposit with a wrong offset", offsets 257 ++ body)),
    (1, pure ("deposit that is too long", offsets 256 ++ body ++ bytesOf [0]))]

/-- What a transaction can do, for a sender and a beneficiary: each with its weight and its kind.

The kinds are a transfer, a call, a creation and a self-destruct.

Three more destroy the child of the factory, create it again and call it.

With `large`, a creation may deposit code at the size limit, which is slow in the reference. -/
def actions (fork : Fork) (sender coinbase : Address) (large : Bool) :
    List (Nat × String × Gen Action) :=
  let two : Gen ByteArray := Gen.zipWith (fun a b => wordBytes a ++ wordBytes b)
    (Gen.nat (.constant 0 2)) (Gen.nat (.constant 0 2))
  [(6, "transfer", do
      let to ← Gen.element ([richAddress, absentAddress, emptyAddress, sender, coinbase,
        numberAddress 2, numberAddress 4, numberAddress 0x0a, numberAddress 0x100] ++
        delegatedOddly)
      pure ⟨"transfer", some to, ← genData, ← Gen.element [0, 0, 1, 1000], 5000⟩),
    (4, "call", do pure ⟨"store", some storeAddress, ← two, 0, 45000⟩),
    (3, "self-destruct", do
      let heir ← Gen.element [sender, absentAddress, destructAddress, coinbase, numberAddress 1,
        richAddress, emptyAddress]
      pure ⟨"self-destruct", some destructAddress, wordBytes (addressNat heir),
        ← Gen.element [0, 5], 35000⟩),
    (4, "call", do
      -- A precompile is warm from the start of a transaction, at the forks that have it.
      let callee ← Gen.frequency [
        (3, Gen.element ([storeAddress, destructAddress, reverterAddress, absentAddress,
          emptyAddress, richAddress, coinbase, sender, loggerAddress] ++ delegatedOddly)),
        (2, numberAddress <$> Gen.element [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
          17, 18, 0x100, 0x101])]
      let sent ← Gen.element [0, 0, 1, 10 ^ 30]
      pure ⟨"call", some callerAddress, wordBytes (addressNat callee) ++ wordBytes sent,
        ← Gen.element [0, 10], 80000⟩),
    (3, "create", do
      let (_, init, enough) ← genInit false
      pure ⟨"create by a contract", some creatorAddress, init, ← Gen.element [0, 3],
        enough + 80000⟩),
    (2, "call", do pure ⟨"log", some loggerAddress, ← genBytes (.linear 0 80), 0, 5000⟩),
    (8, "call", pure ⟨"revert", some reverterAddress, .empty, 0, 25000⟩),
    (1, "call", pure ⟨"loop", some looperAddress, .empty, 0, 0⟩),
    (2, "call", do
      let distance ← Gen.element [0, 1, 2, 3, 8, 9, 255, 256, 257, 258]
      pure ⟨"block hash", some hashesAddress, wordBytes distance, 0, 45000⟩),
    (1, "reborn: destroy", pure ⟨"destroy the child", some childAddress, bytesOf [1], 0, 40000⟩),
    (1, "reborn: create", pure ⟨"create the child", some factoryAddress, .empty, 0, 120000⟩),
    (1, "reborn: count", pure ⟨"call the child", some childAddress, .empty, 0, 50000⟩),
    (4, "call", do pure ⟨"program", some EvmProperty.targetAddress, ← genBytes (.linear 0 40),
        ← Gen.element [0, 1], 150000⟩),
    (2, "call", do pure ⟨"call a delegated account", some delegatedAddress, ← two, 0, 50000⟩),
    (5, "create", do
      let (name, init, enough) ← genInit large
      pure ⟨s!"create: {name}", none, init, ← Gen.element [0, 7], enough⟩),
    (if fork ≥ .pectra then 3 else 0, "call", do
      let request ← genBytesN 56
      pure ⟨"withdrawal request", some WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS, request,
        ← Gen.element [0, 1, 2], 150000⟩),
    (if fork ≥ .pectra then 2 else 0, "call", do
      let request ← genBytesN 96
      pure ⟨"consolidation request", some CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS, request,
        ← Gen.element [0, 1, 2], 180000⟩),
    (if fork ≥ .pectra then 3 else 1, "call", do
      let (name, data) ← genDepositData
      pure ⟨name, some depositAddress, data, 0, 20000⟩)]

/-- What a transaction does: any action, or one of the kinds that start with a word. -/
def genAction (fork : Fork) (sender coinbase : Address) (large : Bool := true)
    (kind : Option String := none) : Gen Action :=
  Gen.frequency (((actions fork sender coinbase large).filter fun (_, k, _) =>
    kind.all (k.startsWith ·)).map fun (weight, _, action) => (weight, action))

/-! ## The edge of a rule -/

/-- The one rule that a transaction is placed at the edge of. -/
inductive Fault where
  | none | nonceLow | nonceHigh | balanceShort | balanceExact | gasBelowMinimum | gasAtMinimum
  | feeBelowBase | feeAtBase | priorityAboveMax | blobFeeBelow | blobFeeAt | blobVersion | noBlobs
  | blobsOverBlock | sevenBlobs | senderCode | senderDelegated | gasOverBlock | gasAtBlock
  | gasOverCap | gasAtCap | wrongChain | highS | zeroR | typedCreate | noAuthorization | earlyType
  | chainBeforeSpuriousDragon | largeInit
  deriving Repr, BEq, DecidableEq

/-- A fault: none for half of the cases, else any one. -/
def genFault : Gen Fault :=
  Gen.frequency [(1, pure .none), (1, Gen.element [.nonceLow, .nonceHigh, .balanceShort,
    .balanceExact, .gasBelowMinimum, .gasAtMinimum, .feeBelowBase, .feeAtBase, .priorityAboveMax,
    .blobFeeBelow, .blobFeeAt, .blobVersion, .noBlobs, .blobsOverBlock, .sevenBlobs, .senderCode,
    .senderDelegated, .gasOverBlock, .gasAtBlock, .gasOverCap, .gasAtCap, .wrongChain, .highS,
    .zeroR, .typedCreate, .noAuthorization, .earlyType, .chainBeforeSpuriousDragon, .largeInit])]

/-- Whether a fault can bite at a fork: the fork has the rule, or the type that the rule is on. -/
def Fault.bites (fault : Fault) (fork : Fork) : Bool :=
  match fault with
  | .blobFeeBelow | .blobFeeAt | .blobVersion | .noBlobs | .blobsOverBlock | .typedCreate =>
    fork ≥ .dencun
  | .sevenBlobs | .gasOverCap | .gasAtCap => fork ≥ .pectra
  | .noAuthorization | .senderDelegated => fork ≥ .paris
  | .feeBelowBase | .priorityAboveMax => fork ≥ .london
  | .wrongChain => fork ≥ .spuriousDragon
  | .chainBeforeSpuriousDragon => fork < .byzantium
  | .earlyType => fork < .pectra
  | .largeInit => fork ≥ .paris
  | _ => true

/-- The types of transaction that a fork has. -/
def typesAt (fork : Fork) : List Nat :=
  [0] ++ (if fork ≥ .berlin then [1] else []) ++ (if fork ≥ .london then [2] else []) ++
    (if fork ≥ .dencun then [3] else []) ++ (if fork ≥ .pectra then [4] else [])

/-- The type of a transaction for a fault: mostly one that the fork has and the fault needs. -/
def genType (fork : Fork) (fault : Fault) (creates : Bool) : Gen Nat :=
  let has := typesAt fork
  let among (wanted : List Nat) : Gen Nat :=
    let fit := has.filter (wanted.contains ·)
    Gen.element (if fit.isEmpty then has else fit)
  match fault with
  | .earlyType => pure (if has.length < 5 then has.length else 0)
  | .blobFeeBelow | .blobFeeAt | .blobVersion | .noBlobs | .blobsOverBlock | .sevenBlobs =>
    among [3]
  | .noAuthorization => among [4]
  | .typedCreate => among [3, 4]
  | .priorityAboveMax => among [2, 3, 4]
  | _ => among (if creates then [0, 1, 2] else [0, 1, 2, 3, 4])

/-- An access list: addresses of the world, each with a few low storage keys. -/
def genAccess (sender coinbase : Address) : Gen (List (Address × List Nat)) :=
  Gen.list (.linear 0 3) (Gen.zip
    (Gen.element [storeAddress, sender, coinbase, absentAddress, numberAddress 1, destructAddress,
      callerAddress, delegatedAddress])
    (Gen.list (.linear 0 2) (Gen.nat (.constant 0 2))))

/-- The account of an authority before the transaction: none, plain, delegated or a contract. -/
structure Authority where
  kind : Nat
  nonce : Nat

/-- The account of an authority, if it has one. -/
def Authority.account (a : Authority) (address : Address) : List PreAccount :=
  match a.kind with
  | 0 => []
  | 1 => [⟨address, a.nonce, 10, .empty, []⟩]
  | 2 => [⟨address, a.nonce, 10, delegationIndicator loggerAddress, []⟩]
  | _ => [⟨address, a.nonce, 10, bytesOf [0x00], []⟩]

/-- The accounts of the authorities, which hold the keys from 4 on. -/
def authorityAccounts (setup : Setup) (authorities : List Authority) : List PreAccount :=
  authorities.zipIdx.flatMap fun (a, i) => a.account (setup.key (i + 4))

/-- Three authorities, each with no account, a plain one, a delegated one or a contract. -/
def genAuthorities : Gen (List Authority) :=
  Gen.list (.singleton 3) (Gen.zipWith Authority.mk (Gen.element [0, 1, 1, 2, 3])
    (Gen.element [0, 1, 5]))

/-- The authorizations of a set code transaction from the key `sender` at the nonce `nonce`.

Most name the nonce that their authority will have, after the authorizations before them.

The sender is an authority now and then, with its nonce one more than the transaction's.

It also gives how many authorizations of the sender itself are in order, which move its nonce. -/
def genAuths (sender nonce : Nat) (authorities : List Authority) : Gen (List AuthSpec × Nat) := do
  let nonceOf (key : Nat) : Nat :=
    if key = sender then nonce + 1
    else match authorities[key - 4]? with
      | some a => if a.kind = 0 then 0 else a.nonce
      | none => 0
  let drawn ← Gen.list (.linear 1 3) (Gen.zip
    (Gen.zip (Gen.element [4, 5, 6, sender])
      (Gen.frequency [(4, pure 1), (2, pure 0), (1, pure 2)]))
    (Gen.zip (Gen.element [storeAddress, loggerAddress, numberAddress 0, numberAddress 1,
        absentAddress, looperAddress])
      (Gen.zip (Gen.frequency [(5, pure 0), (1, pure 1)])
        (Gen.frequency [(8, pure 0), (1, pure 1), (1, pure 2)]))))
  let inOrder (entry : (Nat × Nat) × Address × Nat × Nat) : Bool :=
    entry.1.2 ≠ 2 ∧ entry.2.2.1 = 0 ∧ entry.2.2.2 = 0
  let auths := drawn.zipIdx.map fun (((key, chain), address, skew, fault), index) =>
    let earlier := ((drawn.take index).filter fun e => e.1.1 = key ∧ inOrder e).length
    AuthSpec.mk chain address (nonceOf key + earlier + skew) key fault
  pure (auths, (drawn.filter fun e => e.1.1 = sender ∧ inOrder e).length)

/-! ## A transaction that should enter a block -/

/-- The prices of a block, by which a generator places the fees of a transaction. -/
structure Prices where
  baseFee : Nat
  blobPrice : Nat

/-- A transaction of the key `key` at the nonce `nonce`, with fees that the block accepts.

It is of the kind and the type that are asked, or of any that the fork has.

It also gives what the transaction does, and how far it moves the nonce of its sender. -/
def genIncluded (fork : Fork) (prices : Prices) (key nonce : Nat) (sender coinbase : Address)
    (authorities : List Authority) (kind : Option String := none) (type : Option Nat := none) :
    Gen (TxSpec × String × Nat) := do
  let action ← genAction fork sender coinbase false kind
  let type ← match type with
    | some type => pure type
    | none => Gen.element ((typesAt fork).filter fun t => !(action.to.isNone ∧ t ≥ 3))
  let floor := if fork ≥ .london then prices.baseFee else 0
  let tip ← Gen.element [0, 1, 3, 1000]
  let room ← Gen.element [0, 2, 10]
  let maxFee := prices.baseFee + room
  let priorityFee ← Gen.element [0, 1, room, maxFee]
  let count ← Gen.nat (.constant 1 2)
  let over ← Gen.element [0, 1, 100]
  let access ← if type ≥ 1 then genAccess sender coinbase else pure []
  let (auths, moved) ← if type = 4 then genAuths key nonce authorities else pure ([], 0)
  let named ← Gen.element [0, 1]
  let chain := if type = 0 then (if fork ≥ .spuriousDragon then named else 0) else 1
  let blobs := (List.range count).map fun i => 2 ^ 248 + i + 1
  let draft : TxSpec := ⟨type, key, chain, nonce, floor + tip, priorityFee, maxFee, 0, action.to,
    action.value, action.data, access, prices.blobPrice + over, blobs, auths, 0⟩
  let enough := if fork ≥ .glamsterdam then 10 * action.enough + 300000 else action.enough
  let extra ← if action.name = "loop" then Gen.nat (.linear 0 30000) else
    Gen.frequency [(6, (enough + ·) <$> Gen.nat (.linear 0 100000)),
      (1, Gen.nat (.linear 0 enough)), (1, pure 0)]
  pure ({ draft with gas := draft.minimumGas fork sender + extra }, action.name, 1 + moved)

/-! ## A case -/

/-- One transaction on a world. -/
structure TxCase where
  fork : Fork × String
  env : EnvSpec
  accounts : List PreAccount
  tx : TxSpec
  action : String
  fault : Fault
  coinbase : String

/-- A case as a report shows it. -/
def TxCase.show (c : TxCase) : String :=
  s!"fork={c.fork.2} ({c.fork.1.name}) action={c.action} fault={reprStr c.fault} \
    coinbase={c.coinbase} schedule={c.env.schedule}\n  env={c.env.show}\n  tx={c.tx.show}\n  \
    accounts=\n    \
    {"\n    ".intercalate (c.accounts.map (·.show))}"

/-- The accounts that a generated program may call, and the program itself. -/
def genProgramAccounts (fork : Fork) : Gen (List PreAccount) := do
  let program ← genProgram fork 20
  let callees ← Gen.list (.singleton 2) (genProgram fork 8)
  pure [⟨EvmProperty.targetAddress, 1, 1000, assemble program, [(0, 1), (1, 2)]⟩,
    ⟨addressOf 0xa1 0xa1, 1, 7, assemble (callees.getD 0 []), [(0, 1)]⟩,
    ⟨addressOf 0xa2 0xa2, 0, 0, assemble (callees.getD 1 []), []⟩]

/-- A case: a fork, a block, one transaction with at most one fault, and the world for it. -/
def genCase (setup : Setup) (only : Option (Fork × String) := none) : Gen TxCase := do
  let fault ← genFault
  -- Four cases in five are at a fork where the fault can bite.
  let fork ← match only with
    | some fork => pure fork
    | none => Gen.frequency [(4, genForkWhere fault.bites), (1, genFork)]
  let (fork, schedule) ← if only.isSome then pure (fork, none) else genCrossed fork
  let f := fork.1
  let sender := setup.key 0
  let (coinbaseName, coinbase, coinbaseAccount) ← Gen.element [
    ("absent", addressOf 0xba 0x5e, []), ("absent", addressOf 0xba 0x5e, []),
    ("empty", addressOf 0xba 0x5e, [(⟨addressOf 0xba 0x5e, 0, 0, .empty, []⟩ : PreAccount)]),
    ("funded", addressOf 0xba 0x5e, [⟨addressOf 0xba 0x5e, 0, 5, .empty, []⟩]),
    ("the sender", sender, []), ("a contract", storeAddress, []),
    ("a precompile", numberAddress 3, [])]
  let action ← if fault == .largeInit then
      (fun (n : Nat) => (⟨s!"create: init code of {n} bytes", none, bytesOf (List.replicate n 0),
        0, 0⟩ : Action)) <$> Gen.element [49153, 49152]
    else genAction f sender coinbase
  let type ← genType f fault action.to.isNone
  let to := if fault == .typedCreate then none else
    if type ≥ 3 ∧ action.to.isNone then some richAddress else action.to
  let action := { action with to }
  -- The fees.
  let baseFee ← Gen.element [7, 1, 1000]
  let floor := if f ≥ .london then baseFee else 0
  let tip ← Gen.element [0, 1, 3, 1000]
  let gasPrice := match fault with
    | .feeBelowBase => floor - 1
    | .feeAtBase => floor
    | _ => floor + tip
  let room ← Gen.element [0, 2, 10]
  let maxFee := match fault with
    | .feeBelowBase => baseFee - 1
    | .feeAtBase => baseFee
    | _ => baseFee + room
  let priorityFee ← match fault with
    | .feeBelowBase => pure 0
    | .priorityAboveMax => pure (maxFee + 1)
    | _ => Gen.element [0, 1, room, maxFee]
  -- The blobs.
  let excessBlobGas ← Gen.element [0, 3000000, 10000000]
  let price := blobPrice f excessBlobGas schedule
  let most := maxBlobs f schedule
  let count ← match fault with
    | .noBlobs => pure 0
    | .sevenBlobs => pure 7
    | _ => Gen.nat (.constant 1 (min 6 most))
  let over ← Gen.element [0, 1, 100]
  let blobFee := match fault with
    | .blobFeeBelow => price - 1
    | .blobFeeAt => price
    | _ => price + over
  let version (i : Nat) : Nat := if fault == .blobVersion ∧ i = count - 1 then 2 else 1
  let blobs := (List.range count).map fun i => version i * 2 ^ 248 + i + 1
  let blobGasUsed :=
    if fault == .blobsOverBlock ∧ f ≥ .dencun then (most - count + 1) * 2 ^ 17 else 0
  -- The nonce, the access list and the authorizations.
  let before ← Gen.element [0, 1, 7]
  let before := if fault == .nonceLow then before + 1 else before
  let nonce := match fault with
    | .nonceLow => before - 1
    | .nonceHigh => before + 1
    | _ => before
  let access ← if type ≥ 1 then genAccess sender coinbase else pure []
  let authorities ← genAuthorities
  let (auths, _) ← if type = 4 then genAuths 0 before authorities else pure ([], 0)
  let auths := if fault == .noAuthorization then [] else auths
  let named ← Gen.element [0, 1]
  let chain := match fault with
    | .wrongChain => 2
    | .chainBeforeSpuriousDragon => 1
    | _ => if type = 0 then (if f ≥ .spuriousDragon then named else 0) else 1
  let signature := match fault with
    | .highS => 1
    | .zeroR => 2
    | _ => 0
  -- The gas limit, from the least one.
  let draft : TxSpec := ⟨type, 0, chain, nonce, gasPrice, priorityFee, maxFee, 0, action.to,
    action.value, action.data, access, blobFee, blobs, auths, signature⟩
  let least := draft.minimumGas f sender
  -- From Glamsterdam a new account and a new slot cost state gas, far more than before.
  let enough := if f ≥ .glamsterdam then 10 * action.enough + 300000 else action.enough
  let extra ← if action.name = "loop" then Gen.nat (.linear 0 30000) else
    Gen.frequency [(5, (enough + ·) <$> Gen.nat (.linear 0 100000)),
      (2, Gen.nat (.linear 0 enough)), (1, pure 0)]
  let gas := match fault with
    | .gasBelowMinimum => least - 1
    | .gasAtMinimum => least
    | .gasOverCap => 2 ^ 24 + 1
    | .gasAtCap => 2 ^ 24
    | _ => least + extra
  let tx := { draft with gas }
  let gasLimit := 30000000
  let gasUsed ← match fault with
    | .gasOverBlock => pure (gasLimit - gas + 1)
    | .gasAtBlock => pure (gasLimit - gas)
    | _ => Gen.element [0, 21000, 1000000]
  -- The sender, with a balance near the cost.
  let margin ← Gen.element [0, 1, 10 ^ 18, 10 ^ 18]
  let balance := match fault with
    | .balanceShort => tx.cost - 1
    | .balanceExact => tx.cost
    | _ => tx.cost + margin
  let code := match fault with
    | .senderCode => bytesOf [0x00]
    | .senderDelegated => delegationIndicator storeAddress
    | _ => .empty
  -- An account at the address of a creation, now and then.
  let created := (createAddress sender before).toOption.getD absentAddress
  let collision ← if action.to.isNone then Gen.frequency [(5, pure []),
      (1, pure [(⟨created, 1, 0, .empty, []⟩ : PreAccount)]),
      (1, pure [⟨created, 0, 0, bytesOf [0x00], []⟩]),
      -- Storage alone: EIP-7610 refuses the creation, and EIP-8037 does not.
      --
      -- EthLib follows EIP-7610 at every fork, and says so, so Glamsterdam leaves the case out.
      (if f ≥ .glamsterdam then 0 else 1, pure [⟨created, 0, 0, .empty, [(1, 1)]⟩]),
      (1, pure [⟨created, 0, 9, .empty, []⟩])]
    else pure []
  let empty ← Gen.frequency [(2, pure []),
    (1, pure [(⟨emptyAddress, 0, 0, .empty, []⟩ : PreAccount)])]
  let child ← Gen.element [[], [childAccount]]
  let program ← genProgramAccounts f
  let accounts := distinctAccounts ([⟨sender, before, balance, code, []⟩] ++ collision ++
    authorityAccounts setup authorities ++ coinbaseAccount ++ empty ++ child ++ program ++
    fixedAccounts f)
  let env : EnvSpec := ⟨1000, 1700000000, gasLimit, baseFee, coinbase, 0x20000, 0x11,
    excessBlobGas, gasUsed, blobGasUsed, schedule⟩
  pure ⟨fork, env, accounts, tx, action.name, fault, coinbaseName⟩

/-! ## The property -/

/-- Run a case on both sides and compare all that the transaction left.

It gives the outcome: how the message ended, or why the transaction is invalid. -/
def checkCase (oracle : Oracle) (c : TxCase) : TestT IO String := do
  let fork := c.fork.1
  let answer ← oracle.ask
    ["tx", c.fork.2, c.env.show, showAccounts c.accounts, c.tx.show]
  let words := answer.splitOn "\t"
  if words.length ≠ 7 then failWith s!"the oracle answered: {answer}"
  let raw := (unhex? words[0]!).getD .empty
  let before := bodyStart fork (preState c.accounts) ⟨c.env.gasUsed, 0, c.env.blobGasUsed⟩
  let (got, _) := runTransaction (c.env.toEnv fork) 0 before raw
  annotate s!"the bytes: {words[0]!}"
  annotate s!"the reference: {words[1]!}, {words[2]!}; EthLib: {got.verdict}, {got.detail}"
  sameResult got (words.drop 1)
  if got.verdict = "valid" then
    let ended := (words[2]!.splitOn " ").head!
    -- The two sides name the errors of a halt apart, so running out of gas counts as a halt.
    let coarse (ending : String) : String := if ending = "oog" then "halt" else ending
    coarse got.detail === coarse ended
    pure ended
  else pure s!"invalid: {reasonOfReference ((words[1]!.splitOn " ").getD 1 "")}"

/-- A transaction leaves what the reference leaves, at every fork that the reference has.

Both sides agree on whether it may enter its block.

For a valid one they agree on the gas used, the blob gas, the receipt and every account after it.

So the refund and its cap, the fee of the beneficiary and the burn, and the deletions are compared.

A refused transaction leaves the state as it was. -/
def oneTransaction (setup : Setup) (only : Option (Fork × String) := none) : Property IO :=
  propertyM do
  let c ← forAllWith TxCase.show (genCase setup only)
  let oracle := if only.isSome then setup.glamsterdam.getD setup.oracle else setup.oracle
  pure do
    let outcome ← checkCase oracle c
    let valid := !outcome.startsWith "invalid"
    label s!"{family c.fork.1}: {if valid then outcome else "invalid"}"
    classify s!"outcome: {outcome}" true
    classify s!"action: {(c.action.splitOn ":").head!}" true
    classify s!"fault: {(reprStr c.fault).replace "TransitionProperty.Fault." ""}, refused"
      (!valid)
    classify s!"type {c.tx.type}, valid" valid
    classify s!"beneficiary: {c.coinbase}, valid" valid
    cover 25 "valid" valid
    cover 10 "invalid" (!valid)

/-- Both sides refuse a transaction for the same reason.

The reasons are compared only when a case has one fault, since the order of the checks differs. -/
def refusalReason (setup : Setup) : Property IO := propertyM do
  let c ← forAllWith TxCase.show (genCase setup)
  pure do
    let fork := c.fork.1
    let answer ← setup.oracle.ask
      ["tx", c.fork.2, c.env.show, showAccounts c.accounts, c.tx.show]
    let words := answer.splitOn "\t"
    if words.length ≠ 7 then failWith s!"the oracle answered: {answer}"
    let raw := (unhex? words[0]!).getD .empty
    let before := bodyStart fork (preState c.accounts) ⟨c.env.gasUsed, 0, c.env.blobGasUsed⟩
    let (got, _) := runTransaction (c.env.toEnv fork) 0 before raw
    if got.verdict = "invalid" then
      let reason := reasonOfReference ((words[1]!.splitOn " ").getD 1 "")
      annotate s!"the reference: {words[1]!}"
      label reason
      got.detail === reason

/-- A creation by a transaction at an address that holds storage alone, at Glamsterdam. -/
def genStorageOnlyCreation (setup : Setup) : Gen TxCase := do
  let gas ← Gen.nat (.linear 324000 1000000)
  let value ← Gen.element [0, 7]
  let sender := setup.key 0
  let created := (createAddress sender 0).toOption.getD absentAddress
  let tx : TxSpec := ⟨0, 0, 0, 0, 7, 0, 7, gas, none, value, .empty, [], 0, [], [], 0⟩
  let accounts : List PreAccount :=
    [⟨sender, 0, 10 ^ 18, .empty, []⟩, ⟨created, 0, 0, .empty, [(1, 1)]⟩]
  let env : EnvSpec :=
    ⟨1000, 1700000000, 30000000, 7, addressOf 0xba 0x5e, 0x20000, 0x11, 0, 0, 0, none⟩
  pure ⟨(.glamsterdam, "amsterdam"), env, accounts, tx, "create over storage", .none, "absent"⟩

/-- A creation at an address with storage alone ends as in the branch of the reference.

It does not, and EthLib says why in `Evm/Call/Create.lean`: it follows EIP-7610 at every fork.

EIP-8037 and the branch let such a creation run at Glamsterdam.

So this is a difference that the maintainers wrote down, and it is kept failing to stay in view. -/
def storageOnlyCreation (setup : Setup) : Property IO := propertyM do
  let c ← forAllWith TxCase.show (genStorageOnlyCreation setup)
  pure do
    let _ ← checkCase (setup.glamsterdam.getD setup.oracle) c

end TransitionProperty

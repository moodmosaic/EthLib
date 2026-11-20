import Property.Execution.Common

/-!
# Transactions as bytes, against execution-specs

A transaction is generated as an RLP item, field by field.

The values are at the edges that the rules name.

The item is then changed a little, so that most inputs are almost valid.

EthLib and the reference must agree on whether the bytes hold a transaction.

They must also agree on its hash, its sender, its intrinsic gas, its floor and its validity.
-/

open Hedgehog Support EthLib EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Transactions

namespace ExecutionProperty

/-- The chains that the tests sign: small ones and the top of 64 bits. -/
def genChain : Gen Nat := Gen.element [1, 5, 2 ^ 63, 2 ^ 64 - 1]

/-- A scalar item of at most `bits` bits, often at an edge. -/
def genScalar (bits : Nat) (edges : List Nat := []) : Gen Item :=
  Item.scalar <$> genNatNear bits edges

/-- Call data: zero and other bytes mixed, now and then around the limit of init code. -/
def genData : Gen ByteArray :=
  let byte : Gen UInt8 := Gen.frequency [(1, pure 0), (1, genByte)]
  Gen.frequency [
    (12, bytesOf <$> Gen.list (.linear 0 80) byte),
    (1, (fun (n : Nat) (b : UInt8) => bytesOf (List.replicate n b)) <$>
      Gen.element [49151, 49152, 49153, 24576, 24577] <*> Gen.element [0, 1])]

/-- A recipient: an address, or now and then none. -/
def genTo : Gen Item :=
  Gen.frequency [(4, (fun a => Item.bytes ⟨a.toArray⟩) <$> genAddress),
    (1, pure (.bytes .empty))]

/-- A gas limit, when the test does not set it from the intrinsic gas. -/
def genGas : Gen Item :=
  Item.scalar <$> Gen.frequency [(3, Gen.nat (.linear 21000 200000)),
    (2, Gen.element [0, 20999, 21000, 2 ^ 24 - 1, 2 ^ 24, 2 ^ 24 + 1, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 64,
      2 ^ 256 - 1])]

/-- A nonce, often at the bound of EIP-2681. -/
def genNonce : Gen Item := genScalar 64 [2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 256 - 1]

/-- An integer of a signature, often at a bound of its range. -/
def genSigScalar : Gen Item :=
  Item.scalar <$> Gen.frequency [(6, Gen.nat (.constant 1 (curveOrder / 2))),
    (1, Gen.nat (.constant 1 (2 ^ 256 - 1))),
    (2, Gen.element [0, 1, curveOrder / 2, curveOrder / 2 + 1, curveOrder - 1, curveOrder,
      curveOrder + 1])]

/-- The `v` of a legacy transaction on a chain: mostly a valid one. -/
def genV (chain : Nat) : Gen Item :=
  Item.scalar <$> Gen.frequency [
    (4, Gen.element [27, 28, 35 + 2 * chain, 36 + 2 * chain]),
    (2, Gen.element [0, 1, 26, 29, 34, 35, 36, 37, 38, 34 + 2 * chain, 37 + 2 * chain,
      35 + 2 * (2 ^ 64 - 1), 36 + 2 * (2 ^ 64 - 1), 35 + 2 * 2 ^ 64, 2 ^ 256 - 1])]

/-- The parity of a typed transaction: mostly 0 or 1. -/
def genParity : Gen Item :=
  Item.scalar <$> Gen.frequency [(9, Gen.element [0, 1]), (1, Gen.element [2, 27, 28, 256])]

/-- The chain of a typed transaction: mostly the one of the test. -/
def genChainItem (chain : Nat) : Gen Item :=
  Item.scalar <$> Gen.frequency [(12, pure chain),
    (1, Gen.element [0, chain + 1, 2 ^ 64 - 1, 2 ^ 64])]

/-- An access list: a few accounts, each with a few slots. -/
def genAccessList : Gen Item :=
  let slot := (fun (w : Bytes32) => Item.bytes ⟨w.toArray⟩) <$> genWord
  let entry := (fun (a : Address) slots => Item.list [.bytes ⟨a.toArray⟩, .list slots]) <$>
    genAddress <*> Gen.list (.linear 0 3) slot
  Item.list <$> Gen.list (.linear 0 3) entry

/-- A versioned hash: mostly of version 1. -/
def genVersionedHash : Gen Item :=
  (fun (version : UInt8) (rest : ByteArray) => Item.bytes (⟨#[version]⟩ ++ rest)) <$>
    Gen.frequency [(12, pure 1), (1, Gen.element [0, 2, 0xff])] <*> genBytesN 31

/-- The versioned hashes of a blob transaction: now and then none, or more than six. -/
def genVersionedHashes : Gen Item :=
  Item.list <$> Gen.frequency [(6, Gen.list (.constant 1 6) genVersionedHash),
    (2, pure []), (2, Gen.list (.constant 7 10) genVersionedHash)]

/-- An authorization: each field in its range, or just outside it. -/
def genAuthorization (chain : Nat) : Gen Item := do
  let chainId ← Item.scalar <$> Gen.frequency [(8, Gen.element [0, chain, chain + 1]),
    (1, Gen.element [2 ^ 256 - 1, 2 ^ 256])]
  let address ← Gen.frequency [(15, genTo), (1, pure (.bytes .empty))]
  let nonce ← Item.scalar <$> Gen.frequency [(8, Gen.nat (.exponential 0 (2 ^ 64 - 1))),
    (1, Gen.element [2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64])]
  let parity ← Item.scalar <$> Gen.frequency [(8, Gen.element [0, 1]),
    (1, Gen.element [2, 255, 256])]
  let r ← genSigScalar
  let s ← genSigScalar
  pure (.list [chainId, address, nonce, parity, r, s])

/-- The fields of a transaction of a type on a chain, and the index of its gas limit. -/
def genFields (type chain : Nat) : Gen (List Item × Nat) := do
  let fee ← genScalar 256
  let tip ← genScalar 256
  let nonce ← genNonce
  let gas ← genGas
  let address := (fun (a : Address) => Item.bytes ⟨a.toArray⟩) <$> genAddress
  let to ← if type ≥ 3 then Gen.frequency [(15, address), (1, pure (.bytes .empty))] else genTo
  let value ← genScalar 256
  let large := (fun (n : Nat) (b : UInt8) => bytesOf (List.replicate n b)) <$>
    Gen.element [49151, 49152, 49153, 65536, 65537] <*> Gen.element [0, 1]
  let data ← Item.bytes <$> (if to == .bytes .empty then Gen.frequency [(7, genData), (1, large)]
    else genData)
  let r ← genSigScalar
  let s ← genSigScalar
  if type = 0 then
    pure ([nonce, fee, gas, to, value, data, ← genV chain, r, s], 2)
  else
    let chainId ← genChainItem chain
    let accessList ← genAccessList
    let parity ← genParity
    let head := if type = 1 then [chainId, nonce, fee, gas, to, value, data, accessList]
      else [chainId, nonce, tip, fee, gas, to, value, data, accessList]
    let extra ← match type with
      | 3 => (fun fee hashes => [fee, hashes]) <$> genScalar 256 <*> genVersionedHashes
      | 4 => (fun auths => [Item.list auths]) <$> Gen.frequency [(1, pure []),
        (4, Gen.list (.constant 1 3) (genAuthorization chain))]
      | _ => pure []
    pure (head ++ extra ++ [parity, r, s], if type = 1 then 3 else 4)

/-- The bytes of a transaction of a type with these fields. -/
def txBytes (type : Nat) (fields : Item) : ByteArray :=
  if type = 0 then enc fields else ⟨#[UInt8.ofNat type]⟩ ++ enc fields

/-- The fields with the gas limit a little off the least one of the fork, if they decode. -/
def nearMinimum (fork : Fork) (type index : Nat) (delta : Int) (fields : List Item) :
    List Item :=
  match decodeTransaction .hegota (txBytes type (.list fields)) with
  | .ok tx =>
    let least : Int := minimumGas fork (Vector.replicate 20 0) tx
    fields.set index (Item.scalar (least + delta).toNat)
  | .error _ => fields

/-- A change of the bytes after the encoding. -/
inductive Tweak where
  /-- No change. -/
  | none
  /-- A byte after the end. -/
  | trailing
  /-- Another first byte. -/
  | first (byte : UInt8)
  /-- The last byte removed. -/
  | short
  deriving Repr

/-- The bytes after a tweak. -/
def Tweak.apply (bytes : ByteArray) : Tweak → ByteArray
  | .none => bytes
  | .trailing => bytes ++ ⟨#[0]⟩
  | .first byte => ⟨#[byte]⟩ ++ bytes.extract 1 bytes.size
  | .short => bytes.extract 0 (bytes.size - 1)

/-- Mostly no tweak. -/
def genTweak : Gen Tweak :=
  Gen.frequency [(12, pure .none), (1, pure .trailing), (1, pure .short),
    (2, Tweak.first <$> Gen.element [0, 1, 2, 3, 4, 5, 0x7f, 0x80, 0xc0, 0xf8, 0xff])]

/-- An almost valid transaction as bytes, at a fork and on a chain. -/
structure TxCase where
  /-- The fork, and its name in the reference. -/
  fork : Fork × String
  /-- The chain of the network. -/
  chain : Nat
  /-- The bytes of the transaction. -/
  bytes : ByteArray

instance : Repr TxCase where
  reprPrec c _ := s!"{c.fork.2} chain {c.chain} {hex c.bytes}"

/-- A transaction of any type, at a fork of a list.

Half the time its gas limit is near the least one. -/
def genTxCase (forks : List (Fork × String)) : Gen TxCase := do
  -- One case in three is from Dencun on, where a transaction has blobs or authorizations.
  let late := forks.filter fun fork => fork.1 ≥ .dencun
  let fork ← Gen.frequency [(2, genForkOf forks),
    (1, genForkOf (if late.isEmpty then forks else late))]
  let chain ← genChain
  -- Mostly a type that the fork has, and now and then any type.
  let types := (List.range 5).filter fun type =>
    type = 0 ∨ (typeFork (UInt8.ofNat type)).any (· ≤ fork.1)
  -- The newest type of the fork nearly as often as all the older ones.
  let type ← Gen.frequency [(5, Gen.element types.reverse), (4, pure (types.getLastD 0)),
    (1, Gen.nat (.constant 0 4))]
  let (fields, gasIndex) ← genFields type chain
  let delta ← Gen.option (Gen.int (.constantFrom 0 (-2) 2))
  let fields := match delta with
    | some delta => nearMinimum fork.1 type gasIndex delta fields
    | none => fields
  let mutations ← Gen.frequency [(3, pure []), (1, Gen.list (.constant 1 2) genMutation)]
  let tweak ← genTweak
  pure ⟨fork, chain, tweak.apply (txBytes type (mutateAll mutations (.list fields)))⟩

/-- What EthLib says of the bytes of a transaction, in the words of the oracle. -/
def describeTx (fork : Fork) (chain : Nat) (bytes : ByteArray) : String :=
  match decodeTransaction fork bytes with
  | .error _ => "error"
  | .ok tx =>
    -- The reference types the nonce of a set code transaction on 64 bits, so it reads none above.
    --
    -- EthLib reads it and then refuses it by EIP-2681: the same verdict, at a later step.
    if tx.type = 4 ∧ tx.nonce.toNat ≥ 2 ^ 64 then "error" else
    let hash := orError (hexV <$> transactionHash tx)
    let sender := checkChainId fork (UInt64.ofNat chain) tx *> recoverSender fork tx
    let who := sender.toOption.getD (Vector.replicate 20 0)
    let valid := (validateTransaction fork who tx *> checkContents fork tx).isOk
    let floor := if fork ≥ .pectra then calldataFloor fork who tx else 0
    let senderText := match sender with
      | .ok address => hexV address
      | .error _ => "badsig"
    s!"ok {hash} {senderText} {intrinsicGas fork who tx} {floor} {valid}"

/-- The labels of the bytes of a transaction: its form, and how far the rules take it. -/
def labelTxCase (fork : Fork) (chain : Nat) (bytes : ByteArray) :
    TestT IO Unit := do
  labelFork fork
  let first := bytes.data.getD 0 0
  label (if bytes.isEmpty then "form: no byte"
    else if 0xc0 ≤ first then "form: legacy"
    else if 1 ≤ first ∧ first ≤ 4 then s!"form: type {first}"
    else "form: another first byte")
  classify "form: a type that the fork does not have yet"
    ((typeFork first).any fun since => first < 0xc0 && fork < since)
  match decodeTransaction fork bytes with
  | .error error => label s!"verdict: no transaction, {errorName error}"
  | .ok tx =>
    if let .legacy legacy := tx then
      let v := legacy.v.toNat
      label (if v = 27 ∨ v = 28 then "legacy: signs no chain"
        else if 35 ≤ v then "legacy: signs a chain (EIP-155)" else "legacy: another v")
      coverMin 1 "legacy: signs a chain before Spurious Dragon" (35 ≤ v && fork < .spuriousDragon)
    coverMin 3 "a contract creation" tx.to.isNone
    coverMin 3 "an access list with an entry" (!tx.accesses.isEmpty)
    coverMin 17 "call data with a byte" (!tx.data.isEmpty)
    classify "init code above the limit of EIP-3860" (tx.to.isNone && 49152 < tx.data.size)
    if let .blob blob := tx then
      let count := blob.blobVersionedHashes.length
      label (if count = 0 then "blobs: 0" else if count ≤ 6 then "blobs: 1 to 6" else "blobs: 7+")
    if let .setCode setCode := tx then
      label (if setCode.authorizations.isEmpty then "authorizations: 0" else "authorizations: 1+")
    let chainOk := (checkChainId fork (UInt64.ofNat chain) tx).isOk
    let sender := recoverSender fork tx
    let who := sender.toOption.getD (Vector.replicate 20 0)
    let rules := validateTransaction fork who tx *> checkContents fork tx
    let least := minimumGas fork who tx
    let gas := tx.gas.toNat
    label (if gas + 1 = least then "gas: one below the least" else if gas < least then
      "gas: further below the least" else if gas = least then "gas: the least"
      else if gas = least + 1 then "gas: one above the least" else "gas: further above the least")
    coverMin 1 "the floor of EIP-7623 is above the intrinsic gas"
      (fork ≥ .pectra && intrinsicGas fork who tx < calldataFloor fork who tx)
    coverMin 5 "sender: recovered" sender.isOk
    classify "sender: recovered, on another chain" (sender.isOk && !chainOk)
    match rules with
    | .ok _ =>
      label (if !chainOk then "verdict: a transaction, valid but for its chain"
        else if sender.isOk then "verdict: a transaction, valid, with a sender"
        else "verdict: a transaction, valid but for its signature")
      if chainOk ∧ sender.isOk then label s!"valid with a sender: type {tx.type}"
    | .error error => label s!"verdict: a transaction, invalid, {errorName error}"

/-- `checkTransaction` accepts a transaction exactly when its parts do, as the reference answered.

The answer names a sender and the verdict `true` exactly for a transaction that passes whole.

It then gives the sender and the intrinsic gas of the answer. -/
def checkedAsDescribed (fork : Fork) (chain : Nat) (bytes : ByteArray) (answer : String) :
    TestT IO Unit := do
  match decodeTransaction fork bytes, answer.splitOn " " with
  | .ok tx, ["ok", _, who, intrinsic, _, valid] =>
    let whole := checkTransaction fork (UInt64.ofNat chain) tx
    whole.isOk === (who != "badsig" && valid == "true")
    if let .ok (sender, gas) := whole then
      hexV sender === who
      toString gas === intrinsic
  | _, _ => pure ()

/-- EthLib and execution-specs agree on the bytes of a transaction.

They agree on whether the bytes hold a transaction of the fork.

Then they agree on its hash, its sender on the chain, its intrinsic gas and its floor.

They also agree on whether the rules that read no state accept it. -/
def transactionBytes (oracles : Oracles) : Property IO := propertyM do
  let c ← forAll (genTxCase oracles.forks)
  pure do
    labelTxCase c.fork.1 c.chain c.bytes
    let expected ← (oracles.at c.fork).ask ["tx", c.fork.2, toString c.chain, hex c.bytes]
    describeTx c.fork.1 c.chain c.bytes === expected
    checkedAsDescribed c.fork.1 c.chain c.bytes expected

/-- A transaction as an item of a block body, at a fork. -/
structure BodyCase where
  /-- The fork, and its name in the reference. -/
  fork : Fork × String
  /-- The item of the body. -/
  item : Item

instance : Repr BodyCase where
  reprPrec c _ := s!"{c.fork.2} {hex (enc c.item)}"

/-- An item of a block body: a list, the bytes of a typed transaction, or the bytes of a list. -/
def genBodyCase (forks : List (Fork × String)) : Gen BodyCase := do
  -- One case in four is from Glamsterdam on, where the bytes of a list are read.
  let late := forks.filter fun fork => fork.1 ≥ .glamsterdam
  let c ← Gen.frequency [(3, genTxCase forks),
    (1, genTxCase (if late.isEmpty then forks else late))]
  let asList : Option Item := match decode c.bytes with
    | .ok (.list items) => some (.list items)
    | _ => none
  let item ← match asList with
    | some list => Gen.frequency [(3, pure list), (2, pure (Item.bytes c.bytes)),
        (1, pure (Item.bytes (⟨#[0xff]⟩ ++ c.bytes.extract 1 c.bytes.size)))]
    | none => Gen.frequency [(9, pure (Item.bytes c.bytes)), (1, pure (.bytes .empty))]
  pure ⟨c.fork, item⟩

/-- EthLib and execution-specs agree on a transaction as an item of a block body.

A list is a legacy transaction, and a byte string a typed one: its type, then its payload.

From Glamsterdam the reference also reads a byte string that holds a list, and so does EthLib.

Before it, both refuse that form. -/
def bodyTransaction (oracles : Oracles) : Property IO := propertyM do
  let c ← forAll (genBodyCase oracles.forks)
  pure do
    labelFork c.fork.1
    let first : UInt8 := match c.item with
      | .bytes bytes => bytes.data.getD 0 0
      | .list _ => 0
    label (match c.item with
      | .list _ => "form: a list"
      | .bytes bytes => if bytes.isEmpty then "form: no byte" else if 0xc0 ≤ first then
          "form: the bytes of a list" else if 1 ≤ first ∧ first ≤ 4 then "form: a typed transaction"
          else "form: another first byte")
    classify "the bytes of a list, from Glamsterdam" (0xc0 ≤ first && c.fork.1 ≥ .glamsterdam)
    coverMin 5 "the bytes of a list, before Glamsterdam" (0xc0 ≤ first && c.fork.1 < .glamsterdam)
    coverMin 1 "the bytes of a list that start with 0xff" (first = 0xff)
    let got := match decodeBodyTransaction c.fork.1 c.item with
      | .error _ => "error"
      | .ok tx =>
        if tx.type = 4 ∧ tx.nonce.toNat ≥ 2 ^ 64 then "error"
        else s!"ok {orError (hexV <$> transactionHash tx)}"
    label (match decodeBodyTransaction c.fork.1 c.item with
      | .ok tx => s!"verdict: a transaction of type {tx.type}"
      | .error error => s!"verdict: no transaction, {errorName error}")
    got === (← (oracles.at c.fork).ask ["txbody", c.fork.2, hex (enc c.item)])
    -- The item that EthLib writes for the transaction reads back as the same transaction.
    if let .ok tx := decodeBodyTransaction c.fork.1 c.item then
      match bodyItem tx with
      | .error _ => failWith "the transaction has no item"
      | .ok item =>
        (decodeBodyTransaction c.fork.1 item).toOption.map (orError <| hexV <$> transactionHash ·)
          === some (orError (hexV <$> transactionHash tx))
        -- A list and the bytes of a typed transaction are the forms that EthLib writes.
        if first < 0xc0 then hex (enc item) === hex (enc c.item)

end ExecutionProperty

namespace ExecutionProperty

/-! ## Transactions that eth-account signs -/

/-- A private key: any, or one at an end of the range. -/
def genKey : Gen Nat :=
  Gen.frequency [(4, Gen.nat (.constant 1 (curveOrder - 1))),
    (1, Gen.element [1, 2, curveOrder - 1])]

/-- An item of 20 bytes. -/
def genAddressItem : Gen Item := (fun (a : Address) => Item.bytes ⟨a.toArray⟩) <$> genAddress

/-- The fields before the signature of a valid transaction of a type on a chain.

A legacy transaction ends with its chain, where 0 is for none.

An authorization ends with the key of its authority, in place of a signature. -/
def genUnsigned (type chain : Nat) : Gen Item := do
  let nonce ← genScalar 64
  let fee ← genScalar 256
  let tip ← genScalar 256
  let gas ← genScalar 64
  let to ← if type ≥ 3 then genAddressItem else genTo
  let value ← genScalar 256
  let data ← Item.bytes <$> genData
  let accessList ← genAccessList
  let chainId := Item.scalar chain
  let authorization := (fun (c : Nat) a n (k : Nat) => Item.list [.scalar c, a, n, .scalar k]) <$>
    Gen.element [0, chain, 2 ^ 256 - 1] <*> genAddressItem <*> genScalar 64 [2 ^ 64 - 1] <*> genKey
  match type with
  | 0 => pure (.list [nonce, fee, gas, to, value, data, chainId])
  | 1 => pure (.list [chainId, nonce, fee, gas, to, value, data, accessList])
  | 2 => pure (.list [chainId, nonce, tip, fee, gas, to, value, data, accessList])
  | 3 => do
    let hashes ← Gen.list (.linear 1 6) genVersionedHash
    pure (.list [chainId, nonce, tip, fee, gas, to, value, data, accessList, ← genScalar 256,
      .list hashes])
  | _ => do
    let authorizations ← Gen.list (.linear 1 3) authorization
    pure (.list [chainId, nonce, tip, fee, gas, to, value, data, accessList,
      .list authorizations])

/-- The transaction with the other signature of the same key: `s` negated and the parity flipped.

It is the malleable twin that EIP-2 refuses from Homestead. -/
def highTwin : Transaction → Transaction
  | .legacy tx =>
    let v := tx.v.toNat
    .legacy { tx with s := BitVec.ofNat 256 (curveOrder - tx.s.toNat),
                      v := BitVec.ofNat 256 (if v % 2 = 1 then v + 1 else v - 1) }
  | .accessList tx => .accessList { tx with s := BitVec.ofNat 256 (curveOrder - tx.s.toNat),
                                            yParity := 1 - tx.yParity }
  | .feeMarket tx => .feeMarket { tx with s := BitVec.ofNat 256 (curveOrder - tx.s.toNat),
                                          yParity := 1 - tx.yParity }
  | .blob tx => .blob { tx with s := BitVec.ofNat 256 (curveOrder - tx.s.toNat),
                                yParity := 1 - tx.yParity }
  | .setCode tx => .setCode { tx with s := BitVec.ofNat 256 (curveOrder - tx.s.toNat),
                                      yParity := 1 - tx.yParity }

/-- EthLib reads a transaction that eth-account signed as eth-account wrote it.

The bytes decode and encode back.

The hash, the signing hash and the sender are those of eth-account.

So is the authority of each authorization.

A legacy transaction that signs a chain has no sender before Spurious Dragon.

The twin with a high `s` has no sender from Homestead, and the same sender in Frontier. -/
def signedTransaction (oracle : Oracle) : Property IO := propertyM do
  let type ← forAll (Gen.nat (.constant 0 4))
  let chain ← forAll (if type = 0 then Gen.frequency [(1, pure 0), (3, genChain)] else genChain)
  let key ← forAll genKey
  let fields ← forAllWith (fun item => hex (enc item)) (genUnsigned type chain)
  pure do
    let answer ← oracle.ask ["signed", toString type, hex (bytesOf (natToBytes 32 key)),
      hex (enc fields)]
    let [raw, hash, sender, signing, authorities] := answer.splitOn " "
      | failWith s!"the oracle answered {answer}"
    let some bytes := unhex? raw | failWith "the oracle answered no bytes"
    annotate s!"raw {raw}"
    label s!"type {type}"
    coverMin 1 "legacy: signs no chain" (type = 0 && chain = 0)
    coverMin 4 "legacy: signs a chain (EIP-155)" (type = 0 && chain ≠ 0)
    coverMin 16 "chain: 2^63 or more" (2 ^ 63 ≤ chain)
    match decodeTransaction .pectra bytes with
    | .error error => failWith s!"EthLib does not decode it: {repr error}"
    | .ok tx =>
      coverMin 3 "a contract creation" tx.to.isNone
      coverMin 3 "an access list with an entry" (!tx.accesses.isEmpty)
      coverMin 17 "call data with a byte" (!tx.data.isEmpty)
      coverMin 3 "an authorization for every chain" (tx.authorizations.any (·.chainId == 0))
      coverMin 4 "an authorization for a chain" (tx.authorizations.any (·.chainId != 0))
      orError (hex <$> encodeTransaction tx) === raw
      orError (hexV <$> transactionHash tx) === hash
      orError (hexV <$> recoverSender .pectra tx) === sender
      orError ((fun input => hexV input.1) <$> signingInput .pectra tx) === signing
      orError (hexV <$> recoverSender .tangerineWhistle tx) ===
        (if type = 0 ∧ chain ≠ 0 then "error" else sender)
      orError (hexV <$> recoverSender .spuriousDragon tx) === sender
      (checkChainId .pectra (UInt64.ofNat chain) tx).isOk === true
      (checkChainId .pectra (UInt64.ofNat (chain + 1)) tx).isOk === (type = 0 && chain = 0)
      let found := tx.authorizations.map fun a => ((recoverAuthority a).map hexV).getD "none"
      (if found.isEmpty then "-" else ",".intercalate found) === authorities
      -- EIP-2: the twin with `s > n / 2` is invalid from Homestead.
      orError (hexV <$> recoverSender .pectra (highTwin tx)) === "error"
      orError (hexV <$> recoverSender .homestead (highTwin tx)) === "error"
      if type = 0 ∧ chain = 0 then
        orError (hexV <$> recoverSender .frontier (highTwin tx)) === sender

/-- The authority of an authorization is the one that execution-specs recovers, or neither has one.

Half the authorizations are those of a transaction that eth-account signed.

One of them in three then takes the other signature of its key, with `s` above half the order.

EIP-7702 refuses that one, as it refuses a parity above 1 and an `r` or `s` out of range.

The other half has each field in its range or just outside it, with a signature of no key. -/
def authorityOf (oracle : Oracle) : Property IO := propertyM do
  let chain ← forAll genChain
  let key ← forAll genKey
  let fields ← forAllWith (fun item => hex (enc item)) (genUnsigned 4 chain)
  let loose ← forAllWith (fun item => hex (enc item)) (genAuthorization chain)
  let pick ← forAll (Gen.nat (.constant 0 5))
  pure do
    let answer ← oracle.ask ["signed", "4", hex (bytesOf (natToBytes 32 key)), hex (enc fields)]
    let signed : List Authorization := match (answer.splitOn " ").head? >>= unhex? with
      | some bytes => ((decodeTransaction .pectra bytes).map (·.authorizations)).toOption.getD []
      | none => []
    let twin (a : Authorization) : Authorization :=
      { a with s := BitVec.ofNat 256 (curveOrder - a.s.toNat), yParity := 1 - a.yParity }
    let item : Item ← match pick, signed.head? with
      | 0, some a | 1, some a => do
        label "an authorization that eth-account signed"
        pure (Codec.toItem a)
      | 2, some a => do
        label "the other signature of the key, with a high s"
        pure (Codec.toItem (twin a))
      | _, _ => do
        label "fields at their edges, with a signature of no key"
        pure loose
    let bytes := enc item
    let got := match (Codec.decode bytes : Except RlpError Authorization) with
      | .error _ => "error"
      | .ok a => ((recoverAuthority a).map hexV).getD "error"
    coverMin 14 "an authority is recovered" (got != "error")
    coverMin 18 "no authority" (got == "error")
    got === (← oracle.ask ["authority", hex bytes])

/-- The fields of a transaction that eth-account signs, with a signature of no meaning.

The result decodes, so that the least gas limit of the fields can be read. -/
def withDummySignature (type : Nat) : Item → Item
  | .list fields =>
    if type = 0 then .list (fields.take 6 ++ [.scalar 27, .scalar 1, .scalar 1])
    else
      let fields := if type = 4 then fields.map fun
          | .list entries => .list (entries.map fun
            | .list [chain, address, nonce, _] =>
              .list [chain, address, nonce, .scalar 0, .scalar 1, .scalar 1]
            | entry => entry)
          | field => field
        else fields
      .list (fields ++ [.scalar 0, .scalar 1, .scalar 1])
  | item => item

/-- The fields before the signature of a transaction that is valid, or has one field at an edge.

The gas limit is the least one of the fork, one beside it, more, or at a cap of a later fork.

The nonce reaches the bound of EIP-2681, and the priority fee the maximum fee and one above. -/
def genSignable (fork : Fork) (type chain : Nat) : Gen Item := do
  let nonce ← Item.scalar <$> Gen.frequency [(8, Gen.nat (.exponential 0 (2 ^ 64 - 3))),
    (1, pure (2 ^ 64 - 2)), (1, pure (2 ^ 64 - 1))]
  let fee ← Gen.nat (.exponential 0 (2 ^ 64))
  let tip ← Gen.frequency [(6, Gen.nat (.constant 0 fee)), (2, pure fee), (1, pure (fee + 1))]
  let to ← if type ≥ 3 then genAddressItem
    else Gen.frequency [(2, genAddressItem), (1, pure (.bytes .empty))]
  let value ← genScalar 256
  -- Init code around the limit of EIP-3860, and around twice and half of it.
  let large := (fun (n : Nat) (b : UInt8) => bytesOf (List.replicate n b)) <$>
    Gen.element [24576, 24577, 49151, 49152, 49153, 65536, 65537, 98304, 98305] <*>
    Gen.element [0, 1]
  let data ← Item.bytes <$> (if to == .bytes .empty then
      Gen.frequency [(if fork ≥ .shapella then 2 else 6, genData), (1, large)]
    else genData)
  let accessList ← genAccessList
  let chainId := Item.scalar chain
  let authorization := (fun (c : Nat) a n (k : Nat) => Item.list [.scalar c, a, n, .scalar k]) <$>
    Gen.element [0, chain, chain + 1] <*> genAddressItem <*> genScalar 64 [2 ^ 64 - 1] <*> genKey
  let gas := Item.scalar 0
  let (fields, gasIndex) ← match type with
    | 0 => pure ([nonce, .scalar fee, gas, to, value, data, chainId], 2)
    | 1 => pure ([chainId, nonce, .scalar fee, gas, to, value, data, accessList], 3)
    | 2 => pure ([chainId, nonce, .scalar tip, .scalar fee, gas, to, value, data, accessList], 4)
    | 3 => do
      let hashes ← Gen.frequency [(5, Gen.list (.constant 1 6) genVersionedHash),
        (1, Gen.list (.singleton 6) genVersionedHash), (1, pure []),
        (if fork ≥ .fusaka then 3 else 1, Gen.list (.constant 7 9) genVersionedHash)]
      pure ([chainId, nonce, .scalar tip, .scalar fee, gas, to, value, data, accessList,
        ← genScalar 256, .list hashes], 4)
    | _ => do
      let authorizations ← Gen.frequency [(1, pure []),
        (6, Gen.list (.constant 1 3) authorization)]
      pure ([chainId, nonce, .scalar tip, .scalar fee, gas, to, value, data, accessList,
        .list authorizations], 4)
  let least := match decodeTransaction .hegota
      (txBytes type (withDummySignature type (.list fields))) with
    | .ok tx => minimumGas fork (Vector.replicate 20 0) tx
    | .error _ => 21000
  let limit ← Gen.frequency [(2, pure (least - 1)), (5, pure least), (2, pure (least + 1)),
    (2, (least + ·) <$> Gen.nat (.exponential 0 1000000)),
    (if fork ≥ .fusaka then 5 else 1,
      Gen.element [2 ^ 24 - 1, 2 ^ 24, 2 ^ 24 + 1, 2 ^ 32 - 1, 2 ^ 32])]
  pure (.list (fields.set gasIndex (.scalar limit)))

/-- A transaction to sign: a fork, a type that the fork mostly has, a chain, a key and fields. -/
structure SignCase where
  /-- The fork, and its name in the reference. -/
  fork : Fork × String
  /-- The type of the transaction. -/
  type : Nat
  /-- The chain that the transaction signs, where 0 is none for a legacy transaction. -/
  chain : Nat
  /-- The chain of the network. -/
  network : Nat
  /-- The private key. -/
  key : Nat
  /-- The fields before the signature. -/
  fields : Item

instance : Repr SignCase where
  reprPrec c _ := s!"{c.fork.2} type {c.type} chain {c.chain} network {c.network} key {c.key} \
    fields {hex (enc c.fields)}"

/-- A transaction to sign at a fork of a list. -/
def genSignCase (forks : List (Fork × String)) : Gen SignCase := do
  let fork ← genForkOf forks
  let types := (List.range 5).filter fun type =>
    type = 0 ∨ (typeFork (UInt8.ofNat type)).any (· ≤ fork.1)
  -- The newest type of the fork as often as all the older ones.
  let type ← Gen.frequency [(8, Gen.element types.reverse), (8, pure (types.getLastD 0)),
    (if types.contains 3 then 3 else 0, pure 3), (1, Gen.nat (.constant 0 4))]
  let chain ← if type = 0 then Gen.frequency [(1, pure 0), (2, genChain)] else genChain
  let network ← Gen.frequency [(12, pure (if chain = 0 then 1 else chain)), (1, pure (chain + 1))]
  pure ⟨fork, type, chain, network, ← genKey, ← genSignable fork.1 type chain⟩

/-- A transaction that eth-account signed is valid at a fork exactly when the reference says so.

The signature is a real one, so the sender is recovered and every rule after it is reached.

The fields are valid, or one of them is at an edge of its rule:

- The gas limit is the least one, one below, one above, or at a cap.
- The nonce is at the bound of EIP-2681.
- The priority fee is the maximum fee, or one above it.
- The init code is at the limit of EIP-3860, or a byte above.
- A blob transaction holds up to nine blobs.

EthLib and execution-specs then agree on the hash, the sender, the intrinsic gas and the floor.

They also agree on the verdict.

The sender is the address of the key, as eth-account says. -/
def signedValid (oracles : Oracles) : Property IO := propertyM do
  let c ← forAll (genSignCase oracles.forks)
  pure do
    let answer ← oracles.main.ask ["signed", toString c.type,
      hex (bytesOf (natToBytes 32 c.key)), hex (enc c.fields)]
    classify "eth-account does not sign the fields" (answer.startsWith "error")
    let [raw, _, sender, _, _] := answer.splitOn " "
      | if answer.startsWith "error" then pure () else failWith s!"the oracle answered {answer}"
    let some bytes := unhex? raw | failWith "the oracle answered no bytes"
    annotate s!"raw {raw}"
    labelTxCase c.fork.1 c.network bytes
    let got := describeTx c.fork.1 c.network bytes
    got === (← (oracles.at c.fork).ask ["tx", c.fork.2, toString c.network, raw])
    checkedAsDescribed c.fork.1 c.network bytes got
    match got.splitOn " " with
    | ["ok", _, who, _, _, _] => if who ≠ "badsig" then who === sender
    | _ => pure ()

end ExecutionProperty

namespace ExecutionProperty

/-- The rules of a transaction that read no state and no signature, each at its edge.

The model is in `Nat`, from the texts of the EIPs, at every fork before Glamsterdam:

- EIP-3860, from Shapella: init code has at most 49152 bytes.
- EIP-7825, from Fusaka: the gas limit is at most `2^24`.
- EIP-4844, from Dencun: a blob transaction has a blob, and each hash has the version 1.
- EIP-7594, from Fusaka: it has at most six blobs.
- EIP-7702, from Pectra: a set code transaction has an authorization.
- EIP-2681: the nonce is below `2^64 - 1`.
- EIP-1559, from London: the priority fee is at most the maximum fee.

A type that the fork does not have yet is refused.

No signature is read, so the transactions are built as values, with a gas limit that is enough.

eth-account signs no blob transaction without a blob and no empty list of authorizations.

So this is where those two refusals are reached. -/
def staticRules : Property IO := propertyM do
  let forks := (releaseForks ++ lateForks).filter fun fork => fork.1 < .glamsterdam
  let kind ← forAll (Gen.nat (.constant 0 4))
  -- Three cases in four are at a fork that has the rule.
  let since : Fork := [.shapella, .fusaka, .dencun, .pectra, .london].getD kind .london
  let fork ← forAllWith (·.1.name) (Gen.frequency [(1, genForkOf forks),
    (3, genForkOf (forks.filter fun fork => fork.1 ≥ since))])
  let size ← forAll (Gen.element [49151, 49152, 49153])
  let gas ← forAll (Gen.element [2 ^ 24 - 1, 2 ^ 24, 2 ^ 24 + 1])
  let blobs ← forAll (Gen.element [0, 1, 6, 7, 9])
  let version ← forAll (Gen.frequency [(3, pure (1 : UInt8)), (1, Gen.element [0, 2, 0xff])])
  let spot ← forAll (Gen.nat (.constant 0 8))
  let authorizations ← forAll (Gen.nat (.constant 0 2))
  let nonce ← forAll (Gen.element [2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64])
  let fee ← forAll (Gen.nat (.constant 1 100))
  let tip ← forAll (Gen.element [fee - 1, fee, fee + 1])
  pure do
    let word (n : Nat) : U256 := .ofNat 256 n
    let to : Address := Vector.replicate 20 9
    let enough := 2 ^ 24
    let hashes : List Bytes32 := (List.range blobs).map fun i =>
      (Vector.replicate 32 (7 : UInt8)).set! 0 (if i = spot % max 1 blobs then version else 1)
    let tx : Transaction := match kind with
      | 0 => .legacy ⟨0, 1, word enough, none, 0, bytesOf (List.replicate size 0), 27, 1, 1⟩
      | 1 => .legacy ⟨0, 1, word gas, some to, 0, .empty, 27, 1, 1⟩
      | 2 => .blob ⟨1, 0, 0, 1, word enough, to, 0, .empty, [], 1, hashes, 0, 1, 1⟩
      | 3 => .setCode ⟨1, 0, 0, 1, word enough, to, 0, .empty, [],
        List.replicate authorizations ⟨0, to, 0, 0, 1, 1⟩, 0, 1, 1⟩
      | _ => .feeMarket ⟨1, word nonce, word tip, word fee, word enough, some to, 0, .empty, [], 0,
        1, 1⟩
    let f := fork.1
    let expected : Bool := match kind with
      | 0 => f < .shapella || size ≤ 49152
      | 1 => f < .fusaka || gas ≤ 2 ^ 24
      | 2 => f ≥ .dencun && 0 < blobs && (f < .fusaka || blobs ≤ 6) &&
        (version = 1 || blobs = 0)
      | 3 => f ≥ .pectra && 0 < authorizations
      | _ => f ≥ .london && nonce < 2 ^ 64 - 1 && tip ≤ fee
    let result := validateTransaction f (Vector.replicate 20 1) tx *> checkContents f tx
    labelFork f
    label (match result with
      | .ok _ => "verdict: valid"
      | .error error => s!"verdict: invalid, {errorName error}")
    coverMin 1 "init code of 49152 bytes, from Shapella" (kind = 0 && f ≥ .shapella && size = 49152)
    coverMin 1 "init code of 49153 bytes, from Shapella" (kind = 0 && f ≥ .shapella && size = 49153)
    coverMin 1 "a gas limit of 2^24, from Fusaka" (kind = 1 && f ≥ .fusaka && gas = 2 ^ 24)
    coverMin 1 "a gas limit of 2^24 + 1, from Fusaka" (kind = 1 && f ≥ .fusaka && gas = 2 ^ 24 + 1)
    coverMin 1 "no blob, from Dencun" (kind = 2 && f ≥ .dencun && blobs = 0)
    classify "six blobs, from Fusaka" (kind = 2 && f ≥ .fusaka && blobs = 6)
    classify "seven blobs or more, from Fusaka" (kind = 2 && f ≥ .fusaka && 6 < blobs)
    coverMin 1 "seven blobs or more, before Fusaka" (kind = 2 && f ≥ .dencun && f < .fusaka &&
      6 < blobs)
    coverMin 1 "a hash of another version, from Dencun" (kind = 2 && f ≥ .dencun && 0 < blobs &&
      version ≠ 1)
    coverMin 1 "no authorization, from Pectra" (kind = 3 && f ≥ .pectra && authorizations = 0)
    coverMin 3 "an authorization, from Pectra" (kind = 3 && f ≥ .pectra && 0 < authorizations)
    coverMin 1 "a nonce of 2^64 - 2, from London" (kind = 4 && f ≥ .london && nonce = 2 ^ 64 - 2)
    coverMin 2 "a nonce of 2^64 - 1, from London" (kind = 4 && f ≥ .london && nonce = 2 ^ 64 - 1)
    coverMin 2 "a priority fee above the maximum fee" (kind = 4 && f ≥ .london && fee < tip)
    coverMin 3 "a type that the fork does not have yet" (2 ≤ kind && tx.fork > f)
    result.isOk === expected

open EthLib.Execution.State in
/-- The sender of a transaction may send it exactly when the rules of its EIPs say so.

The model is in `Nat`, from the text of EIP-1559, EIP-4844, EIP-3607 and EIP-7702.

The nonce of the sender is the nonce of the transaction.

Its balance covers the gas limit at the maximum fee, the blob gas at its maximum fee, and the value.

It has no code, or from Pectra a delegation indicator: `0xef0100`, then 20 bytes.

The forks are all 29 of EthLib, and half the cases are from Pectra on.

The price that the sender pays is the price of EIP-1559: the base fee plus the capped priority. -/
def senderRules : Property IO := propertyM do
  let forks := releaseForks ++ lateForks
  let fork ← forAllWith (·.1.name) (Gen.frequency [(1, genForkOf forks),
    (1, genForkOf (forks.filter fun fork => fork.1 ≥ .pectra))])
  let type ← forAll (Gen.nat (.constant 0 4))
  let gas ← forAll (Gen.nat (.constant 21000 30000))
  let fee ← forAll (Gen.nat (.exponential 0 (2 ^ 70)))
  let tip ← forAll (Gen.nat (.exponential 0 (2 ^ 70)))
  let value ← forAll (Gen.nat (.exponential 0 (2 ^ 70)))
  let blobs ← forAll (Gen.nat (.constant 1 6))
  let blobFee ← forAll (Gen.nat (.exponential 0 (2 ^ 40)))
  let nonce ← forAll (Gen.nat (.constant 0 5))
  let senderNonce ← forAll (Gen.frequency [(3, pure nonce), (1, Gen.nat (.constant 0 6))])
  let cost := gas * fee + value + (if type = 3 then 131072 * blobs * blobFee else 0)
  let balance ← forAll (Gen.frequency [(2, pure cost), (1, pure (cost - 1)), (1, pure (cost + 1)),
    (1, Gen.nat (.exponential 0 (2 ^ 100)))])
  let code ← forAllWith hex (Gen.frequency [(3, pure .empty),
    (3, pure (bytesOf ([0xef, 0x01, 0x00] ++ List.replicate 20 7))),
    (2, (fun n => bytesOf ([0xef, 0x01, 0x00] ++ List.replicate n 7)) <$> Gen.element [19, 21]),
    (1, pure (bytesOf ([0xef, 0x01, 0x01] ++ List.replicate 20 7))),
    (1, pure (bytesOf ([0xef, 0x00, 0x00] ++ List.replicate 20 7))),
    (1, pure ⟨#[0]⟩)])
  let baseFee ← forAll (Gen.frequency [(2, Gen.nat (.constant 0 fee)), (1, pure fee)])
  pure do
    let word (n : Nat) : U256 := .ofNat 256 n
    let to : Address := Vector.replicate 20 9
    let tx : Transaction := match type with
      | 0 => .legacy ⟨word nonce, word fee, word gas, some to, word value, .empty, 27, 1, 1⟩
      | 1 => .accessList ⟨1, word nonce, word fee, word gas, some to, word value, .empty, [], 0, 1,
        1⟩
      | 2 => .feeMarket ⟨1, word nonce, word tip, word fee, word gas, some to, word value, .empty,
        [], 0, 1, 1⟩
      | 3 => .blob ⟨1, word nonce, word tip, word fee, word gas, to, word value, .empty, [],
        word blobFee, List.replicate blobs (Vector.replicate 32 1), 0, 1, 1⟩
      | _ => .setCode ⟨1, word nonce, word tip, word fee, word gas, to, word value, .empty, [],
        [⟨0, to, 0, 0, 1, 1⟩], 0, 1, 1⟩
    let sender : Address := Vector.replicate 20 1
    let empty : TransactionState := .ofBlock ⟨⟨∅, ∅, ∅⟩, ∅, ∅, ∅, ∅⟩
    let .ok funded := (do
        let state ← empty.setAccountBalance .frontier sender (word balance)
        let state ← state.setCode .frontier sender code
        (List.range senderNonce).foldlM
          (fun (state : TransactionState) _ => state.incrementNonce .frontier sender) state)
      | failWith "the state of the sender does not build"
    let delegation := code.size = 23 ∧ code.data.toList.take 3 = [0xef, 0x01, 0x00]
    let expected := nonce = senderNonce ∧ cost ≤ balance ∧
      (code.isEmpty ∨ (fork.1 ≥ Fork.pectra ∧ delegation))
    labelFork fork.1
    label s!"type {type}"
    label (if decide expected then "verdict: may send"
      else match checkSender fork.1 funded sender tx with
        | .error error => s!"verdict: refused, {errorName error}"
        | .ok _ => "verdict: accepted against the model")
    label (if balance + 1 = cost then "balance: one wei short" else if balance < cost then
      "balance: further short" else if balance = cost then "balance: exact" else "balance: more")
    label (if nonce = senderNonce then "nonce: the sender's" else if senderNonce < nonce then
      "nonce: above the sender's" else "nonce: below the sender's")
    label (if code.isEmpty then "code: none" else if delegation then "code: a delegation indicator"
      else "code: other")
    coverMin 3 "a delegation indicator before Pectra" (delegation && fork.1 < .pectra)
    coverMin 6 "a delegation indicator from Pectra" (delegation && fork.1 ≥ .pectra)
    coverMin 16 "the tip is capped by the fee" (2 ≤ type && fee - baseFee < tip)
    coverMin 3 "the tip is paid whole" (2 ≤ type && tip ≤ fee - baseFee)
    (checkSender fork.1 funded sender tx).isOk === decide expected
    -- EIP-1559: `priority_fee_per_gas = min(max_priority_fee_per_gas, max_fee_per_gas - base_fee)`.
    effectiveGasPrice baseFee tx === (if type < 2 then fee else baseFee + min tip (fee - baseFee))

end ExecutionProperty

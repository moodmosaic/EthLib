import Property.Execution.Common

/-!
# Transactions as bytes, against execution-specs

A transaction is generated as an RLP item, field by field, with values at the edges that the
rules name.
It is then changed a little, so that most inputs are almost valid.
EthLib and the reference must agree on whether the bytes hold a transaction, and on its hash,
its sender, its intrinsic gas, its floor and its validity.
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
    (2, Gen.element [0, 20999, 21000, 2 ^ 24 - 1, 2 ^ 24, 2 ^ 24 + 1, 2 ^ 64, 2 ^ 256 - 1])]

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
    Gen.frequency [(8, pure 1), (1, Gen.element [0, 2, 0xff])] <*> genBytesN 31

/-- The versioned hashes of a blob transaction: now and then none, or more than six. -/
def genVersionedHashes : Gen Item :=
  Item.list <$> Gen.frequency [(6, Gen.list (.constant 1 6) genVersionedHash),
    (1, pure []), (1, Gen.list (.constant 7 10) genVersionedHash)]

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
  let data ← Item.bytes <$> genData
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
      | 4 => (fun auths => [Item.list auths]) <$> Gen.list (.linear 0 3) (genAuthorization chain)
      | _ => pure []
    pure (head ++ extra ++ [parity, r, s], if type = 1 then 3 else 4)

/-- The bytes of a transaction of a type with these fields. -/
def txBytes (type : Nat) (fields : Item) : ByteArray :=
  if type = 0 then enc fields else ⟨#[UInt8.ofNat type]⟩ ++ enc fields

/-- The fields with the gas limit a little off the least one of the fork, if they decode. -/
def nearMinimum (fork : Fork) (type index : Nat) (delta : Int) (fields : List Item) :
    List Item :=
  match decodeTransaction .pectra (txBytes type (.list fields)) with
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

/-- A transaction of any type, at any fork, with a gas limit near the least one half the time. -/
def genTxCase : Gen TxCase := do
  let fork ← genFork
  let chain ← genChain
  -- Mostly a type that the fork has, and now and then any type.
  let types := (List.range 5).filter fun type =>
    type = 0 ∨ (typeFork (UInt8.ofNat type)).any (· ≤ fork.1)
  let type ← Gen.frequency [(9, Gen.element types.reverse), (1, Gen.nat (.constant 0 4))]
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

/-- EthLib and execution-specs agree on the bytes of a transaction.

They agree on whether the bytes hold a transaction of the fork, and then on its hash, its sender on
the chain, its intrinsic gas, its floor, and whether the rules that read no state accept it. -/
def transactionBytes (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genTxCase
  pure do
    let expected ← oracle.ask ["tx", c.fork.2, toString c.chain, hex c.bytes]
    describeTx c.fork.1 c.chain c.bytes === expected

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

The bytes decode and encode back, and the hash, the signing hash and the sender are those of
eth-account, as is the authority of each authorization.
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
    match decodeTransaction .pectra bytes with
    | .error error => failWith s!"EthLib does not decode it: {repr error}"
    | .ok tx =>
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

end ExecutionProperty

namespace ExecutionProperty

open EthLib.Execution.State in
/-- The sender of a transaction may send it exactly when the rules of its EIPs say so.

The model is in `Nat`, from the text of EIP-1559, EIP-4844, EIP-3607 and EIP-7702.
The nonce of the sender is the nonce of the transaction.
Its balance covers the gas limit at the maximum fee, the blob gas at its maximum fee, and the
value.
It has no code, or from Pectra a delegation indicator: `0xef0100`, then 20 bytes.
The price that the sender pays is the price of EIP-1559: the base fee plus the capped priority. -/
def senderRules : Property IO := pureIO do
  let fork ← forAllWith (·.2) genFork
  let type ← forAll (Gen.nat (.constant 0 3))
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
    (3, (fun n => bytesOf ([0xef, 0x01, 0x00] ++ List.replicate n 7)) <$> Gen.element [20, 19, 21]),
    (1, pure (bytesOf ([0xef, 0x01, 0x01] ++ List.replicate 20 7))),
    (1, pure (bytesOf ([0xef, 0x00, 0x00] ++ List.replicate 20 7))),
    (1, pure ⟨#[0]⟩)])
  let baseFee ← forAll (Gen.frequency [(2, Gen.nat (.constant 0 fee)), (1, pure fee)])
  let word (n : Nat) : U256 := .ofNat 256 n
  let to : Address := Vector.replicate 20 9
  let tx : Transaction := match type with
    | 0 => .legacy ⟨word nonce, word fee, word gas, some to, word value, .empty, 27, 1, 1⟩
    | 1 => .accessList ⟨1, word nonce, word fee, word gas, some to, word value, .empty, [], 0, 1,
      1⟩
    | 2 => .feeMarket ⟨1, word nonce, word tip, word fee, word gas, some to, word value, .empty,
      [], 0, 1, 1⟩
    | _ => .blob ⟨1, word nonce, word tip, word fee, word gas, to, word value, .empty, [],
      word blobFee, List.replicate blobs (Vector.replicate 32 1), 0, 1, 1⟩
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
  (checkSender fork.1 funded sender tx).isOk === decide expected
  -- EIP-1559: `priority_fee_per_gas = min(max_priority_fee_per_gas, max_fee_per_gas - base_fee)`.
  effectiveGasPrice baseFee tx === (if type < 2 then fee else baseFee + min tip (fee - baseFee))

end ExecutionProperty

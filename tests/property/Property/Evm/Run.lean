import Hedgehog
import Support
import EthLib.Execution.Evm

/-!
# Running EthLib's EVM beside the reference

A message runs in EthLib and in the Python execution-specs from the same state.

Each side prints what the message left in the same text form.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Evm
open EthLib.Execution.State (Account TransactionState BlockState)

namespace EvmProperty

/-- The forks the reference has, each with the name of its module there.

A fork that changes only the consensus layer runs the EVM of the fork before it. -/
def forks : List (Fork × String) := [
  (.frontier, "frontier"), (.homestead, "homestead"), (.daoFork, "dao_fork"),
  (.tangerineWhistle, "tangerine_whistle"), (.spuriousDragon, "spurious_dragon"),
  (.byzantium, "byzantium"), (.constantinople, "constantinople"), (.petersburg, "constantinople"),
  (.istanbul, "istanbul"), (.muirGlacier, "muir_glacier"), (.phase0, "muir_glacier"),
  (.berlin, "berlin"), (.london, "london"), (.altair, "london"),
  (.arrowGlacier, "arrow_glacier"), (.grayGlacier, "gray_glacier"), (.bellatrix, "gray_glacier"),
  (.paris, "paris"), (.shapella, "shanghai"), (.dencun, "cancun"), (.pectra, "prague"),
  (.fusaka, "osaka"), (.bpo1, "bpo1"), (.bpo2, "bpo2")]

/-- A fork with a reference: the late ones more often, since they hold more rules. -/
def genFork : Gen (Fork × String) :=
  Gen.frequency [(1, Gen.element forks), (1, Gen.element (forks.drop 11))]

/-- An address of twenty copies of two bytes. -/
def addressOf (hi lo : UInt8) : Address := Vector.ofFn fun i => if i.val % 2 = 0 then hi else lo

/-- The caller of every run. -/
def callerAddress : Address := addressOf 0xca 0xca

/-- The account whose code runs. -/
def targetAddress : Address := addressOf 0xc0 0xde

/-- The coinbase of the block. -/
def coinbaseAddress : Address := addressOf 0xba 0x5e

/-- A 32-byte word of a number. -/
def word32 (n : Nat) : Bytes32 := U256.toBeBytes (BitVec.ofNat 256 n)

/-- The block of a run, the one of `oracle/evm.py`.

With `big`, each number of the block is near the top of its type.

An instruction that cut one to 64 bits, or to 32, would show there and not on a small block. -/
def blockEnv (fork : Fork) (big : Bool := false) : BlockEnvironment fork where
  chainId := if big then (2 ^ 64 - 1 : Nat).toUInt64 else 1
  coinbase := coinbaseAddress
  number := if big then 2 ^ 63 + 1000 else 1000
  gasLimit := if big then 2 ^ 64 - 1 else 30000000
  timestamp := if big then BitVec.ofNat 256 (2 ^ 255 + 3) else 1700000000
  difficulty := if big then 2 ^ 200 + 7 else 0x20000
  blockHashes := (List.range 256).map fun i => word32 (i + 1)
  baseFeePerGas := fun _ => if big then 2 ^ 100 + 1 else 7
  prevRandao := fun _ => Vector.replicate 32 (if big then 0xff else 0x11)
  -- An excess at which each blob schedule gives another blob gas price.
  excessBlobGas := fun _ => (60000000 : Nat).toUInt64
  parentBeaconBlockRoot := fun _ => Vector.replicate 32 0x22
  slotNumber := fun _ => 0

/-- The transaction of a run, with a gas price near the top of a word when `big`. -/
def txEnv (fork : Fork) (big : Bool := false) : TransactionEnvironment fork where
  origin := callerAddress
  gasPrice := if big then 2 ^ 255 + 10 else 10
  blobVersionedHashes := fun _ =>
    [Vector.ofFn fun i => if i.val = 0 then 0x01 else 0xb1,
     Vector.ofFn fun i => if i.val = 0 then 0x01 else 0xb2]

/-- An account of the state before a run. -/
structure PreAccount where
  address : Address
  nonce : Nat
  balance : Nat
  code : ByteArray
  storage : List (Nat × Nat)

/-- Lower-case hexadecimal of a number, with no padding. -/
def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- Hexadecimal of a vector of bytes. -/
def hexVec {n : Nat} (v : Vector UInt8 n) : String := hex ⟨v.toArray⟩

instance : Repr PreAccount where
  reprPrec a _ := s!"{hexVec a.address} nonce={a.nonce} balance={a.balance} code={hex a.code} \
    storage={a.storage}"

/-- An account in the text form of the oracle. -/
def PreAccount.show (a : PreAccount) : String :=
  let slots := a.storage.map fun (k, v) => s!"{hexVec (word32 k)}={hexNat v}"
  let storage := if slots.isEmpty then "-" else "&".intercalate slots
  s!"{hexVec a.address},{a.nonce},{a.balance},{hex a.code},{storage}"

/-- The state before a block that holds the accounts. -/
def preState (accounts : List PreAccount) : State.State :=
  accounts.foldl (init := ⟨∅, ∅, ∅⟩) fun state a =>
    let codeHash := Cryptography.Hash.Keccak.keccak256 a.code
    { accounts := state.accounts.insert a.address ⟨a.nonce, BitVec.ofNat 256 a.balance, codeHash⟩
      storage := state.storage.insert a.address
        (a.storage.foldl (init := ∅) fun m (k, v) => m.insert (word32 k) (BitVec.ofNat 256 v))
      code := state.code.insert codeHash a.code }

/-- A transaction with no write yet over the accounts. -/
def txState (accounts : List PreAccount) : TransactionState :=
  .ofBlock ⟨preState accounts, ∅, ∅, ∅, ∅⟩

/-- The substate at the start of a run: the caller and the target are warm. -/
def startSubstate : Substate :=
  { Substate.empty with
    accessedAddresses := ((∅ : Std.ExtTreeSet Address).insert callerAddress).insert targetAddress }

/-- A message from the caller to the target, or a creation at the target. -/
def messageOf (fork : Fork) (create static : Bool) (gas value : Nat) (data code : ByteArray)
    (big : Bool := false) : Message fork where
  blockEnv := blockEnv fork big
  txEnv := txEnv fork big
  caller := callerAddress
  target := if create then none else some targetAddress
  currentTarget := targetAddress
  gas := gas
  value := BitVec.ofNat 256 value
  data := data
  codeAddress := if create then none else some targetAddress
  code := code
  depth := 0
  shouldTransferValue := true
  isStatic := static
  disablePrecompiles := false

/-- The logs in the text form of the oracle. -/
def showLogs (logs : Array Blocks.Log) : String :=
  if logs.isEmpty then "-" else ";".intercalate (logs.toList.map fun log =>
    let topics := if log.topics.isEmpty then "-" else ".".intercalate (log.topics.map hexVec)
    s!"{hexVec log.address},{topics},{hex log.data}")

/-- Whether one address sorts before another, as byte strings. -/
def addressLt (a b : Address) : Bool := decide (a.toList < b.toList)

/-- The accounts that exist in a state, in the text form of the oracle.

The addresses are those of the state before and those the transaction wrote. -/
def showState (accounts : List PreAccount) (state : TransactionState) : String :=
  let addresses := (accounts.map (·.address) ++ state.accountWrites.keys).eraseDups
  let sorted := (addresses.toArray.qsort addressLt).toList
  let shown := sorted.filterMap fun address =>
    (state.getAccountOptional address).map fun account =>
      let before := (accounts.filter (·.address = address)).flatMap fun a =>
        a.storage.map fun (k, _) => word32 k
      let keys := (before ++ (state.storageWrites.getD address ∅).keys).eraseDups
      let keys := (keys.toArray.qsort fun a b => decide (a.toList < b.toList)).toList
      let slots := keys.filterMap fun key =>
        let value := state.getStorage address key
        if value = 0 then none else some s!"{hexVec key}={hexNat value.toNat}"
      let storage := if slots.isEmpty then "-" else "&".intercalate slots
      s!"{hexVec address},{account.nonce},{account.balance.toNat},{hexVec account.codeHash},\
        {storage}"
  if shown.isEmpty then "-" else ";".intercalate shown

/-- The transient storage of a state: each word that is not zero, in the order of the oracle. -/
def showTransient (state : TransactionState) : String :=
  let shown := state.transientStorage.toList.flatMap fun (address, slots) =>
    slots.toList.filterMap fun (key, value) =>
      if value = 0 then none else some s!"{hexVec address}:{hexVec key}={hexNat value.toNat}"
  if shown.isEmpty then "-" else ",".intercalate (shown.toArray.qsort (· < ·)).toList

/-- What a frame that ended a message left, in the text form of the oracle. -/
def showResult {fork : Fork} (accounts : List PreAccount) (evm : Evm fork Nat) : String :=
  let status := match evm.error with
    | none => "ok"
    | some .revert => "revert"
    | some _ => "halt"
  let deleted := (evm.substate.accountsToDelete.toList.toArray.qsort addressLt).toList
  let showAddresses (addresses : List Address) : String :=
    if addresses.isEmpty then "-" else ",".intercalate (addresses.map hexVec)
  -- The reference tracks touched accounts from Spurious Dragon until Paris forbids empty ones.
  let touched := if fork ≥ .spuriousDragon ∧ fork < .paris then
      showAddresses (evm.substate.touchedAccounts.toList.toArray.qsort addressLt).toList
    else "n/a"
  let tail := if evm.error.isNone then
      s!"{evm.substate.refundCounter} {showLogs evm.substate.logs} {showAddresses deleted} \
        {touched}"
    else "0 - - n/a"
  s!"{status} {evm.gas} {hex evm.output} {tail} {showState accounts evm.state} \
    {showTransient evm.state}"

/-- Run a message in EthLib and print what it left, with the error of its frame. -/
def runEthLib (fork : Fork) (create static : Bool) (gas value : Nat) (data code : ByteArray)
    (accounts : List PreAccount) (big : Bool := false) : String × String :=
  let message := messageOf fork create static gas value data code big
  let state := txState accounts
  let result := if create then processCreateMessage (Meter := Nat) fork message state startSubstate
    else processMessage (Meter := Nat) fork message state startSubstate
  match result with
  | .error e => (s!"abort {reprStr e}", "")
  | .ok ⟨evm, _⟩ => (showResult accounts evm, reprStr evm.error)

/-- The command that asks the oracle for the same run. -/
def runCommand (name : String) (create static : Bool) (gas value : Nat) (data code : ByteArray)
    (accounts : List PreAccount) (big : Bool := false) : List String :=
  ["run", name, if create then "create" else "call", if static then "1" else "0", toString gas,
    toString value, hex data, hex code,
    if accounts.isEmpty then "-" else ";".intercalate (accounts.map (·.show)),
    if big then "big" else "small"]

end EvmProperty

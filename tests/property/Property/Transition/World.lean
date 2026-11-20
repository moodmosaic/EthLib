import Hedgehog
import Support
import EthLib.Execution.Transactions
import EthLib.Execution.Blocks
import Property.Evm.Program

/-!
# A small world for a transaction and a block

A world is a few accounts and a block.

Some accounts are externally owned, with a balance near what a transaction costs.

The others hold short contracts written by hand, or a generated program.

A transaction is a list of fields, which the oracle signs and encodes.

So both sides run the same bytes.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Transactions EthLib.Execution.Blocks EthLib.Execution.Evm
open EvmProperty (PreAccount addressOf hexVec hexNat word32 beBytes preState assemble genProgram
  Snip addressNat)
open EvmProperty (hexNat)

namespace TransitionProperty

/-! ## The oracle -/

/-- What every property needs: the oracle, and the addresses of its eight keys.

The oracle of Glamsterdam is there when the branch of the reference is installed. -/
structure Setup where
  oracle : Oracle
  keys : Array Address
  glamsterdam : Option Oracle := none

/-- Send a command and read its answer, outside a test. -/
def askIO (oracle : Oracle) (words : List String) : IO String := do
  oracle.stdin.putStrLn ("\t".intercalate words)
  oracle.stdin.flush
  let line ← oracle.stdout.getLine
  pure (String.ofList (line.toList.filter (· ≠ '\n')))

/-- The address that some hexadecimal holds, or none. -/
def address? (text : String) : Option Address := do
  let bytes ← unhex? text
  if bytes.size = 20 then some (Vector.ofFn fun (i : Fin 20) => bytes.get! i.val) else none

/-- Start the oracle and read the addresses of its keys. -/
def Setup.start : IO Setup := do
  let oracle ← Oracle.start "transition"
  let answer ← askIO oracle ["setup"]
  let keys := (answer.splitOn ",").filterMap address?
  if keys.length ≠ 8 then throw (IO.userError s!"the oracle gave no keys: {answer}")
  let specs := (← IO.getEnv "ETHLIB_AMSTERDAM_SPECS").getD ".venv/evm-amsterdam"
  let glamsterdam ← if ← System.FilePath.pathExists s!"{specs}/ethereum/forks/amsterdam" then
      some <$> Oracle.start "transition_amsterdam"
    else pure none
  pure ⟨oracle, keys.toArray, glamsterdam⟩

/-- The address of a key. -/
def Setup.key (setup : Setup) (index : Nat) : Address := setup.keys[index]!

/-! ## The forks -/

/-- The family of a fork: the forks between two changes of the rules of a transaction. -/
def family (fork : Fork) : String :=
  if fork < .spuriousDragon then "1 Frontier to Tangerine Whistle"
  else if fork < .berlin then "2 Spurious Dragon to Muir Glacier"
  else if fork < .london then "3 Berlin"
  else if fork < .paris then "4 London to Gray Glacier"
  else if fork < .shapella then "5 Paris"
  else if fork < .dencun then "6 Shanghai"
  else if fork < .pectra then "7 Cancun"
  else if fork < .fusaka then "8 Prague"
  else if fork < .glamsterdam then "9 Osaka to BPO2"
  else "10 Glamsterdam"

/-- One fork of each family, so that each family is as common as the others. -/
def familyForks : List (Fork × String) := [
  (.homestead, "homestead"), (.byzantium, "byzantium"), (.berlin, "berlin"), (.london, "london"),
  (.paris, "paris"), (.shapella, "shanghai"), (.dencun, "cancun"), (.pectra, "prague"),
  (.fusaka, "osaka")]

/-- A fork that the reference has, among those that pass a test if any does.

Two draws in three are a fork of each family in turn, and the third is any fork. -/
def genForkWhere (wanted : Fork → Bool) : Gen (Fork × String) :=
  let among (forks : List (Fork × String)) : List (Fork × String) :=
    let fit := forks.filter fun fork => wanted fork.1
    if fit.isEmpty then forks else fit
  Gen.frequency [(2, Gen.element (among familyForks)), (1, Gen.element (among EvmProperty.forks))]

/-- A fork that the reference has. -/
def genFork : Gen (Fork × String) := genForkWhere fun _ => true

/-! ## The accounts -/

/-- The contract that stores its first two words of call data in slots 0 and 1. -/
def storeAddress : Address := addressOf 0xc1 0x01

/-- The contract that destroys itself to the address in its call data. -/
def destructAddress : Address := addressOf 0xc2 0x02

/-- The contract that calls the address in its call data with the value in its second word. -/
def callerAddress : Address := addressOf 0xc3 0x03

/-- The contract that creates a contract from its call data, with the value it got. -/
def creatorAddress : Address := addressOf 0xc4 0x04

/-- The contract that logs its call data under its first word. -/
def loggerAddress : Address := addressOf 0xc5 0x05

/-- The contract that stores a word and reverts. -/
def reverterAddress : Address := addressOf 0xc6 0x06

/-- The contract that loops until the gas is gone. -/
def looperAddress : Address := addressOf 0xc7 0x07

/-- The contract that stores the hash of the block as far back as its call data says. -/
def hashesAddress : Address := addressOf 0xc8 0x08

/-- The contract that creates the same child at each call, with CREATE2. -/
def factoryAddress : Address := addressOf 0xc9 0x09

/-- The account whose code delegates to the storing contract, as EIP-7702 writes it. -/
def delegatedAddress : Address := addressOf 0xde 0x1e

/-- Accounts whose code delegates to a precompile, to a delegated account and to itself. -/
def delegatedOddly : List Address := [addressOf 0xde 0x1f, addressOf 0xde 0x2f, addressOf 0xde 0x3f]

/-- An account that exists and is empty, which only a state before Spurious Dragon holds. -/
def emptyAddress : Address := addressOf 0xe0 0x00

/-- An externally owned account with a balance. -/
def richAddress : Address := addressOf 0xe0 0xa1

/-- An address with no account. -/
def absentAddress : Address := addressOf 0xab 0x5e

/-- The address of a precompile, or of a number. -/
def numberAddress (n : Nat) : Address := toAddressMasked (BitVec.ofNat 256 n)

/-- The deposit contract of mainnet, which EIP-6110 names. -/
def depositAddress : Address := ChainConfig.mainnet.depositContractAddress

/-- The topic of a deposit event, as EIP-6110 gives it. -/
def depositTopic : Nat := 0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5

/-- The bytes of a list. -/
def bytesOf (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-- A number as a 32-byte word of call data. -/
def wordBytes (n : Nat) : ByteArray := ⟨(word32 n).toArray⟩

/-- The code of the child of the factory.

It adds one to slot 0, and destroys itself to its caller when it is called with data. -/
def childCode : ByteArray :=
  ⟨#[0x60, 0x00, 0x54, 0x60, 0x01, 0x01, 0x60, 0x00, 0x55, 0x36, 0x15, 0x60, 0x10, 0x57, 0x33,
    0xff, 0x5b, 0x00]⟩

/-- The init code of the child, 32 bytes: it stores 7 in slot 5 and returns the code. -/
def childInit : ByteArray :=
  ⟨#[0x60, 0x07, 0x60, 0x05, 0x55, 0x71]⟩ ++ childCode ++
    ⟨#[0x60, 0x00, 0x52, 0x60, 0x12, 0x60, 0x0e, 0xf3]⟩

/-- The address of the child, the same at each creation, as EthLib counts it.

An earlier property compared `create2Address` with the reference. -/
def childAddress : Address := create2Address factoryAddress 0 childInit

/-- The child as an account of the state before, with a count of 3.

A SELFDESTRUCT before Dencun deletes it, and the factory then creates it again with no count. -/
def childAccount : PreAccount := ⟨childAddress, 1, 0, childCode, [(0, 3), (5, 7)]⟩

/-- The code of each contract written by hand.

No code uses PUSH0, so each runs at every fork. -/
def zoo : List (Address × ByteArray × List (Nat × Nat)) := [
  -- SSTORE(0, CALLDATALOAD(0)), SSTORE(1, CALLDATALOAD(32)).
  (storeAddress, bytesOf [0x60, 0x00, 0x35, 0x60, 0x00, 0x55, 0x60, 0x20, 0x35, 0x60, 0x01, 0x55,
    0x00], [(0, 1), (1, 1)]),
  -- SELFDESTRUCT(CALLDATALOAD(0)).
  (destructAddress, bytesOf [0x60, 0x00, 0x35, 0xff], [(3, 7)]),
  -- SSTORE(5, CALL(GAS, CALLDATALOAD(0), CALLDATALOAD(32), 0, 0, 0, 0)).
  (callerAddress, bytesOf [0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x20, 0x35, 0x60,
    0x00, 0x35, 0x5a, 0xf1, 0x60, 0x05, 0x55, 0x00], []),
  -- CALLDATACOPY(0, 0, CALLDATASIZE), SSTORE(0, CREATE(CALLVALUE, 0, CALLDATASIZE)).
  (creatorAddress, bytesOf [0x36, 0x60, 0x00, 0x60, 0x00, 0x37, 0x36, 0x60, 0x00, 0x34, 0xf0, 0x60,
    0x00, 0x55, 0x00], []),
  -- CALLDATACOPY(0, 0, CALLDATASIZE), LOG1(0, CALLDATASIZE, CALLDATALOAD(0)).
  (loggerAddress, bytesOf [0x36, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x35, 0x36, 0x60, 0x00,
    0xa1, 0x00], []),
  -- SSTORE(0, 1), REVERT(0, 0).
  (reverterAddress, bytesOf [0x60, 0x01, 0x60, 0x00, 0x55, 0x60, 0x00, 0x60, 0x00, 0xfd], []),
  -- JUMPDEST, JUMP(0).
  (looperAddress, bytesOf [0x5b, 0x60, 0x00, 0x56], []),
  -- SSTORE(0, BLOCKHASH(NUMBER - CALLDATALOAD(0))), SSTORE(1, 1).
  (hashesAddress, bytesOf [0x60, 0x00, 0x35, 0x43, 0x03, 0x40, 0x60, 0x00, 0x55, 0x60, 0x01, 0x60,
    0x01, 0x55, 0x00], []),
  -- MSTORE(0, the init code of the child), CREATE2(0, 0, 32, 0).
  (factoryAddress, bytesOf ([0x7f] ++ childInit.toList ++ [0x60, 0x00, 0x52, 0x60, 0x00, 0x60,
    0x20, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00]), []),
  -- CALLDATACOPY(0, 0, CALLDATASIZE), LOG1(0, CALLDATASIZE, the topic of a deposit event).
  (depositAddress, bytesOf ([0x36, 0x60, 0x00, 0x60, 0x00, 0x37, 0x7f] ++ beBytes 32 depositTopic
    ++ [0x36, 0x60, 0x00, 0xa1, 0x00]), [])]

/-- The code of the beacon roots contract of EIP-4788. -/
def beaconRootsCode : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe14604d57602036146024575f5ffd5b5f35801560495762001f\
   ff810690815414603c575f5ffd5b62001fff01545f5260205ff35b5f5ffd5b62001fff42064281555f359062001fff\
   015500"

/-- The code of the history storage contract of EIP-2935. -/
def historyCode : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe14604657602036036042575f35600143038111604257611fff\
   81430311604257611fff9006545f5260205ff35b5f5ffd5b5f35611fff60014303065500"

/-- The code of the withdrawal request contract of EIP-7002. -/
def withdrawalRequestCode : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1460cb5760115f54807fffffffffffffffffffffffffffffff\
   ffffffffffffffffffffffffffffffffff146101f457600182026001905f5b5f821115606857810190830284830290\
   04916001019190604d565b909390049250505036603814608857366101f457346101f4575f5260205ff35b34106101\
   f457600154600101600155600354806003026004013381556001015f35815560010160203590553360601b5f526038\
   5f601437604c5fa0600101600355005b6003546002548082038060101160df575060105b5f5b818114610183578281\
   0160030260040181604c02815460601b8152601401816001015481526020019060020154807fffffffffffffffffff\
   ffffffffffffff00000000000000000000000000000000168252906010019060401c908160381c8160070153816030\
   1c81600601538160281c81600501538160201c81600401538160181c81600301538160101c81600201538160081c81\
   600101535360010160e1565b910180921461019557906002556101a0565b90505f6002555f6003555b5f54807fffff\
   ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff14156101cd57505f5b6001546002828201\
   116101e25750505f6101e8565b01600290035b5f555f600155604c025ff35b5f5ffd"

/-- The code of the consolidation request contract of EIP-7251. -/
def consolidationRequestCode : String :=
  "3373fffffffffffffffffffffffffffffffffffffffe1460d35760115f54807fffffffffffffffffffffffffffffff\
   ffffffffffffffffffffffffffffffffff1461019a57600182026001905f5b5f821115606857810190830284830290\
   04916001019190604d565b9093900492505050366060146088573661019a573461019a575f5260205ff35b34106101\
   9a57600154600101600155600354806004026004013381556001015f35815560010160203581556001016040359055\
   3360601b5f5260605f60143760745fa0600101600355005b6003546002548082038060021160e7575060025b5f5b81\
   81146101295782810160040260040181607402815460601b8152601401816001015481526020018160020154815260\
   20019060030154905260010160e9565b910180921461013b5790600255610146565b90505f6002555f6003555b5f54\
   807fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff141561017357505f5b60015460\
   01828201116101885750505f61018e565b01600190035b5f555f6001556074025ff35b5f5ffd"

/-- The code that some hexadecimal holds. -/
def codeOf (text : String) : ByteArray := (unhex? text).getD .empty

/-- The system contracts that a fork calls, with their code as their EIPs give it.

With `broken`, the withdrawal request contract has no code, so a block from Pectra is invalid. -/
def systemAccounts (fork : Fork) (broken : Bool := false) : List PreAccount :=
  (if fork ≥ .dencun then [⟨BEACON_ROOTS_ADDRESS, 1, 0, codeOf beaconRootsCode, []⟩] else []) ++
  (if fork ≥ .pectra then
    [⟨HISTORY_STORAGE_ADDRESS, 1, 0, codeOf historyCode, []⟩,
     ⟨WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS, 1, 0,
       if broken then .empty else codeOf withdrawalRequestCode, []⟩,
     ⟨CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS, 1, 0, codeOf consolidationRequestCode, []⟩]
   else []) ++
  -- No EIP gives the code of the builder contracts yet: one returns five bytes, one nothing.
  (if fork ≥ .glamsterdam then
    [⟨BUILDER_DEPOSIT_CONTRACT_ADDRESS, 1, 0, bytesOf [0x64, 0x01, 0x02, 0x03, 0x04, 0x05, 0x60,
       0x00, 0x52, 0x60, 0x05, 0x60, 0x1b, 0xf3], []⟩,
     ⟨BUILDER_EXIT_CONTRACT_ADDRESS, 1, 0, bytesOf [0x00], []⟩]
   else [])

/-- The accounts that every world holds: the contracts, a rich account and an empty one. -/
def fixedAccounts (fork : Fork) (broken : Bool := false) : List PreAccount :=
  zoo.map (fun (address, code, storage) => ⟨address, 1, 100, code, storage⟩) ++
  [⟨delegatedAddress, 1, 50, delegationIndicator storeAddress, [(0, 2)]⟩,
   ⟨addressOf 0xde 0x1f, 1, 0, delegationIndicator (numberAddress 2), []⟩,
   ⟨addressOf 0xde 0x2f, 1, 0, delegationIndicator delegatedAddress, []⟩,
   ⟨addressOf 0xde 0x3f, 1, 0, delegationIndicator (addressOf 0xde 0x3f), []⟩,
   ⟨richAddress, 3, 10 ^ 18, .empty, []⟩] ++ systemAccounts fork broken

/-- The accounts in the text form of the oracle. -/
def showAccounts (accounts : List PreAccount) : String :=
  if accounts.isEmpty then "-" else ";".intercalate (accounts.map (·.show))

/-- The accounts with the later of two accounts at one address dropped. -/
def distinctAccounts (accounts : List PreAccount) : List PreAccount :=
  accounts.foldl (init := []) fun kept a =>
    if kept.any (·.address = a.address) then kept else kept ++ [a]

/-! ## A transaction as its fields -/

/-- An authorization of EIP-7702 as its fields, which the oracle signs with a key. -/
structure AuthSpec where
  chain : Nat
  address : Address
  nonce : Nat
  key : Nat
  /-- 0 for a good signature, 1 for a high `s`, 2 for an `r` of 0. -/
  fault : Nat

/-- A transaction as its fields, which the oracle signs with a key. -/
structure TxSpec where
  type : Nat
  key : Nat
  /-- The chain that the transaction names, or 0 for a legacy transaction that names none. -/
  chain : Nat
  nonce : Nat
  gasPrice : Nat
  priorityFee : Nat
  maxFee : Nat
  gas : Nat
  to : Option Address
  value : Nat
  data : ByteArray
  access : List (Address × List Nat)
  blobFee : Nat
  blobs : List Nat
  auths : List AuthSpec
  /-- 0 for a good signature, 1 for a high `s`, 2 for an `r` of 0. -/
  fault : Nat

/-- A list in the text form of the oracle: the items joined, or `-` for none. -/
def joined (separator : String) (items : List String) : String :=
  if items.isEmpty then "-" else separator.intercalate items

/-- A transaction in the text form of the oracle. -/
def TxSpec.show (t : TxSpec) : String :=
  let access := t.access.map fun (address, keys) =>
    s!"{hexVec address}:{".".intercalate (keys.map fun k => hexVec (word32 k))}"
  let auths := t.auths.map fun a => s!"{a.chain}:{hexVec a.address}:{a.nonce}:{a.key}:{a.fault}"
  ",".intercalate [toString t.type, toString t.key, toString t.chain, toString t.nonce,
    toString t.gasPrice, toString t.priorityFee, toString t.maxFee, toString t.gas,
    (t.to.map hexVec).getD "-", toString t.value, hex t.data, joined "/" access,
    toString t.blobFee, joined "." (t.blobs.map fun b => hexVec (word32 b)), joined "/" auths,
    toString t.fault]

/-- The transaction of EthLib with the fields, and no signature.

It gives the intrinsic gas, which reads no signature. -/
def TxSpec.unsigned (t : TxSpec) : Transaction :=
  let u (n : Nat) : U256 := BitVec.ofNat 256 n
  let accessList : List Access := t.access.map fun (address, keys) => ⟨address, keys.map word32⟩
  let to := t.to.getD (Vector.replicate 20 0)
  match t.type with
  | 0 => .legacy {
      nonce := u t.nonce, gasPrice := u t.gasPrice, gas := u t.gas, to := t.to,
      value := u t.value, data := t.data, v := 0, r := 0, s := 0 }
  | 1 => .accessList {
      chainId := 1, nonce := u t.nonce, gasPrice := u t.gasPrice, gas := u t.gas, to := t.to,
      value := u t.value, data := t.data, accessList, yParity := 0, r := 0, s := 0 }
  | 2 => .feeMarket {
      chainId := 1, nonce := u t.nonce, maxPriorityFeePerGas := u t.priorityFee,
      maxFeePerGas := u t.maxFee, gas := u t.gas, to := t.to, value := u t.value, data := t.data,
      accessList, yParity := 0, r := 0, s := 0 }
  | 3 => .blob {
      chainId := 1, nonce := u t.nonce, maxPriorityFeePerGas := u t.priorityFee,
      maxFeePerGas := u t.maxFee, gas := u t.gas, to, value := u t.value, data := t.data,
      accessList, maxFeePerBlobGas := u t.blobFee, blobVersionedHashes := t.blobs.map word32,
      yParity := 0, r := 0, s := 0 }
  | _ => .setCode {
      chainId := 1, nonce := u t.nonce, maxPriorityFeePerGas := u t.priorityFee,
      maxFeePerGas := u t.maxFee, gas := u t.gas, to, value := u t.value, data := t.data,
      accessList, yParity := 0, r := 0, s := 0,
      authorizations := t.auths.map fun a => ⟨u a.chain, a.address, a.nonce.toUInt64, 0, 0, 0⟩ }

/-- The least gas limit of a transaction at a fork, as EthLib counts it.

Earlier properties compared it with the reference, and a generator places the gas limit by it. -/
def TxSpec.minimumGas (t : TxSpec) (fork : Fork) (sender : Address := Vector.replicate 20 0) :
    Nat :=
  Transactions.minimumGas fork sender t.unsigned

/-- The price per gas that a transaction offers at most. -/
def TxSpec.price (t : TxSpec) : Nat := if t.type < 2 then t.gasPrice else t.maxFee

/-- The most that a transaction can cost its sender. -/
def TxSpec.cost (t : TxSpec) : Nat :=
  t.gas * t.price + t.value + (if t.type = 3 then 2 ^ 17 * t.blobs.length * t.blobFee else 0)

/-! ## A block as its fields -/

/-- A blob schedule as its three numbers: the target, the maximum and the update fraction. -/
abbrev Schedule := Nat × Nat × Nat

/-- The blob schedule of a fork of the reference.

EIP-4844 gives the one of Cancun, EIP-7691 the one of Prague, and EIP-7892 those of BPO1 and BPO2.

They are written here apart from the table of EthLib. -/
def referenceSchedule (name : String) : Schedule :=
  match name with
  | "cancun" => (3, 6, 3338477)
  | "prague" | "osaka" => (6, 9, 5007716)
  | "bpo1" => (10, 15, 8346193)
  | _ => (14, 21, 11684671)

/-- The blob schedule of EthLib with three numbers, or the one of a fork for numbers it refuses. -/
def scheduleAt (fork : Fork) (h : .dencun ≤ fork) : Option Schedule → BlobSchedule
  | some (target, most, fraction) =>
    if ok : target ≤ most ∧ 0 < most ∧ 0 < fraction then
      ⟨target, most, fraction, ok.1, ok.2.1, ok.2.2⟩
    else Fees.BlobBaseFee.blobSchedule fork h
  | none => Fees.BlobBaseFee.blobSchedule fork h

/-- The block of one transaction, in the fields of the oracle. -/
structure EnvSpec where
  number : Nat
  time : Nat
  gasLimit : Nat
  baseFee : Nat
  coinbase : Address
  difficulty : Nat
  randao : UInt8
  excessBlobGas : Nat
  /-- The gas that the transactions before this one used. -/
  gasUsed : Nat
  /-- The blob gas that the transactions before this one used. -/
  blobGasUsed : Nat
  /-- The blob schedule that the chain sets itself, or none for the schedule of the fork. -/
  schedule : Option Schedule := none

/-- The environment in the text form of the oracle. -/
def EnvSpec.show (e : EnvSpec) : String :=
  let word (b : UInt8) : String := hexVec (Vector.replicate 32 b)
  ",".intercalate [toString e.number, toString e.time, toString e.gasLimit, toString e.baseFee,
    hexVec e.coinbase, toString e.difficulty, word e.randao, toString e.excessBlobGas, word 0x22,
    toString e.gasUsed, toString e.blobGasUsed]

/-- The block environment of EthLib with the fields. -/
def EnvSpec.toEnv (e : EnvSpec) (fork : Fork) : BlockEnvironment fork where
  chainId := 1
  coinbase := e.coinbase
  number := e.number
  gasLimit := e.gasLimit
  timestamp := BitVec.ofNat 256 e.time
  difficulty := e.difficulty
  blockHashes := (List.range 256).map fun i => word32 (i + 1)
  baseFeePerGas := fun _ => e.baseFee
  prevRandao := fun _ => Vector.replicate 32 e.randao
  excessBlobGas := fun _ => e.excessBlobGas.toUInt64
  parentBeaconBlockRoot := fun _ => Vector.replicate 32 0x22
  slotNumber := fun _ => 0
  blobSchedule := fun h => scheduleAt fork h e.schedule

/-- The base fee per blob gas at an excess blob gas, or 1 before Dencun, as EthLib counts it.

The schedule is the chain's own, or the one of the fork. -/
def blobPrice (fork : Fork) (excess : Nat) (schedule : Option Schedule := none) : Nat :=
  if h : .dencun ≤ fork then
    Fees.BlobBaseFee.getBaseFeePerBlobGas (scheduleAt fork h schedule) excess
  else 1

/-- The most blobs of a block at a fork, or 6 before Dencun. -/
def maxBlobs (fork : Fork) (schedule : Option Schedule := none) : Nat :=
  if h : .dencun ≤ fork then (scheduleAt fork h schedule).max else 6

/-- A fork of EthLib beside a fork of the reference, with the blob schedule that joins them.

From Fusaka, the forks differ only in their blob schedule.

So any of them, on a chain that sets the schedule of a fork of the reference, is that fork.

Half of the draws from Fusaka cross two forks this way, and the others keep the fork's own table.
-/
def genCrossed (fork : Fork × String) : Gen ((Fork × String) × Option Schedule) :=
  if fork.1 ≥ .fusaka then
    Gen.frequency [(1, pure (fork, none)),
      (1, Gen.zipWith (fun (f : Fork) name => ((f, name), some (referenceSchedule name)))
        (Gen.element [.fusaka, .bpo1, .bpo2, .bpo3, .bpo4, .bpo5])
        (Gen.element ["osaka", "bpo1", "bpo2"]))]
  else pure (fork, none)

/-! ## What a state and a run look like -/

/-- Whether one vector of bytes sorts before another. -/
def bytesLt {n : Nat} (a b : Vector UInt8 n) : Bool := decide (a.toList < b.toList)

/-- The accounts of a state, in the text form of the oracle. -/
def showState (state : State.State) : String :=
  let accounts := (state.accounts.toList.toArray.qsort fun a b => bytesLt a.1 b.1).toList
  joined ";" (accounts.map fun (address, account) =>
    let slots := ((state.storage.getD address ∅).toList.toArray.qsort
      fun a b => bytesLt a.1 b.1).toList
    let storage := slots.filterMap fun (key, value) =>
      if value = 0 then none else some s!"{hexVec key}={EvmProperty.hexNat value.toNat}"
    s!"{hexVec address},{account.nonce},{account.balance.toNat},{hexVec account.codeHash},\
      {joined "&" storage}")

/-- Why EthLib refuses a transaction, as a short word that the reference's errors map to. -/
def reasonOfTransaction : TransactionError → String
  | .emptyTransaction | .unsupportedType _ | .decoding _ | .encoding _ => "decode"
  | .invalidSignature | .wrongChainId .. => "signature"
  | .insufficientGas .. => "intrinsic gas"
  | .initCodeTooLarge _ => "init code size"
  | .gasLimitExceeded _ => "gas cap"
  | .nonceOverflow _ => "nonce overflow"
  | .priorityFeeGreaterThanMaxFee .. => "fee order"
  | .noBlobData => "no blob"
  | .blobCountExceeded _ => "blob count"
  | .invalidBlobVersionedHash .. => "blob version"
  | .emptyAuthorizationList => "no authorization"
  | .intrinsicGasAboveLimit _ => "intrinsic gas cap"

/-- Why EthLib refuses a transaction in a block, as a short word. -/
def reasonOf : InclusionError → String
  | .transaction e => reasonOfTransaction e
  | .gasAllowanceExceeded .. => "block gas"
  | .blobGasLimitExceeded .. => "block blob gas"
  | .insufficientMaxFeePerGas .. => "base fee"
  | .insufficientMaxFeePerBlobGas .. => "blob fee"
  | .nonceTooLow .. | .nonceTooHigh .. => "nonce"
  | .insufficientBalance .. => "balance"
  | .senderNotEoa _ => "sender"
  | .missingCode _ => "missing code"

/-- Why the reference refuses a transaction, from the name of its error. -/
def reasonOfReference (name : String) : String :=
  match name with
  | "GasUsedExceedsLimitError" => "block gas"
  | "BlobGasLimitExceededError" => "block blob gas"
  | "BlobCountExceededError" => "blob count"
  | "InvalidSignatureError" | "chain" => "signature"
  | "PriorityFeeGreaterThanMaxFeeError" => "fee order"
  | "InsufficientMaxFeePerGasError" | "InvalidBlock" => "base fee"
  | "NoBlobDataError" => "no blob"
  | "InvalidBlobVersionedHashError" => "blob version"
  | "InsufficientMaxFeePerBlobGasError" => "blob fee"
  | "EmptyAuthorizationListError" => "no authorization"
  | "NonceMismatchError" => "nonce"
  | "InsufficientBalanceError" => "balance"
  | "InvalidSenderError" => "sender"
  | "InsufficientTransactionGasError" => "intrinsic gas"
  | "NonceOverflowError" => "nonce overflow"
  | "InitCodeTooLargeError" => "init code size"
  | "TransactionGasLimitExceededError" => "gas cap"
  | _ => "decode"

/-- What a transaction left, in the fields that the oracle answers. -/
structure TxResult where
  /-- `valid`, `invalid` or `abort`. -/
  verdict : String
  /-- Why it is invalid, or how its message ended: ok, revert, oog or halt. -/
  detail : String
  gasUsed : String
  blobGasUsed : String
  receipt : String
  state : String

/-- The fields of a result, with the name of each. -/
def TxResult.fields (r : TxResult) : List (String × String) :=
  [("verdict", r.verdict), ("gas used", r.gasUsed), ("blob gas used", r.blobGasUsed),
    ("receipt", r.receipt), ("state", r.state)]

/-- How a message ended, as a short word. -/
def outcomeOf : Option EvmError → String
  | none => "ok"
  | some .revert => "revert"
  | some .outOfGas => "oog"
  | some _ => "halt"

/-- The body of a block before its first transaction, on a state, after some gas was used. -/
def bodyStart (fork : Fork) (state : State.State) (used : BlockGas) : BodyOutput fork :=
  ⟨.init ⟨state, ∅, ∅, ∅, ∅⟩, used, used.execution, [], [], []⟩

/-- Run a transaction as bytes in EthLib after the body so far, and say what it left.

It also gives the body after the transaction, which is the body before it for a refused one. -/
def runTransaction {fork : Fork} (env : BlockEnvironment fork) (index : Nat)
    (before : BodyOutput fork) (raw : ByteArray) : TxResult × BodyOutput fork :=
  let state := showState before.block.applyChanges
  match decodeTransaction fork raw with
  | .error e => (⟨"invalid", reasonOfTransaction e, "-", "-", "-", state⟩, before)
  | .ok tx =>
    match applyTransaction env index before tx with
    | .error (.invalidTransaction _ e) => (⟨"invalid", reasonOf e, "-", "-", "-", state⟩, before)
    | .error e => (⟨"abort", reprStr e, "-", "-", "-", state⟩, before)
    | .ok after =>
      let receipt := match after.receipts.getLast? with
        | some (type, receipt) =>
          match encodeReceipt type receipt with
          | .ok bytes => hex bytes
          | .error e => reprStr e
        | none => "none"
      let error := (after.results.getLast?.map (·.error)).getD none
      -- From Glamsterdam a block counts two kinds of gas, and the oracle answers both.
      let gas := if fork ≥ .glamsterdam then s!"{after.gas.execution}/{after.gas.state}"
        else toString after.gas.execution
      (⟨"valid", outcomeOf error, gas, toString after.gas.blob, receipt,
        showState after.block.applyChanges⟩, after)

/-- The fields of two results agree, and the report names the first that does not.

Two states that differ are shown account by account. -/
def sameResult (got : TxResult) (want : List String) : TestT IO Unit := do
  let names := got.fields
  let want := (want.head!.splitOn " ").head! :: want.drop 2
  if names.length ≠ want.length then failWith s!"the oracle answered {want.length} fields"
  for ((name, mine), theirs) in names.zip want do
    if mine ≠ theirs then
      if name = "state" then
        let (a, b) := (mine.splitOn ";", theirs.splitOn ";")
        failWith s!"the state differs.\n  EthLib only:    {a.filter (!b.contains ·)}\n  \
          reference only: {b.filter (!a.contains ·)}"
      else failWith s!"{name} differs.\n  EthLib:    {mine}\n  reference: {theirs}"

end TransitionProperty

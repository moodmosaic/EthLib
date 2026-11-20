import Hedgehog
import Support
import EthLib.Execution.Rpc

/-!
# What the properties of the RPC layer share

A node is a chain view: some blocks, each with the state after it, its receipts and its logs.

A view here is built from plain fields, so that the oracle can build the same one from the text.

Its headers and receipts are data, and nothing checks that a block follows its parent.

The methods under test read a view and never run its blocks, so that is enough for them.

The helpers of the EVM driver are copied here, since that driver is being rewritten.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Blocks EthLib.Execution.Transactions EthLib.Execution.Rpc
open EthLib.Serialization.JsonRpc (RpcError)

namespace RpcProperty

/-! ## Text -/

/-- Lower-case hexadecimal of a number, with no padding. -/
def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- Hexadecimal of a vector of bytes. -/
def hexVec {n : Nat} (v : Vector UInt8 n) : String := hex ⟨v.toArray⟩

/-- A 32-byte word of a number. -/
def word32 (n : Nat) : Bytes32 := U256.toBeBytes (BitVec.ofNat 256 n)

/-- An address of twenty copies of two bytes. -/
def addressOf (hi lo : UInt8) : Address := Vector.ofFn fun i => if i.val % 2 = 0 then hi else lo

/-- A list in the text form of the oracle: the items joined, or `-` for none. -/
def joined (separator : String) (items : List String) : String :=
  if items.isEmpty then "-" else separator.intercalate items

/-- The bytes of a list. -/
def bytesOf (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-- The vector of `n` bytes that some hexadecimal holds, or none. -/
def vector? (n : Nat) (text : String) : Option (Vector UInt8 n) := do
  let bytes ← unhex? text
  if bytes.size = n then some (Vector.ofFn fun (i : Fin n) => bytes.get! i.val) else none

/-- Send a command and read its answer, outside a test. -/
def askIO (oracle : Oracle) (words : List String) : IO String := do
  oracle.stdin.putStrLn ("\t".intercalate words)
  oracle.stdin.flush
  let line ← oracle.stdout.getLine
  pure (String.ofList (line.toList.filter (· ≠ '\n')))

/-- A value, or a failed test with the error. -/
def orFail {α : Type} (result : Except String α) : TestT IO α :=
  match result with
  | .ok value => pure value
  | .error e => failWith e

/-- The code and the message of an error, which is all that the source fixes of one. -/
def showError (e : RpcError) : String := s!"error {e.code}"

/-! ## The forks -/

/-- The forks the reference has, each with the name of its module there.

A fork that changes only the consensus layer runs the rules of the fork before it. -/
def forks : List (Fork × String) := [
  (.frontier, "frontier"), (.homestead, "homestead"),
  (.tangerineWhistle, "tangerine_whistle"), (.spuriousDragon, "spurious_dragon"),
  (.byzantium, "byzantium"), (.constantinople, "constantinople"), (.petersburg, "constantinople"),
  (.istanbul, "istanbul"), (.muirGlacier, "muir_glacier"), (.phase0, "muir_glacier"),
  (.berlin, "berlin"), (.london, "london"), (.altair, "london"),
  (.arrowGlacier, "arrow_glacier"), (.grayGlacier, "gray_glacier"), (.bellatrix, "gray_glacier"),
  (.paris, "paris"), (.shapella, "shanghai"), (.dencun, "cancun"), (.pectra, "prague"),
  (.fusaka, "osaka"), (.bpo1, "bpo1"), (.bpo2, "bpo2")]

/-- The name of a fork in the reference. -/
def referenceName (fork : Fork) : String :=
  ((forks.find? (·.1 = fork)).map (·.2)).getD "osaka"

/-! ## Accounts -/

/-- An account of the state after a block. -/
structure PreAccount where
  address : Address
  nonce : Nat
  balance : Nat
  code : ByteArray
  storage : List (Nat × Nat)

/-- An account in the text form of the oracle. -/
def PreAccount.show (a : PreAccount) : String :=
  let slots := a.storage.map fun (k, v) => s!"{hexVec (word32 k)}={hexNat v}"
  s!"{hexVec a.address},{a.nonce},{a.balance},{hex a.code},{joined "&" slots}"

instance : Repr PreAccount where
  reprPrec a _ := a.show

/-- The state that holds the accounts. -/
def preState (accounts : List PreAccount) : State.State :=
  accounts.foldl (init := ⟨∅, ∅, ∅⟩) fun state a =>
    let codeHash := Cryptography.Hash.Keccak.keccak256 a.code
    { accounts := state.accounts.insert a.address ⟨a.nonce, BitVec.ofNat 256 a.balance, codeHash⟩
      storage := state.storage.insert a.address
        (a.storage.foldl (init := ∅) fun m (k, v) => m.insert (word32 k) (BitVec.ofNat 256 v))
      code := state.code.insert codeHash a.code }

/-- The accounts with the later of two accounts at one address dropped. -/
def distinctAccounts (accounts : List PreAccount) : List PreAccount :=
  accounts.foldl (init := []) fun kept a =>
    if kept.any (·.address = a.address) then kept else kept ++ [a]

/-! ## A view from plain fields -/

/-- A header as the fields that a method of the node can read.

Every other field is zero, or the empty value of its type. -/
structure HeaderSpec where
  number : Nat
  time : Nat
  gasLimit : Nat
  gasUsed : Nat
  baseFee : Nat
  excessBlobGas : Nat
  blobGasUsed : Nat
  coinbase : Address := addressOf 0xba 0x5e
  difficulty : Nat := 0
  randao : UInt8 := 0x11
  parentHash : Hash32 := Vector.replicate 32 0
  deriving Repr

/-- The header of EthLib with the fields, at a fork. -/
def HeaderSpec.toHeader (s : HeaderSpec) (fork : Fork) : Header fork where
  parentHash := s.parentHash
  ommersHash := Blocks.EMPTY_OMMER_HASH
  coinbase := s.coinbase
  stateRoot := Vector.replicate 32 0
  transactionsRoot := Vector.replicate 32 0
  receiptRoot := Vector.replicate 32 0
  bloom := Vector.replicate 256 0
  difficulty := s.difficulty
  number := s.number
  gasLimit := s.gasLimit
  gasUsed := s.gasUsed
  timestamp := BitVec.ofNat 256 s.time
  extraData := .empty
  prevRandao := Vector.replicate 32 s.randao
  nonce := Vector.replicate 8 0
  baseFeePerGas := fun _ => s.baseFee
  withdrawalsRoot := fun _ => Vector.replicate 32 0
  blobGasUsed := fun _ => s.blobGasUsed.toUInt64
  excessBlobGas := fun _ => s.excessBlobGas.toUInt64
  parentBeaconBlockRoot := fun _ => Vector.replicate 32 0x22
  requestsHash := fun _ => Vector.replicate 32 0
  blockAccessListHash := fun _ => Vector.replicate 32 0
  slotNumber := fun _ => 0

/-- The header in the text form of the oracle. -/
def HeaderSpec.show (s : HeaderSpec) : String :=
  ",".intercalate [toString s.number, toString s.time, toString s.gasLimit, toString s.gasUsed,
    toString s.baseFee, toString s.excessBlobGas, toString s.blobGasUsed, hexVec s.coinbase,
    toString s.difficulty, hexVec (Vector.replicate 32 s.randao : Bytes32),
    hexVec s.parentHash]

/-- A trusted setup of points at infinity, which no property here reads. -/
def noSetup : Cryptography.Kzg.TrustedSetup :=
  ⟨Vector.replicate _ default, Vector.replicate _ default, Vector.replicate _ default⟩

/-- A record of a block from its parts, with the hash of its header. -/
def recordOf (fork : Fork) (header : Header fork) (state : State.State)
    (transactions : List Transaction) (receipts : List (UInt8 × Receipt fork)) :
    Except String BlockRecord := do
  let hash ← header.hash.mapError fun e => s!"a header has no hash: {reprStr e}"
  pure { fork, block := ⟨header, transactions, [], fun _ => []⟩, hash, state, receipts
         logs := receipts.flatMap (·.2.logs) }

/-- A view of some canonical blocks, or none for no block. -/
def viewOf (config : ChainConfig) (canonical : List BlockRecord)
    (pending : Option BlockRecord := none) (safe finalized : Option Hash32 := none)
    (side : List BlockRecord := []) : Option ChainView :=
  if nonempty : canonical ≠ [] then
    some { config, canonical, nonempty, side, safe, finalized, pending, networkId := 1
           setup := noSetup }
  else none

end RpcProperty

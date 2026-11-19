import Property.Execution.Common

/-!
# The tracker of writes, as a state machine

The tracker keeps the writes of a block and of a transaction apart from the state, with snapshots
for the calls that fail.
Two references run beside it on random sequences of operations.

- A model here, written from the text of `state.py` of execution-specs: one flat state, copied
  whole at each snapshot.
- `state.py` itself, in the oracle, with its own tries and its own snapshots.

After every operation the three agree on what a transaction can read of each account and slot.
-/

open Hedgehog Support EthLib EthLib.Base
open EthLib.Execution.State
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace ExecutionProperty

/-- The addresses of the tests. -/
def addresses : List Address := [0, 1, 2, 0xff].map fun (b : UInt8) => Vector.replicate 20 b

/-- The storage keys of the tests. -/
def slots : List Bytes32 := [0, 1, 2].map fun (b : UInt8) => Vector.replicate 32 b

/-- The codes of the tests: none, and two that are not empty. -/
def codes : List ByteArray := [.empty, ⟨#[0]⟩, ⟨#[0x60, 0x00]⟩]

/-- The address of an index. -/
def addressAt (i : Nat) : Address := addresses.getD i (Vector.replicate 20 0)

/-- The storage key of an index. -/
def slotAt (i : Nat) : Bytes32 := slots.getD i (Vector.replicate 32 0)

/-- An operation on the tracker; accounts, keys and codes are indices into the lists above. -/
inductive Op where
  | setBalance (account amount : Nat)
  | incrementNonce (account : Nat)
  | setCode (account code : Nat)
  | moveEther (sender recipient amount : Nat)
  | createEther (account amount : Nat)
  | setStorage (account key value : Nat)
  | destroyStorage (account : Nat)
  | destroyAccount (account : Nat)
  | markCreated (account : Nat)
  | setTransient (account key value : Nat)
  | touch (account : Nat)
  | destroyTouched (accounts : List Nat)
  | snapshot
  | rollback
  | commit
  | endTransaction
  deriving Repr, BEq

/-- The operation as a line of the oracle. -/
def Op.words : Op → List String
  | .setBalance a n => ["balance", toString a, toString n]
  | .incrementNonce a => ["nonce", toString a]
  | .setCode a c => ["code", toString a, toString c]
  | .moveEther a b n => ["move", toString a, toString b, toString n]
  | .createEther a n => ["create", toString a, toString n]
  | .setStorage a k v => ["storage", toString a, toString k, toString v]
  | .destroyStorage a => ["destroystorage", toString a]
  | .destroyAccount a => ["destroy", toString a]
  | .markCreated a => ["created", toString a]
  | .setTransient a k v => ["transient", toString a, toString k, toString v]
  | .touch a => ["touch", toString a]
  | .destroyTouched as => "destroytouched" :: as.map toString
  | .snapshot => ["snapshot"]
  | .rollback => ["rollback"]
  | .commit => ["commit"]
  | .endTransaction => ["end"]

/-! ## The model -/

/-- An account of the model: its nonce, its balance and the index of its code. -/
structure Acct where
  nonce : Nat
  balance : Nat
  code : Nat
  deriving Repr, BEq

/-- The state of the model: what `state.py` keeps in its tries, as lists. -/
structure Flat where
  accounts : List (Nat × Acct) := []
  storage : List ((Nat × Nat) × Nat) := []
  transient : List ((Nat × Nat) × Nat) := []
  deriving Repr, BEq

namespace Flat

/-- `get_account_optional`. -/
def account (f : Flat) (a : Nat) : Option Acct := f.accounts.lookup a

/-- `get_storage`: zero for a key that is not set. -/
def slot (f : Flat) (a k : Nat) : Nat := (f.storage.lookup (a, k)).getD 0

/-- `set_account`. -/
def setAccount (f : Flat) (a : Nat) (acct : Option Acct) : Flat :=
  let rest := f.accounts.filter (·.1 != a)
  { f with accounts := match acct with
      | some acct => (a, acct) :: rest
      | none => rest }

/-- `destroy_storage`. -/
def destroyStorage (f : Flat) (a : Nat) : Flat :=
  { f with storage := f.storage.filter (·.1.1 != a) }

/-- `destroy_account`: the storage, then the account. -/
def destroyAccount (f : Flat) (a : Nat) : Flat := (f.destroyStorage a).setAccount a none

/-- `set_storage`, where the word zero removes the key. -/
def setSlot (f : Flat) (a k v : Nat) : Flat :=
  let rest := f.storage.filter (·.1 != (a, k))
  { f with storage := if v = 0 then rest else ((a, k), v) :: rest }

/-- `set_transient_storage`, where the word zero removes the key. -/
def setTransient (f : Flat) (a k v : Nat) : Flat :=
  let rest := f.transient.filter (·.1 != (a, k))
  { f with transient := if v = 0 then rest else ((a, k), v) :: rest }

/-- `account_exists_and_is_empty`. -/
def emptyAt (f : Flat) (a : Nat) : Bool := f.account a == some ⟨0, 0, 0⟩

/-- `modify_state`: from Paris, a change that leaves the account empty destroys it. -/
def modify (paris : Bool) (f : Flat) (a : Nat) (change : Acct → Acct) : Flat :=
  let f := f.setAccount a (some (change ((f.account a).getD ⟨0, 0, 0⟩)))
  if paris && f.emptyAt a then f.destroyAccount a else f

end Flat

/-- The model of the tracker. -/
structure TrackerModel where
  /-- The fork, which says when an empty account is destroyed. -/
  fork : Fork
  /-- The state now. -/
  now : Flat := {}
  /-- The accounts that the transaction created. -/
  created : List Nat := []
  /-- The state at each open snapshot, the last one first. -/
  stack : List Flat := []
  /-- The state when the transaction began. -/
  start : Flat := {}

instance : Repr TrackerModel where
  reprPrec m _ := s!"{m.fork.name}"

/-- The model after an operation. -/
def TrackerModel.step (m : TrackerModel) : Op → TrackerModel
  | .setBalance a n => { m with now := m.now.modify paris a fun x => { x with balance := n } }
  | .incrementNonce a =>
    { m with now := m.now.modify paris a fun x => { x with nonce := x.nonce + 1 } }
  | .setCode a c => { m with now := m.now.modify paris a fun x => { x with code := c } }
  | .moveEther a b n =>
    if ((m.now.account a).getD ⟨0, 0, 0⟩).balance < n then m else
    let now := m.now.modify paris a fun x => { x with balance := x.balance - n }
    { m with now := now.modify paris b fun x => { x with balance := x.balance + n } }
  | .createEther a n =>
    { m with now := m.now.modify paris a fun x => { x with balance := x.balance + n } }
  | .setStorage a k v =>
    if (m.now.account a).isNone then m else { m with now := m.now.setSlot a k v }
  | .destroyStorage a => { m with now := m.now.destroyStorage a }
  | .destroyAccount a => { m with now := m.now.destroyAccount a }
  | .markCreated a => { m with created := a :: m.created }
  | .setTransient a k v => { m with now := m.now.setTransient a k v }
  | .touch a =>
    if (m.now.account a).isSome then m
    else { m with now := m.now.setAccount a (some ⟨0, 0, 0⟩) }
  | .destroyTouched as =>
    if m.fork < .spuriousDragon then m else
    { m with now := as.foldl (fun f a => if f.emptyAt a then f.destroyAccount a else f) m.now }
  | .snapshot => { m with stack := m.now :: m.stack }
  | .rollback =>
    match m.stack with
    | saved :: rest => { m with now := saved, stack := rest }
    | [] => m
  | .commit => { m with stack := m.stack.drop 1 }
  | .endTransaction =>
    let now := { m.now with transient := [] }
    { m with now, start := now, created := [], stack := [] }
where
  /-- Whether the fork destroys an account that a change leaves empty. -/
  paris : Bool := m.fork ≥ .paris

/-- What a transaction reads of the model, one word for each account.

The word holds the account, whether it has storage and is alive, and for each key the word of
its storage, the word before the transaction, and the transient word. -/
def TrackerModel.reads (m : TrackerModel) : List String :=
  (List.range addresses.length).map fun a =>
    let account := match m.now.account a with
      | some x => s!"{x.nonce}/{x.balance}/{x.code}"
      | none => "none"
    let hasStorage := m.now.storage.any (·.1.1 == a)
    let alive := (m.now.account a).any (· != ⟨0, 0, 0⟩)
    let keys := (List.range slots.length).map fun k =>
      let original := if m.created.contains a then 0 else m.start.slot a k
      s!"{m.now.slot a k},{original},{(m.now.transient.lookup (a, k)).getD 0}"
    ";".intercalate ([account, toString hasStorage, toString alive] ++ keys)

/-- The model: operations on a few accounts and keys, with small balances so that accounts empty.

A rollback and a commit need an open snapshot, and a transaction ends with none open.
An account is touched, and the touched empty accounts destroyed, only before Paris. -/
def genOp (m : TrackerModel) : Gen Op :=
  let account := Gen.nat (.constant 0 (addresses.length - 1))
  let key := Gen.nat (.constant 0 (slots.length - 1))
  let amount := Gen.frequency [(3, Gen.nat (.constant 0 3)), (1, Gen.nat (.exponential 0 (2 ^ 64)))]
  let word := Gen.frequency [(1, pure 0), (2, Gen.nat (.constant 1 3))]
  Gen.frequency ([
    (3, Op.setBalance <$> account <*> amount),
    (2, Op.incrementNonce <$> account),
    (2, Op.setCode <$> account <*> Gen.nat (.constant 0 (codes.length - 1))),
    (3, Op.moveEther <$> account <*> account <*> amount),
    (1, Op.createEther <$> account <*> amount),
    (5, Op.setStorage <$> account <*> key <*> word),
    (1, Op.destroyStorage <$> account),
    (2, Op.destroyAccount <$> account),
    (1, Op.markCreated <$> account),
    (2, Op.setTransient <$> account <*> key <*> word),
    (3, pure .snapshot)]
    ++ (if m.stack.isEmpty then [(2, pure Op.endTransaction)]
      else [(3, pure Op.rollback), (2, pure Op.commit)])
    ++ (if m.fork < .paris then [(2, Op.touch <$> account),
      (2, Op.destroyTouched <$> Gen.subsequence (List.range addresses.length))] else []))

/-- Whether an operation may run in a state of the model. -/
def opAllowed (m : TrackerModel) : Op → Bool
  | .rollback | .commit => !m.stack.isEmpty
  | .endTransaction => m.stack.isEmpty
  | .touch _ | .destroyTouched _ => m.fork < .paris
  | _ => true

/-- The forks whose rules for an empty account differ. -/
def trackerForks : List (Fork × String) :=
  [(.tangerineWhistle, "tangerine_whistle"), (.spuriousDragon, "spurious_dragon"),
    (.istanbul, "istanbul"), (.london, "london"), (.paris, "paris"), (.dencun, "cancun"),
    (.fusaka, "osaka")]

/-- The model as a state machine, from the empty state at a fork. -/
def trackerModel : Model TrackerModel Op where
  initState := (fun fork => { fork := fork.1 }) <$> Gen.element trackerForks
  transitions := genOp
  apply := TrackerModel.step
  preconditions := opAllowed

/-! ## EthLib's tracker -/

/-- The tracker under test: the transaction, and the snapshot of each open call. -/
structure Tracker where
  /-- The transaction now. -/
  tx : TransactionState
  /-- The open snapshots, the last one first. -/
  stack : List TransactionState := []

/-- A tracker with no account. -/
def Tracker.empty : Tracker := ⟨.ofBlock ⟨⟨∅, ∅, ∅⟩, ∅, ∅, ∅, ∅⟩, []⟩

/-- The tracker after an operation, as the EVM uses it.

An operation that fails leaves it as it was. -/
def Tracker.step (fork : Fork) (t : Tracker) : Op → Tracker
  | .setBalance a n => attempt (t.tx.setAccountBalance fork (addressAt a) (.ofNat 256 n))
  | .incrementNonce a => attempt (t.tx.incrementNonce fork (addressAt a))
  | .setCode a c => attempt (t.tx.setCode fork (addressAt a) (codes.getD c .empty))
  | .moveEther a b n => attempt (t.tx.moveEther fork (addressAt a) (addressAt b) (.ofNat 256 n))
  | .createEther a n => attempt (t.tx.createEther fork (addressAt a) (.ofNat 256 n))
  | .setStorage a k v => attempt (t.tx.setStorage (addressAt a) (slotAt k) (.ofNat 256 v))
  | .destroyStorage a => { t with tx := t.tx.destroyStorage (addressAt a) }
  | .destroyAccount a => { t with tx := t.tx.destroyAccount (addressAt a) }
  | .markCreated a => { t with tx := t.tx.markAccountCreated (addressAt a) }
  | .setTransient a k v =>
    { t with tx := t.tx.setTransientStorage (addressAt a) (slotAt k) (.ofNat 256 v) }
  | .touch a => { t with tx := t.tx.touchAccount (addressAt a) }
  | .destroyTouched as =>
    { t with tx := t.tx.destroyTouchedEmptyAccounts fork (as.map addressAt) }
  | .snapshot => { t with stack := t.tx :: t.stack }
  | .rollback =>
    match t.stack with
    | saved :: rest => ⟨t.tx.restoreTxState saved, rest⟩
    | [] => t
  | .commit => { t with stack := t.stack.drop 1 }
  | .endTransaction => ⟨t.tx.incorporateTxIntoBlock, []⟩
where
  /-- The tracker with the transaction of a result, or as it was after an error. -/
  attempt (result : Except StateError TransactionState) : Tracker :=
    match result with
    | .ok tx => { t with tx }
    | .error _ => t

/-- What a transaction reads of the tracker, in the words of the model. -/
def Tracker.reads (t : Tracker) : List String :=
  addresses.map fun address =>
    let account := match t.tx.getAccountOptional address with
      | some x =>
        let code := match t.tx.getCode x.codeHash with
          | .ok code =>
            toString ((codes.findIdx? fun (c : ByteArray) => c.data == code.data).getD 99)
          | .error _ => "missing"
        s!"{x.nonce}/{x.balance.toNat}/{code}"
      | none => "none"
    let keys := slots.map fun key =>
      s!"{(t.tx.getStorage address key).toNat},{(t.tx.getStorageOriginal address key).toNat},\
        {(t.tx.getTransientStorage address key).toNat}"
    ";".intercalate ([account, toString (t.tx.accountHasStorage address),
      toString (t.tx.isAccountAlive address)] ++ keys)

/-- The accounts and the storage of a state, in the words of the model with no transaction. -/
def stateWords (state : State) : List String :=
  addresses.map fun address =>
    let account := match state.accounts[address]? with
      | some x => s!"{x.nonce}/{x.balance.toNat}"
      | none => "none"
    ";".intercalate (account :: slots.map fun key => toString (state.getStorage address key).toNat)

/-- The state of the model, in the same words. -/
def TrackerModel.stateWords (m : TrackerModel) : List String :=
  (List.range addresses.length).map fun a =>
    let account := match m.now.account a with
      | some x => s!"{x.nonce}/{x.balance}"
      | none => "none"
    ";".intercalate (account :: (List.range slots.length).map fun k => toString (m.now.slot a k))

/-- The tracker reads as the model after every operation.

The model copies its whole state at a snapshot, and the tracker keeps writes in layers.
When a transaction ends, the state that the block's writes give is the state of the model.
A state holds no storage for an account that it does not hold. -/
def trackerMachine : StateMachine TrackerModel Op Tracker IO where
  toModel := trackerModel
  initSut _ := pure .empty
  applySut t m op := pure (t.step m.fork op)
  invariants t m := do
    t.reads === m.reads
    if m.stack.isEmpty && m.now == m.start then
      let state := t.tx.parent.applyChanges
      stateWords state === m.stateWords
      -- The storage of an account that left the state leaves with it, whatever its address.
      for (address, _) in state.storage.toList do
        ensure (state.accounts.contains address || (m.now.storage.any fun ((a, _), _) =>
          addressAt a == address)) "the state holds storage that no account and no model has"

/-! ## The tracker beside `state.py`, one command type for each operation -/

/-- The state of a scenario: the tracker, and whether the oracle holds its twin yet. -/
structure Beside where
  /-- EthLib's tracker. -/
  tracker : Tracker := .empty
  /-- Whether the oracle was told to start a state. -/
  started : Bool := false
  /-- How many snapshots are open. -/
  depth : Nat := 0

instance : Inhabited Beside := ⟨{}⟩

/-- What a scenario is built from: the oracle and the fork. -/
structure BesideContext where
  oracle : Oracle
  fork : Fork × String

/-- Run an operation on both sides, and compare what each then reads.

The oracle answers the reads of its state, and at the end of a transaction its state root too. -/
def runBeside (ctx : BesideContext) (op : Op) (s : Beside) : TestT IO Beside := do
  unless s.started do
    let _ ← ctx.oracle.ask ["state", "new", ctx.fork.2]
  let tracker := s.tracker.step ctx.fork.1 op
  let answer ← ctx.oracle.ask ("state" :: op.words)
  let reads := tracker.reads
  let mine ← match op with
    | .endTransaction =>
      let state := tracker.tx.parent.applyChanges
      pure (reads ++ [orError (hexV <$> (stateRoot keccak256 state).mapError fun _ => ())])
    | _ => pure reads
  -- The reference has transient storage from Dencun and the original word from Constantinople,
  -- so those words are compared from there.
  let strip (word : String) : String :=
    ";".intercalate ((word.splitOn ";").map fun part =>
      match part.splitOn "," with
      | [now, original, transient] =>
        s!"{now},{if ctx.fork.1 ≥ .constantinople then original else "x"},\
          {if ctx.fork.1 ≥ .dencun then transient else "0"}"
      | _ => part)
  " ".intercalate (mine.map strip) === answer
  let depth := match op with
    | .snapshot => s.depth + 1
    | .rollback | .commit => s.depth - 1
    | _ => s.depth
  pure { tracker, started := true, depth }

/-- A command of a scenario: an operation, with the oracle and the fork that run it.

`Command.apply` does not see the context, so each command carries it. -/
structure Step where
  ctx : BesideContext
  op : Op

/-- Whether a step may run: the rule of the model, on the count of open snapshots. -/
def Step.allowed (c : Step) (s : Beside) : Bool :=
  match c.op with
  | .rollback | .commit => 0 < s.depth
  | .endTransaction => s.depth = 0
  | .touch _ | .destroyTouched _ => c.ctx.fork.1 < .paris
  | _ => true

/-- An account of the tests. -/
def genAccountIndex : Gen Nat := Gen.nat (.constant 0 (addresses.length - 1))

/-- A key of the tests. -/
def genSlotIndex : Gen Nat := Gen.nat (.constant 0 (slots.length - 1))

/-- A small amount, so that balances reach zero. -/
def genAmount : Gen Nat := Gen.nat (.constant 0 3)

/-- Set a balance. -/
structure WriteBalance extends Step
/-- Add one to a nonce. -/
structure BumpNonce extends Step
/-- Set a code. -/
structure WriteCode extends Step
/-- Move ether between two accounts. -/
structure MoveEther extends Step
/-- Write a storage slot. -/
structure WriteStorage extends Step
/-- Wipe a storage. -/
structure WipeStorage extends Step
/-- Destroy an account. -/
structure DestroyAccount extends Step
/-- Mark an account as created by the transaction. -/
structure MarkCreated extends Step
/-- Write a transient storage slot. -/
structure WriteTransient extends Step
/-- Touch an account, before Paris. -/
structure TouchAccount extends Step
/-- Destroy the touched empty accounts, before Paris. -/
structure SweepTouched extends Step
/-- Open a snapshot. -/
structure OpenSnapshot extends Step
/-- Roll back to the last snapshot. -/
structure RollBack extends Step
/-- Drop the last snapshot and keep the writes. -/
structure CommitSnapshot extends Step
/-- End the transaction. -/
structure EndTransaction extends Step

instance : Command WriteBalance Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a n => ⟨⟨ctx, .setBalance a n⟩⟩) <$> genAccountIndex <*> genAmount

instance : Command BumpNonce Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a => ⟨⟨ctx, .incrementNonce a⟩⟩) <$> genAccountIndex

instance : Command WriteCode Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a k => ⟨⟨ctx, .setCode a k⟩⟩) <$> genAccountIndex <*>
    Gen.nat (.constant 0 (codes.length - 1))

instance : Command MoveEther Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a b n => ⟨⟨ctx, .moveEther a b n⟩⟩) <$> genAccountIndex <*>
    genAccountIndex <*> genAmount

instance : Command WriteStorage Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a k v => ⟨⟨ctx, .setStorage a k v⟩⟩) <$> genAccountIndex <*>
    genSlotIndex <*> genAmount

instance : Command WipeStorage Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a => ⟨⟨ctx, .destroyStorage a⟩⟩) <$> genAccountIndex

instance : Command DestroyAccount Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a => ⟨⟨ctx, .destroyAccount a⟩⟩) <$> genAccountIndex

instance : Command MarkCreated Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a => ⟨⟨ctx, .markCreated a⟩⟩) <$> genAccountIndex

instance : Command WriteTransient Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a k v => ⟨⟨ctx, .setTransient a k v⟩⟩) <$> genAccountIndex <*>
    genSlotIndex <*> genAmount

instance : Command TouchAccount Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun a => ⟨⟨ctx, .touch a⟩⟩) <$> genAccountIndex

instance : Command SweepTouched Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := (fun as => ⟨⟨ctx, .destroyTouched as⟩⟩) <$>
    Gen.subsequence (List.range addresses.length)

instance : Command OpenSnapshot Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := pure ⟨⟨ctx, .snapshot⟩⟩

instance : Command RollBack Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := pure ⟨⟨ctx, .rollback⟩⟩

instance : Command CommitSnapshot Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := pure ⟨⟨ctx, .commit⟩⟩

instance : Command EndTransaction Beside BesideContext IO where
  check c := c.allowed
  apply c := runBeside c.ctx c.op
  label c := reprStr c.op
  build ctx := pure ⟨⟨ctx, .endTransaction⟩⟩

/-- The tracker reads as `state.py` of execution-specs after every command, at a fork.

The scenario draws random sequences of the commands, and each runs on both sides.
At the end of a transaction the state root of the block's writes is the reference's. -/
def trackerScenario (mode : Mode) (ctx : BesideContext) : Property IO :=
  scenario mode ctx [
    Command.gen WriteBalance, Command.gen WriteStorage, Command.gen OpenSnapshot,
    Command.gen BumpNonce, Command.gen WriteCode, Command.gen MoveEther,
    Command.gen WriteStorage, Command.gen RollBack, Command.gen WriteStorage,
    Command.gen WipeStorage, Command.gen DestroyAccount, Command.gen MarkCreated,
    Command.gen WriteTransient, Command.gen TouchAccount, Command.gen SweepTouched,
    Command.gen OpenSnapshot, Command.gen WriteBalance, Command.gen CommitSnapshot,
    Command.gen EndTransaction, Command.gen WriteStorage, Command.gen EndTransaction]

end ExecutionProperty

namespace ExecutionProperty

/-- A change of an answer of `eth_getProof` that makes it false. -/
inductive Tamper where
  | nonce
  | balance
  | codeHash
  | storageHash
  | slotValue (index : Nat)
  | slotKey (index : Nat)
  | swapSlotProofs
  deriving Repr

/-- An answer of `eth_getProof` holds against the state root exactly when it is true.

The state comes from a sequence of operations on the tracker.
The answer that EthLib builds for an account and some slots verifies, and shows what the state
holds: the account or its absence, and each slot as set or not.
An answer with one field changed is refused. -/
def accountProofs : Property IO := pureIO do
  let (model, ops) ← forAll (trackerModel.sequence (.linear 1 40))
  let account ← forAll genAccountIndex
  let keys ← forAll (Gen.list (.constant 0 3) genSlotIndex)
  let tamper ← forAll (Gen.element [Tamper.nonce, .balance, .codeHash, .storageHash, .slotValue 0,
    .slotValue 1, .slotKey 0, .swapSlotProofs])
  let tracker := (ops.foldl (Tracker.step model.fork) .empty).step model.fork .endTransaction
  let final := (ops.foldl TrackerModel.step model).step .endTransaction
  let state := tracker.tx.parent.applyChanges
  let .ok stateRootHash := stateRoot keccak256 state | failWith "no state root"
  let address := addressAt account
  let .ok answer := AccountProof.ofState keccak256 state address (keys.map slotAt)
    | failWith "no answer"
  let exists_ := (final.now.account account).isSome
  let truth : AccountOutcome := if exists_ then
      .present (keys.map fun k => if final.now.slot account k = 0 then .absent else .set)
    else .absent
  match answer.verify keccak256 stateRootHash with
  | .ok outcome => outcome === truth
  | .error error => failWith s!"the answer of EthLib is refused: {repr error}"
  let other : Hash32 := Vector.replicate 32 0x5a
  let bump (s : StorageProof) : StorageProof := { s with value := s.value + 1 }
  let rekey (s : StorageProof) : StorageProof :=
    { s with key := if s.key == slotAt 0 then slotAt 1 else slotAt 0 }
  let changed : Option AccountProof := match tamper with
    | .nonce => some { answer with nonce := answer.nonce + 1 }
    | .balance => some { answer with balance := answer.balance + 1 }
    | .codeHash => some { answer with codeHash := other }
    | .storageHash => some { answer with storageHash := other }
    | .slotValue i =>
      if i < answer.storageProof.length then
        some { answer with storageProof := answer.storageProof.modify i bump }
      else none
    | .slotKey i =>
      -- Another key reads another slot, and the answer is false when the two words differ.
      match answer.storageProof[i]? with
      | some s =>
        if state.getStorage address (rekey s).key != s.value then
          some { answer with storageProof := answer.storageProof.modify i rekey }
        else none
      | none => none
    | .swapSlotProofs =>
      match answer.storageProof with
      | a :: b :: rest =>
        -- A trie of one leaf proves every key by that leaf, so equal proofs are no change.
        if a.proof.map hex != b.proof.map hex then
          some { answer with storageProof :=
            { a with proof := b.proof } :: { b with proof := a.proof } :: rest }
        else none
      | _ => none
  if let some false_ := changed then
    match false_.verify keccak256 stateRootHash with
    | .ok outcome => failWith s!"a false answer is accepted as {repr outcome} after {repr tamper}"
    | .error _ => pure ()

end ExecutionProperty

namespace ExecutionProperty

/-- An answer of `eth_getProof` as go-ethereum gives it for an account with no storage holds.

go-ethereum answers a slot of an empty storage trie with the word 0 and no proof node.
EthLib refuses that answer, so this property fails: see the findings. -/
def emptyStorageAnswer : Property IO := pureIO do
  let balance ← forAll (Gen.nat (.constant 1 100))
  let key ← forAll genSlotIndex
  let address := addressAt 1
  let tracker := (Tracker.empty.step .fusaka (.setBalance 1 balance)).step .fusaka .endTransaction
  let state := tracker.tx.parent.applyChanges
  let .ok stateRootHash := stateRoot keccak256 state | failWith "no state root"
  let .ok answer := AccountProof.ofState keccak256 state address [slotAt key]
    | failWith "no answer"
  let geth := { answer with storageProof := answer.storageProof.map fun (s : StorageProof) => { s with proof := [] } }
  match geth.verify keccak256 stateRootHash with
  | .ok outcome => outcome === .present [.absent]
  | .error error => failWith s!"EthLib refuses the answer: {repr error}"

end ExecutionProperty

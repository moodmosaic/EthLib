import Property.Execution.Common

/-!
# The tracker of writes, as a state machine

The tracker keeps the writes of a block and of a transaction apart from the state.

It keeps snapshots for the calls that fail.

Two references run beside it on random sequences of operations.

- A model here, written from the text of `state.py` of execution-specs.
  It is one flat state, copied whole at each snapshot.
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

/-- The name of an operation, without its arguments. -/
def Op.name : Op → String
  | .setBalance .. => "setBalance"
  | .incrementNonce .. => "incrementNonce"
  | .setCode .. => "setCode"
  | .moveEther .. => "moveEther"
  | .createEther .. => "createEther"
  | .setStorage .. => "setStorage"
  | .destroyStorage .. => "destroyStorage"
  | .destroyAccount .. => "destroyAccount"
  | .markCreated .. => "markCreated"
  | .setTransient .. => "setTransient"
  | .touch .. => "touch"
  | .destroyTouched .. => "destroyTouched"
  | .snapshot => "snapshot"
  | .rollback => "rollback"
  | .commit => "commit"
  | .endTransaction => "endTransaction"

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

The word holds the account, and whether it has storage and is alive.

For each key it holds the storage word, the word before the transaction, and the transient word. -/
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

/-- An account of the tests. -/
def genAccountIndex : Gen Nat := Gen.nat (.constant 0 (addresses.length - 1))

/-- A key of the tests. -/
def genSlotIndex : Gen Nat := Gen.nat (.constant 0 (slots.length - 1))

/-- A small amount, so that balances reach zero. -/
def genAmount : Gen Nat := Gen.nat (.constant 0 3)

/-- An account: three times in four one that the model holds, if it holds one. -/
def genLive (m : TrackerModel) : Gen Nat :=
  let held := m.now.accounts.map Prod.fst
  if held.isEmpty then genAccountIndex
  else Gen.frequency [(3, Gen.element held), (1, genAccountIndex)]

/-- A sender and an amount: mostly an account that holds ether, and at most what it holds. -/
def genSpend (m : TrackerModel) : Gen (Nat × Nat) :=
  let funded := m.now.accounts.filter fun (_, x) => 0 < x.balance
  let any := Gen.zip genAccountIndex genAmount
  if funded.isEmpty then any
  else Gen.frequency [(3, do
      let (a, x) ← Gen.element funded
      pure (a, ← Gen.frequency [(2, Gen.nat (.constant 1 x.balance)), (2, pure x.balance),
        (1, pure (x.balance + 1))])),
    (1, any)]

/-- A storage write: mostly to an account that the model holds, and often zero to a set word. -/
def genStorageWrite (m : TrackerModel) : Gen (Nat × Nat × Nat) :=
  let word := Gen.frequency [(1, pure 0), (3, Gen.nat (.constant 1 3))]
  let fresh := Gen.zip (genLive m) (Gen.zip genSlotIndex word)
  let held := m.now.storage.filter fun ((a, _), _) => (m.now.account a).isSome
  if held.isEmpty then fresh
  else Gen.frequency [(3, fresh),
    (1, (fun (((a, k), _) : (Nat × Nat) × Nat) v => (a, k, v)) <$> Gen.element held <*>
      Gen.element [0, 0, 1, 2])]

/-- The model: operations on a few accounts and keys, with small balances so that accounts empty.

A rollback and a commit need an open snapshot, and a transaction ends with none open.

An account is touched, and the touched empty accounts destroyed, only before Paris.

A write is mostly to an account that the model holds, so that storage and codes build up. -/
def genOp (m : TrackerModel) : Gen Op :=
  let account := genLive m
  let key := genSlotIndex
  let amount := Gen.frequency [(3, genAmount), (1, Gen.nat (.exponential 0 (2 ^ 64)))]
  let word := Gen.frequency [(1, pure 0), (2, Gen.nat (.constant 1 3))]
  Gen.frequency ([
    (3, Op.setBalance <$> account <*> amount),
    (2, Op.incrementNonce <$> account),
    (2, Op.setCode <$> account <*> Gen.nat (.constant 0 (codes.length - 1))),
    (3, (fun (a, n) b => Op.moveEther a b n) <$> genSpend m <*> genAccountIndex),
    (1, Op.createEther <$> account <*> amount),
    (6, (fun (a, k, v) => Op.setStorage a k v) <$> genStorageWrite m),
    (1, Op.destroyStorage <$> account),
    (1, Op.destroyAccount <$> account),
    (1, Op.markCreated <$> genAccountIndex),
    (2, Op.setTransient <$> genAccountIndex <*> key <*> word),
    (3, pure .snapshot)]
    ++ (if m.stack.isEmpty then [(2, pure Op.endTransaction)]
      else [(3, pure Op.rollback), (2, pure Op.commit)])
    ++ (if m.fork < .paris then [(2, Op.touch <$> genAccountIndex),
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

/-- The labels of an operation of the model: what it is, and what it did to the state. -/
def labelOp (before after : TrackerModel) (op : Op) :
    TestT IO Unit := do
  label s!"fork: {before.fork.name}"
  label s!"op: {op.name}"
  let changed := before.now != after.now
  let account (model : TrackerModel) (a : Nat) : Option Acct := model.now.account a
  match op with
  | .rollback =>
    label (if changed then "a rollback that undoes a write" else "a rollback of no write")
    coverMin 1 "a rollback that brings back an account"
      ((List.range addresses.length).any fun a => (account before a).isNone &&
        (account after a).isSome)
    coverMin 2 "a rollback that brings back a storage word"
      (before.now.storage != after.now.storage)
    coverMin 3 "a rollback inside another snapshot" (2 ≤ before.stack.length)
  | .commit => coverMin 2 "a commit inside another snapshot" (2 ≤ before.stack.length)
  | .snapshot =>
    coverMin 2 "snapshots: three deep or more" (3 ≤ after.stack.length)
  | .moveEther a b n =>
    label (if !changed ∧ 0 < n ∧ a ≠ b then "a move refused for the balance"
      else if a = b then "a move to the sender itself" else "a move that is made")
  | .setStorage a k v =>
    label (if (account before a).isNone then "a storage write to no account"
      else if v = 0 ∧ before.now.slot a k ≠ 0 then "a storage write that clears a word"
      else if v = 0 then "a storage write of zero to no word"
      else "a storage write of a word")
  | .destroyAccount a =>
    coverMin 3 "an account destroyed with storage" (before.now.storage.any (·.1.1 == a))
  | .destroyTouched _ =>
    classify "touched empty accounts destroyed" changed
  | .endTransaction =>
    coverMin 8 "a transaction ends with a changed state" (before.now != before.start)
    coverMin 2 "a transaction ends with storage in the state" (!after.now.storage.isEmpty)
    coverMin 3 "a transaction ends with transient storage" (!before.now.transient.isEmpty)
  | .setBalance a _ | .incrementNonce a | .setCode a _ | .createEther a _ =>
    classify "from Paris: a change leaves the account empty, and destroys it"
      (before.fork ≥ .paris && (account before a).isSome && (account after a).isNone)
    classify "before Paris: a change leaves an empty account"
      (before.fork < .paris && account after a == some ⟨0, 0, 0⟩)
  | _ => pure ()
  coverMin 11 "a read of a word that differs from the word before the transaction"
    ((List.range addresses.length).any fun a => (List.range slots.length).any fun k =>
      after.now.slot a k ≠ after.start.slot a k)

/-- The tracker reads as the model after every operation.

The model copies its whole state at a snapshot, and the tracker keeps writes in layers.

When a transaction ends, the state that the block's writes give is the state of the model.

A state holds no storage for an account that it does not hold. -/
def trackerMachine : StateMachine TrackerModel Op Tracker IO where
  toModel := trackerModel
  initSut _ := pure .empty
  applySut t before m op := do
    labelOp before m op
    pure (t.step m.fork op)
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

/-- The state of a scenario: the tracker, and the model that the generators read. -/
structure Beside where
  /-- EthLib's tracker. -/
  tracker : Tracker := .empty
  /-- The model of the tracker, which `next` moves while a sequence is generated. -/
  model : TrackerModel := { fork := .frontier }

instance : Inhabited Beside := ⟨{}⟩

/-- What a scenario is built from: the oracle and the fork. -/
structure BesideContext where
  oracle : Oracle
  fork : Fork × String

/-- The model of a state, at the fork of the context. -/
def Beside.modelAt (ctx : BesideContext) (s : Beside) : TrackerModel :=
  { s.model with fork := ctx.fork.1 }

/-- Run an operation on the three sides, and compare what each then reads.

The model answers first, then the oracle.

The oracle answers the reads of its state, and at the end of a transaction its state root too. -/
def runBeside (ctx : BesideContext) (op : Op) (s : Beside) : TestT IO Beside := do
  let before := s.modelAt ctx
  let after := before.step op
  labelOp before after op
  let tracker := s.tracker.step ctx.fork.1 op
  let answer ← ctx.oracle.ask ("state" :: op.words)
  let reads := tracker.reads
  reads === after.reads
  let mine ← match op with
    | .endTransaction =>
      let state := tracker.tx.parent.applyChanges
      coverMin 7 "a state root of a state with an account" (!state.accounts.isEmpty)
      coverMin 1 "a state root of a state with two accounts or more" (2 ≤ state.accounts.size)
      coverMin 2 "a state root of a state with storage" (!state.storage.isEmpty)
      pure (reads ++ [orError (hexV <$> (stateRoot keccak256 state).mapError fun _ => ())])
    | _ => pure reads
  -- The reference has transient storage from Dencun and the original word from Constantinople.
  --
  -- So those words are compared from there.
  let strip (word : String) : String :=
    ";".intercalate ((word.splitOn ";").map fun part =>
      match part.splitOn "," with
      | [now, original, transient] =>
        s!"{now},{if ctx.fork.1 ≥ .constantinople then original else "x"},\
          {if ctx.fork.1 ≥ .dencun then transient else "0"}"
      | _ => part)
  " ".intercalate (mine.map strip) === answer
  pure { tracker, model := after }

/-- A command of a scenario: an operation.

The oracle and the fork that run it are in the context. -/
structure Step where
  op : Op

/-- The instance of a command type that holds an operation, from its generator in a model state.

`check` is the rule of the model, and `next` is the step of the model.

So a command is generated for the accounts and the snapshots that the commands before it leave. -/
def stepCommand {κ : Type} (op : κ → Op) (gen : TrackerModel → Gen κ) :
    Command κ Beside BesideContext IO where
  check ctx c s := opAllowed (s.modelAt ctx) (op c)
  apply ctx c := runBeside ctx (op c)
  label c := reprStr (op c)
  build ctx := gen { fork := ctx.fork.1 }
  next ctx c s := { s with model := (s.modelAt ctx).step (op c) }
  buildIn ctx s := gen (s.modelAt ctx)

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

instance : Command WriteBalance Beside BesideContext IO :=
  stepCommand (·.op) fun m => (fun a n => ⟨⟨.setBalance a n⟩⟩) <$> genLive m <*> genAmount

instance : Command BumpNonce Beside BesideContext IO :=
  stepCommand (·.op) fun m => (fun a => ⟨⟨.incrementNonce a⟩⟩) <$> genLive m

instance : Command WriteCode Beside BesideContext IO :=
  stepCommand (·.op) fun m => (fun a k => ⟨⟨.setCode a k⟩⟩) <$> genLive m <*>
    Gen.nat (.constant 0 (codes.length - 1))

instance : Command MoveEther Beside BesideContext IO :=
  stepCommand (·.op) fun m => (fun (a, n) b => ⟨⟨.moveEther a b n⟩⟩) <$> genSpend m <*>
    genAccountIndex

instance : Command WriteStorage Beside BesideContext IO :=
  stepCommand (·.op) fun m => (fun (a, k, v) => ⟨⟨.setStorage a k v⟩⟩) <$> genStorageWrite m

instance : Command WipeStorage Beside BesideContext IO :=
  stepCommand (·.op) fun m => (fun a => ⟨⟨.destroyStorage a⟩⟩) <$> genLive m

instance : Command DestroyAccount Beside BesideContext IO :=
  stepCommand (·.op) fun m => (fun a => ⟨⟨.destroyAccount a⟩⟩) <$> genLive m

instance : Command MarkCreated Beside BesideContext IO :=
  stepCommand (·.op) fun _ => (fun a => ⟨⟨.markCreated a⟩⟩) <$> genAccountIndex

instance : Command WriteTransient Beside BesideContext IO :=
  stepCommand (·.op) fun _ => (fun a k v => ⟨⟨.setTransient a k v⟩⟩) <$> genAccountIndex <*>
    genSlotIndex <*> genAmount

instance : Command TouchAccount Beside BesideContext IO :=
  stepCommand (·.op) fun _ => (fun a => ⟨⟨.touch a⟩⟩) <$> genAccountIndex

instance : Command SweepTouched Beside BesideContext IO :=
  stepCommand (·.op) fun _ => (fun as => ⟨⟨.destroyTouched as⟩⟩) <$>
    Gen.subsequence (List.range addresses.length)

instance : Command OpenSnapshot Beside BesideContext IO :=
  stepCommand (·.op) fun _ => pure ⟨⟨.snapshot⟩⟩

instance : Command RollBack Beside BesideContext IO :=
  stepCommand (·.op) fun _ => pure ⟨⟨.rollback⟩⟩

instance : Command CommitSnapshot Beside BesideContext IO :=
  stepCommand (·.op) fun _ => pure ⟨⟨.commit⟩⟩

instance : Command EndTransaction Beside BesideContext IO :=
  stepCommand (·.op) fun _ => pure ⟨⟨.endTransaction⟩⟩

/-- The tracker reads as `state.py` of execution-specs after every command, at a fork.

The scenario draws random sequences of the commands, and each runs on both sides.

The setup starts the state of the reference, and a command is drawn for the state before it.

At the end of a transaction the state root of the block's writes is the reference's. -/
def trackerScenario (mode : Mode) (ctx : BesideContext) : Property IO :=
  scenario mode ctx [
    Command.gen WriteBalance, Command.gen WriteStorage, Command.gen OpenSnapshot,
    Command.gen BumpNonce, Command.gen WriteCode, Command.gen MoveEther,
    Command.gen WriteStorage, Command.gen RollBack, Command.gen WriteStorage,
    Command.gen WipeStorage, Command.gen DestroyAccount, Command.gen MarkCreated,
    Command.gen WriteTransient, Command.gen TouchAccount, Command.gen SweepTouched,
    Command.gen OpenSnapshot, Command.gen WriteBalance, Command.gen CommitSnapshot,
    Command.gen EndTransaction, Command.gen WriteStorage, Command.gen EndTransaction,
    Command.gen DestroyAccount, Command.gen RollBack]
    (.linear 1 60) fun s => do
      let _ ← ctx.oracle.ask ["state", "new", ctx.fork.2]
      pure s

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

The answer that EthLib builds for an account and some slots verifies.

It shows what the state holds: the account or its absence, and each slot as set or not.

An answer with one field changed is refused. -/
def accountProofs : Property IO := propertyM do
  let (model, ops) ← forAll (trackerModel.sequence (.linear 1 40))
  let account ← forAll (genLive (ops.foldl TrackerModel.step model))
  -- Half the states gain an account with a balance and a few storage words at the end.
  let extra ← forAll (Gen.frequency [(1, pure []),
    (1, (Op.setBalance account 1 :: ·) <$> Gen.list (.constant 1 4)
      (Op.setStorage account <$> genSlotIndex <*> Gen.nat (.constant 0 3)))])
  let ops := ops ++ extra
  let keys ← forAll (Gen.frequency [(1, Gen.list (.constant 0 3) genSlotIndex),
    (2, Gen.shuffle (List.range slots.length))])
  let tamper ← forAll (Gen.element [Tamper.nonce, .balance, .codeHash, .storageHash, .slotValue 0,
    .slotValue 1, .slotKey 0, .slotKey 1, .swapSlotProofs, .swapSlotProofs])
  pure do
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
    label s!"fork: {model.fork.name}"
    label (if exists_ then "the account exists" else "the account is absent")
    label s!"slots asked: {keys.length}"
    coverMin 15 "a slot that is set" (exists_ && keys.any fun k => final.now.slot account k ≠ 0)
    coverMin 14 "a slot that is not set, in a storage with words"
      (exists_ && final.now.storage.any (·.1.1 == account) &&
        keys.any fun k => final.now.slot account k = 0)
    coverMin 8 "a slot of an account with no storage"
      (exists_ && !keys.isEmpty && !final.now.storage.any (·.1.1 == account))
    let words := (final.now.storage.filter (·.1.1 == account)).length
    coverMin 9 "the storage of the account holds one word" (exists_ && words = 1)
    coverMin 8 "the storage of the account holds two words or more" (exists_ && 2 ≤ words)
    let accounts := final.now.accounts.length
    label (if accounts = 0 then "accounts in the state: 0" else if accounts = 1 then
      "accounts in the state: 1" else "accounts in the state: 2+")
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
    let tamperName := ((reprStr tamper).splitOn " ").headD ""
    let tamperName := (tamperName.splitOn ".").getLastD tamperName
    label (if changed.isSome then s!"a false answer: {tamperName}" else "no false answer to try")
    coverMin 3 "a false answer about an account that is absent" (changed.isSome && !exists_)
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
  let geth := { answer with
    storageProof := answer.storageProof.map fun (s : StorageProof) => { s with proof := [] } }
  match geth.verify keccak256 stateRootHash with
  | .ok outcome => outcome === .present [.absent]
  | .error error => failWith s!"EthLib refuses the answer: {repr error}"

end ExecutionProperty

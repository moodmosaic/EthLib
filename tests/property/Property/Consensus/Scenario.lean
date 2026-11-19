import Property.Consensus.Operations

/-!
# A block's operations in any order, as commands

Each operation of block processing is a command of its own type.

A scenario starts from a state of settled validators and runs a random sequence of commands.

The state that EthLib reaches after one command is the state the next one meets, on both sides.

So the sequence reaches states that no single step does:

- An exit after a slashing.
- A consolidation of a validator with a pending withdrawal.
- An epoch boundary between two requests.

A command that the reference refuses must be refused, and it leaves the state as it was.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ConsensusProperty

/-- What a command needs: the oracle, the fork and the state to start from. -/
structure Env (fork : Fork) where
  /-- The reference. -/
  oracle : Oracle
  /-- The name of the fork in consensus-specs. -/
  forkName : String
  /-- The SSZ bytes of the first state. -/
  initial : ByteArray

/-- The builders of the first state, by key: each is active and may exit once. -/
def firstBuilders : List Nat := List.range 4

/-- The state of a scenario: EthLib's state after the commands so far, or none before the first. -/
structure Chain (fork : Fork) where
  /-- The state, where a command has changed the first one. -/
  state : Option (State fork) := none
  /-- The builders that no command has asked to exit yet.

  Commands are generated before any runs, so this is what a generator knows of the state:

  `Command.next` moves it, and `Command.buildIn` reads it. -/
  staying : List Nat := firstBuilders

instance {fork : Fork} : Inhabited (Chain fork) := ⟨{}⟩

/-- A call with its argument words, ready to run. -/
structure Invocation (fork : Fork) where
  /-- The oracle, the fork and the first state. -/
  env : Env fork
  /-- The name of the call in consensus-specs. -/
  name : String
  /-- The words of the argument. -/
  words : List String

/-- The call of a name. -/
def callOf (name : String) : Option Call := operations.find? (·.name = name)

/-- Whether the fork has the call. -/
def Invocation.available {fork : Fork} (i : Invocation fork) : Bool :=
  (callOf i.name).any fun call => call.forks.any (·.1 = i.env.forkName)

/-- Run a call on the state of the scenario, on both sides, and keep EthLib's state after. -/
def Invocation.apply {fork : Fork} (i : Invocation fork) (chain : Chain fork) :
    TestT IO (Chain fork) := do
  let some call := callOf i.name | failWith s!"no call {i.name}"
  let bytes ← match chain.state with
    | none => pure i.env.initial
    | some state =>
      match SszType.serialize state with
      | .ok bytes => pure bytes
      | .error _ => failWith "EthLib cannot write its own state"
  let answer ← i.env.oracle.ask (["on", i.env.forkName, i.name, hex bytes] ++ i.words)
  match ← compareAnswer i.env.oracle i.env.forkName fork answer i.words (call.run fork) with
  | some post => pure { chain with state := some post }
  | none => pure chain

/-- The SSZ bytes of the state of the scenario, or none if EthLib cannot write it. -/
def Chain.bytes {fork : Fork} (env : Env fork) (chain : Chain fork) : Option ByteArray :=
  match chain.state with
  | none => some env.initial
  | some state => (SszType.serialize state).toOption

/-- The label of a call in a report. -/
def Invocation.label {fork : Fork} (i : Invocation fork) : String :=
  s!"{i.name}({" ".intercalate i.words})"

/-- The generator of a call with its argument. -/
def Invocation.build {fork : Fork} (name : String) (env : Env fork) : Gen (Invocation fork) :=
  (fun words => ⟨env, name, words⟩) <$> ((callOf name).map (·.arguments)).getD (pure [])

/-- A voluntary exit. -/
structure VoluntaryExitCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (VoluntaryExitCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := VoluntaryExitCommand.mk <$> Invocation.build "process_voluntary_exit" env

/-- A proposer slashing. -/
structure ProposerSlashingCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (ProposerSlashingCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := ProposerSlashingCommand.mk <$> Invocation.build "process_proposer_slashing" env

/-- An attester slashing. -/
structure AttesterSlashingCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (AttesterSlashingCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := AttesterSlashingCommand.mk <$> Invocation.build "process_attester_slashing" env

/-- An attestation. -/
structure AttestationCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (AttestationCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := AttestationCommand.mk <$> Invocation.build "process_attestation" env

/-- From Capella: a change of BLS credentials. -/
structure BlsChangeCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (BlsChangeCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := BlsChangeCommand.mk <$> Invocation.build "process_bls_to_execution_change" env

/-- Before Fulu: a deposit of the deposit contract, with its proof. -/
structure DepositCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (DepositCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := DepositCommand.mk <$> Invocation.build "process_deposit" env

/-- From Electra: a deposit request. -/
structure DepositRequestCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (DepositRequestCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := DepositRequestCommand.mk <$> Invocation.build "process_deposit_request" env

/-- From Electra: a withdrawal request. -/
structure WithdrawalRequestCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (WithdrawalRequestCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := WithdrawalRequestCommand.mk <$> Invocation.build "process_withdrawal_request" env

/-- From Electra: a consolidation request. -/
structure ConsolidationRequestCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} :
    Command (ConsolidationRequestCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env :=
    ConsolidationRequestCommand.mk <$> Invocation.build "process_consolidation_request" env

/-- From Altair: a sync aggregate. -/
structure SyncAggregateCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (SyncAggregateCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := SyncAggregateCommand.mk <$> Invocation.build "process_sync_aggregate" env

/-- From Capella: the withdrawals of a block. -/
structure WithdrawalsCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (WithdrawalsCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := WithdrawalsCommand.mk <$> Invocation.build "process_withdrawals" env

/-- From Gloas: a deposit request of a builder. -/
structure BuilderDepositCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (BuilderDepositCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env :=
    BuilderDepositCommand.mk <$> Invocation.build "process_builder_deposit_request" env

/-- From Gloas: an exit request of a builder.

Generated blind, a request names a builder that never was or that has left, and none takes effect.

So most requests are generated for the state: a builder that stays, with its own address. -/
structure BuilderExitCommand (fork : Fork) where
  call : Invocation fork

/-- The builder that a request names with its own address, if it does. -/
def BuilderExitCommand.leaving {fork : Fork} (c : BuilderExitCommand fork) : Option Nat :=
  match c.call.words.map (·.splitOn ",") with
  | [["9", key]] => key.toNat?
  | _ => none

instance {fork : Fork} : Command (BuilderExitCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c chain := do
    let after ← c.call.apply chain
    -- A scenario whose requests all do nothing does not test the exit of a builder.
    cover 5 "a builder exit took effect" (after.bytes c.call.env != chain.bytes c.call.env)
    pure after
  label c := c.call.label
  build env := BuilderExitCommand.mk <$> Invocation.build "process_builder_exit_request" env
  next c chain := { chain with staying := chain.staying.filter (some · != c.leaving) }
  buildIn env chain :=
    let blind := BuilderExitCommand.mk <$> Invocation.build "process_builder_exit_request" env
    if chain.staying.isEmpty then blind
    else Gen.frequency [
      (4, (fun key => ⟨⟨env, "process_builder_exit_request", [s!"9,{key}"]⟩⟩) <$>
        Gen.element chain.staying),
      (1, blind)]

/-- Some slots pass, with the epoch transition at each boundary. -/
structure SlotsCommand (fork : Fork) where
  call : Invocation fork

instance {fork : Fork} : Command (SlotsCommand fork) (Chain fork) (Env fork) IO where
  check c _ := c.call.available
  apply c := c.call.apply
  label c := c.call.label
  build env := SlotsCommand.mk <$> Invocation.build "process_slots" env

/-- The words of the first state: settled validators, three of them large, at a late slot.

A fork without builders ignores theirs. -/
def initialWords : List String :=
  let validator (i : Nat) : String :=
    let effective := if i % 5 = 0 then 2048 else 32
    let credentials := if i % 5 = 0 then 2 else i % 3
    s!"v={credentials},{i % 4},{effective * increment},{effective * increment + i * 300000000},\
0,0,0,{far},{far},7,7,0"
  -- From Gloas: builders that deposited before the finalized epoch, so that each is active.
  let builder (key : Nat) : String := s!"b={key},{key},{(key + 1) * increment},0,{far}"
  ["slot=805", "fin=c-2", "pj=c-2", "cj=c-1", "bits=15", "sync=0", "lookahead",
    s!"drsi={far}", "churn=0,0,0,0,0"] ++ (List.range 20).map validator ++
    firstBuilders.map builder

/-- The scenario of a fork: every operation the fork has, in any order, from the first state.

The slots command is listed twice, so that epochs pass between the operations. -/
def blockScenario (oracle : Oracle) (forkName : String) (fork : Fork) (mode : Mode) :
    IO (Property IO) := do
  oracle.stdin.putStrLn ("\t".intercalate (["st", forkName, "get_current_epoch"] ++ initialWords))
  oracle.stdin.flush
  let answer ← oracle.stdout.getLine
  let some initial := unhex? ((answer.splitOn " ").headD "")
    | throw (IO.userError s!"no first state: {answer.take 200}")
  let env : Env fork := ⟨oracle, forkName, initial⟩
  pure (scenario (σ := Chain fork) mode env [
    Command.gen (VoluntaryExitCommand fork),
    Command.gen (ProposerSlashingCommand fork),
    Command.gen (AttesterSlashingCommand fork),
    Command.gen (AttestationCommand fork),
    Command.gen (BlsChangeCommand fork),
    Command.gen (DepositCommand fork),
    Command.gen (DepositRequestCommand fork),
    Command.gen (WithdrawalRequestCommand fork),
    Command.gen (ConsolidationRequestCommand fork),
    Command.gen (SyncAggregateCommand fork),
    Command.gen (WithdrawalsCommand fork),
    Command.gen (BuilderDepositCommand fork),
    Command.gen (BuilderExitCommand fork),
    Command.gen (SlotsCommand fork),
    Command.gen (SlotsCommand fork)])

end ConsensusProperty

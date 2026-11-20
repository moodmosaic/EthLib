import Property.Evm.Program
import Property.Evm.Trace
import Property.Evm.Glamsterdam

/-!
# Whole programs beside the reference

A message runs a generated program in EthLib and in the Python execution-specs.

Both sides print what the message left, and the two texts must agree.

An observer of EthLib's run names what the program reached, for the shares of the report.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Evm

namespace EvmProperty

/-- The gas of a run, drawn before the run is known. -/
inductive GasChoice where
  /-- That much gas, which is enough for most programs. -/
  | ample (gas : Nat)
  /-- A share, in percent, of what the run uses with ample gas. -/
  | part (percent : Nat)
  /-- What the run uses with ample gas, and that much more or less. -/
  | edge (delta : Int)
  deriving Repr

/-- The gas of a run with ample gas. -/
def ampleGas : Nat := 3000000

/-- A choice of gas: mostly ample, else around what the run needs, where gas runs out late. -/
def genRunGas : Gen GasChoice :=
  Gen.frequency [
    (10, GasChoice.ample <$> Gen.frequency [(6, pure ampleGas), (1, pure 30000000),
      (1, Gen.nat (.linear 100000 ampleGas))]),
    (2, GasChoice.part <$> Gen.nat (.constant 0 99)),
    (3, GasChoice.edge <$> Gen.element [0, 0, 0, -1, -1, 1, 1, -2, 2300, -2300]),
    (1, GasChoice.ample <$> Gen.nat (.linear 0 30000))]

/-- A run: the fork, the message and the state before it. -/
structure Scenario where
  fork : Fork × String
  create : Bool
  static : Bool
  gas : GasChoice
  value : Nat
  data : ByteArray
  program : Program
  callees : List Program
  delegate : Nat
  slots : List (Nat × Nat)
  /-- The nonce of the account that runs the program. -/
  nonce : Nat
  /-- Whether the numbers of the block are near the top of their types. -/
  big : Bool

instance : Repr Scenario where
  reprPrec s _ := s!"fork={s.fork.2} ({s.fork.1.name}) create={s.create} static={s.static} \
    gas={reprStr s.gas} value={s.value} data={hex s.data} nonce={s.nonce} big={s.big}\n  \
    code={hex s.program.code}\n  program={reprStr s.program.snips}\n  \
    callees={s.callees.map fun c => hex c.code} delegate={hexNat s.delegate} slots={s.slots}"

/-- The accounts of a scenario: the caller, the target with the program, and what it may call.

The third callee holds a delegation designator of EIP-7702.

The fourth exists and is empty, which no rule of the state forbids before a transaction ends. -/
def Scenario.accounts (s : Scenario) : List PreAccount :=
  let designator : ByteArray :=
    ⟨(([0xef, 0x01, 0x00] : List UInt8) ++ beBytes 20 s.delegate).toArray⟩
  let callee (i : Nat) : ByteArray := (s.callees[i]?.map (·.code)).getD .empty
  [⟨callerAddress, 0, 10 ^ 18, .empty, []⟩,
   ⟨targetAddress, if s.create then 0 else s.nonce, if s.create then 0 else 1000,
     if s.create then .empty else s.program.code, if s.create then [] else s.slots⟩,
   ⟨addressOf 0xa1 0xa1, 1, 7, callee 0, [(0, 1)]⟩,
   ⟨addressOf 0xa2 0xa2, 0, 0, callee 1, []⟩,
   ⟨addressOf 0xa3 0xa3, 1, 1, designator, []⟩,
   ⟨addressOf 0xe0 0xe0, 0, 0, .empty, []⟩]

/-- A scenario at a fork: mostly a call with enough gas, and programs for that fork. -/
def genScenarioAt (fork : Fork × String) (most : Nat := 120) : Gen Scenario := do
  let create ← Gen.frequency [(6, pure false), (1, pure true)]
  let static ← Gen.frequency [(9, pure false), (1, pure true)]
  let gas ← genRunGas
  let value ← Gen.frequency [(3, pure 0), (1, Gen.nat (.linear 1 100))]
  let data ← genBytes (.linear 0 70)
  let program ← genParts fork.1 most
  let callees ← Gen.list (.constant 2 2) (genParts fork.1 12 3 4 (some 30000))
  let delegate ← Gen.frequency [
    (4, addressNat <$> Gen.element (auxAddresses ++ [targetAddress])),
    (2, Gen.element [1, 2, 4, 9, 0x100, 0])]
  -- Each of the four slots that a program writes starts at 0, 1 or 2.
  let slots ← (fun words => (List.range 4).zip words) <$>
    Gen.list (.singleton 4) (Gen.nat (.constant 0 2))
  -- A nonce at the limit of EIP-2681 lets one creation run, or none.
  let nonce ← Gen.frequency [(12, pure 1), (1, Gen.element [2 ^ 64 - 2, 2 ^ 64 - 1])]
  let big ← Gen.frequency [(3, pure false), (1, pure true)]
  -- No message is static before STATICCALL exists.
  pure ⟨fork, create, static && !create && fork.1 ≥ .byzantium, gas, value, data, program, callees,
    delegate, slots, nonce, big⟩

/-- A scenario of accounts that destroy themselves, at any fork that the reference has.

The program and what it calls end by SELFDESTRUCT, and the program calls them more than once. -/
def genDestroyScenario : Gen Scenario := do
  let fork ← Gen.element forks
  let s ← genScenarioAt fork 0
  let program ← genDestroyer fork.1
  let callees ← Gen.list (.constant 2 2) (genDestroyer fork.1 3)
  let value ← Gen.frequency [(1, pure 0), (1, Gen.nat (.linear 1 100))]
  pure { s with program, callees, value, gas := .ample ampleGas, static := false, nonce := 1 }

/-- A scenario at any fork that the reference has, each as often as another. -/
def genScenario : Gen Scenario := do
  genScenarioAt (← Gen.element forks)

/-- The gas of a scenario, once a run of EthLib with ample gas says what the program uses.

The run only places the draw: the reference decides what that gas buys. -/
def Scenario.gasOf (s : Scenario) (run : Nat → Option Nat) : Nat :=
  match s.gas with
  | .ample gas => gas
  | .part percent => ((run ampleGas).map fun left => (ampleGas - left) * percent / 100).getD 0
  | .edge delta => ((run ampleGas).map fun left => ((ampleGas - left : Nat) + delta).toNat).getD 0

/-- The class of a choice of gas, for the shares of a report. -/
def GasChoice.name : GasChoice → String
  | .ample gas => if gas ≤ 30000 then "gas: little" else "gas: ample"
  | .part _ => "gas: a part of what the run uses"
  | .edge 0 => "gas: exactly what the run uses"
  | .edge delta => if delta < 0 then "gas: less than the run uses, by 1, 2 or 2300"
      else "gas: more than the run uses, by 1 or 2300"

/-- The fields of two results agree, and the report names the first that does not. -/
def sameFields (names : List String) (got want : String) : TestT IO Unit := do
  let gots := got.splitOn " "
  let wants := want.splitOn " "
  if gots.length ≠ names.length || wants.length ≠ names.length then got === want
  else
    for (name, g, w) in names.zip (gots.zip wants) do
      if g ≠ w then
        annotate s!"{name} differs"
        if name = "state" then
          for (a, b) in (g.splitOn ";").zip (w.splitOn ";") do
            if a ≠ b then a === b
        g === w

/-- The fields of a result of a fork with a release of the reference. -/
def fieldNames : List String := ["status", "gas left", "output", "refund", "logs",
  "accounts to delete", "touched accounts", "state", "transient storage"]

/-- The answer of the oracle to a run: what the run left, and the name of its error. -/
def splitAnswer (answer : String) : String × String :=
  match answer.splitOn "\t" with
  | [want, error] => (want, error)
  | _ => (answer, "")

/-- The minimums of the classes of a whole program, in percent of the cases.

They are about a third of the shares of a run of 1,000 cases, and a short run asks for none. -/
def coverWhole {m : Type → Type} [Monad m] (asked : Bool) (trace : Trace) (error : Option EvmError)
    (output : ByteArray) (refund : Int) (logs : Nat) : TestT m Unit := do
  let least (percent : Nat) : Nat := if asked then percent else 0
  let halts (name : String) : Bool := trace.halts.any (·.2 = name)
  let call (result : String) : Bool := trace.calls.any (·.2 = result)
  cover (least 15) "the first frame runs over 20 steps" (trace.topSteps > 20)
  cover (least 10) "it returns data" (error.isNone ∧ !output.isEmpty)
  cover (least 1) "it reverts" (error == some .revert)
  cover (least 3) "out of gas" (halts "out of gas")
  cover (least 1) "stack underflow" (halts "stack underflow")
  cover (least 1) "stack overflow" (halts "stack overflow")
  cover (least 1) "invalid jump" (halts "invalid jump")
  cover (least 1) "invalid opcode" (halts "invalid opcode")
  cover (least 1) "static violation" (halts "static violation")
  cover (least 1) "a call succeeds" (call "succeeds")
  cover (least 1) "a call halts" (call "halts")
  cover (least 1) "a call reverts" (call "reverts")
  cover (least 1) "a call runs no message" (call "runs no message")
  cover (least 5) "memory grows" trace.memoryGrew
  cover (least 3) "a log" (logs > 0)
  cover (least 3) "a refund" (refund > 0)
  cover (least 3) "a frame at depth 2 or more" (trace.depth ≥ 2)

/-- A message leaves in EthLib what it leaves in the reference.

This covers the status, the gas left, the output, the refund, the logs and the accounts to delete.

It also covers each account with its nonce, its balance, its code and its storage.

`asked` requires the minimum share of each class, which a run of 500 cases or more can reach. -/
def wholeProgram (oracle : Oracle) (counts : IO.Ref OpCounts) (asked : Bool)
    (destroys : Bool := false) : Property IO := propertyM do
  let s ← forAll (if destroys then genDestroyScenario else genScenario)
  pure do
    let code := s.program.code
    let accounts := s.accounts
    let run (gas : Nat) : Option Nat :=
      (traceMessage s.fork.1 s.create s.static gas s.value s.data code accounts s.big).2.map
        (·.gas)
    let gas := s.gasOf run
    annotate s!"gas {gas}"
    let (got, error) :=
      runEthLib s.fork.1 s.create s.static gas s.value s.data code accounts s.big
    let answer ← oracle.ask
      (runCommand s.fork.2 s.create s.static gas s.value s.data code accounts s.big)
    let (want, wantError) := splitAnswer answer
    annotate s!"EthLib's error: {error}; the reference's: {wantError}"
    sameFields fieldNames got want
    let (trace, ended) :=
      traceMessage s.fork.1 s.create s.static gas s.value s.data code accounts s.big
    -- The table of opcodes is of the programs of any snippets.
    if !destroys then evalIO (counts.modify (·.add s.fork.1.name trace))
    label (if s.create then "a creation" else if s.static then "a static call" else "a call")
    label s.gas.name
    classify "a block with numbers near the top of their types" s.big
    match ended with
    | some evm =>
      -- The frame that the observer saw end is the frame that was compared.
      showResult accounts evm === got
      labelTrace trace evm.error evm.output evm.substate.refundCounter evm.substate.logs.size
      if destroys then
        let least (percent : Nat) : Nat := if asked then percent else 0
        let fork := s.fork.1
        label (if fork < .tangerineWhistle then "before Tangerine Whistle"
          else if fork < .spuriousDragon then "Tangerine Whistle" else if fork < .london then
          "Spurious Dragon to Berlin" else if fork < .dencun then "London to Shapella"
          else "Dencun and later")
        cover (least 20) "SELFDESTRUCT runs" (trace.ran[0xff]! > 0)
        cover (least 5) "SELFDESTRUCT runs twice or more" (trace.ran[0xff]! > 1)
        cover (least 10) "an account to delete at the end" (!evm.substate.accountsToDelete.isEmpty)
        cover (least 3) "the refund of SELFDESTRUCT, before London"
          (fork < .london ∧ evm.substate.refundCounter ≥ 24000)
        cover (least 3) "SELFDESTRUCT in a creation" (trace.calls.any fun (op, _) =>
          op = 0xf0 ∨ op = 0xf5)
      else
        coverWhole asked trace evm.error evm.output evm.substate.refundCounter
          evm.substate.logs.size
    | none => label "ends: aborts"

/-- The fields of a result of Glamsterdam. -/
def glamsterdamNames : List String := ["status", "gas left", "state gas left", "output", "refund",
  "logs", "accounts to delete", "state", "account reads", "storage reads", "transient storage"]

/-- A call at Glamsterdam leaves what the branch `forks/amsterdam` of the reference leaves.

This covers the status, the gas left, the state gas left of EIP-8037, the output and the refund.

It also covers the logs with the transfer logs of EIP-7708, the accounts to delete and the state. -/
def glamsterdam (oracle : Oracle) (counts : IO.Ref OpCounts) (asked : Bool) : Property IO :=
  propertyM do
  let s ← forAll ((fun s => { s with create := false }) <$>
    genScenarioAt (.glamsterdam, "amsterdam"))
  let reservoir ← forAll (Gen.frequency [(2, pure 0), (2, Gen.nat (.linear 0 400000)),
    (1, Gen.element [97920, 97919, 183600, 183599])])
  pure do
    let code := s.program.code
    let accounts := s.accounts
    let run (gas : Nat) : Option Nat :=
      (traceGlamsterdam s.static gas reservoir s.value s.data code accounts).2.map
        (·.gas.gasLeft)
    let gas := s.gasOf run
    annotate s!"gas {gas}"
    let (got, error) := runGlamsterdam s.static gas reservoir s.value s.data code accounts
    let answer ← oracle.ask ["run", if s.static then "1" else "0", toString gas,
      toString reservoir, toString s.value, hex s.data, hex code,
      ";".intercalate (accounts.map (·.show))]
    let (want, wantError) := splitAnswer answer
    annotate s!"EthLib's error: {error}; the reference's: {wantError}"
    sameFields glamsterdamNames got want
    let (trace, ended) := traceGlamsterdam s.static gas reservoir s.value s.data code accounts
    evalIO (counts.modify (·.add "glamsterdam" trace))
    label (if s.static then "a static call" else "a call")
    label s.gas.name
    label (if reservoir = 0 then "no reservoir" else "a reservoir")
    match ended with
    | some evm =>
      labelTrace trace evm.error evm.output evm.substate.refundCounter evm.substate.logs.size
      coverWhole asked trace evm.error evm.output evm.substate.refundCounter
        evm.substate.logs.size
      let least (percent : Nat) : Nat := if asked then percent else 0
      cover (least 2) "state gas is spent from the reservoir" (evm.gas.reservoir < reservoir)
      cover (least 3) "state gas is spent from the gas left"
        (reservoir = 0 ∧ trace.sstores.any (· = "SSTORE sets a clean zero slot"))
      classify "the reservoir ends empty, from one that was not"
        (reservoir > 0 ∧ evm.gas.reservoir = 0)
    | none => label "ends: aborts"

/-- FINDING: a frame that runs DELEGATECALL or STATICCALL records a read of its own account.

The reference reads the balance of the running account only for CALL and CALLCODE, which send value.

The frame here is alone, so the account is in the reads for no other reason. -/
def delegatecallReads (oracle : Oracle) : Property IO := propertyM do
  let call ← forAll (Gen.element [(0xf4 : UInt8), 0xfa])
  pure do
    let callee := addressNat (addressOf 0xa1 0xa1)
    let code := assemble [Snip.ofBytes "call" (pushes [0, callee, 0, 0, 0, 0] ++ [call])]
    let accounts : List PreAccount := [⟨callerAddress, 0, 10 ^ 18, .empty, []⟩,
      ⟨targetAddress, 1, 1000, code, []⟩, ⟨addressOf 0xa1 0xa1, 1, 7, .empty, []⟩]
    let message := messageOf .glamsterdam false false 100000 0 .empty code
    let got := match processMessage (Meter := StateGasMeter) .glamsterdam message
        (txState accounts) startSubstate with
      | .error e => s!"abort {reprStr e}"
      | .ok ⟨evm, _⟩ => ",".intercalate (evm.state.accountReads.toList.map hexVec)
    let want ← oracle.ask ["reads", "0", "100000", "0", "0", "-", hex code,
      ";".intercalate (accounts.map (·.show))]
    got === want

/-- A program that calls itself with all its gas, so the depth of calls reaches its limit.

Each level may first count itself in storage, and keeps the result of its call in memory. -/
def genRecursion (fork : Fork) : Gen (List UInt8) := do
  let call ← Gen.element ([0xf1, 0xf2, 0xf4, 0xfa].filter (hasOp fork))
  let count ← Gen.bool
  let value ← Gen.frequency [(3, pure 0), (1, pure 1)]
  let counter : List UInt8 := if count then [0x60, 0, 0x54, 0x60, 1, 0x01, 0x60, 0, 0x55] else []
  let args := [0, 0, 0, 0] ++ (if call = 0xf1 || call = 0xf2 then [value] else [])
  -- The operands of the call, the gas on top: all the gas but 1000, to this account.
  --
  -- Before EIP-150 a call that asks for all the gas halts, since it cannot also pay its price.
  pure (counter ++ args.flatMap (fun (a : Nat) => [0x60, UInt8.ofNat a]) ++
    [0x30, 0x5a, 0x61, 0x03, 0xe8, 0x90, 0x03, call, 0x60, 0, 0x52, 0x59, 0x60, 0x00, 0xf3])

/-- A program that pushes words until the stack is full, in a loop or in a line. -/
def genDeepStack : Gen (List UInt8) := do
  let pusher ← Gen.element [[0x60, 1], [0x30], [0x58], [0x5a], [0x59], [0x80], [0x8f]]
  let line ← Gen.bool
  let count ← Gen.element [1021, 1022, 1023, 1024, 1025]
  let seed ← Gen.element [[], [0x60, 7], [0x60, 7, 0x60, 8]]
  -- The line ends with STOP, which a full stack allows.
  if line then pure (seed ++ (List.replicate count pusher).flatten ++ [0x00])
  else pure (seed ++ [0x5b] ++ pusher ++ [0x60, UInt8.ofNat seed.length, 0x56])

/-- A message that fills the stack or the depth of calls leaves what the reference leaves.

The limits are 1024 items and 1024 frames, and a random program reaches neither. -/
def deepLimits (oracle : Oracle) (asked : Bool) : Property IO := propertyM do
  let fork ← forAllWith (·.2) (Gen.element forks)
  let deepCalls ← forAll Gen.bool
  let program ← forAllWith (fun bytes => hex ⟨bytes.toArray⟩)
    (if deepCalls then genRecursion fork.1 else genDeepStack)
  -- All but one 64th of the gas goes down from Tangerine Whistle, so depth 1024 needs a lot.
  let gas ← forAll (if deepCalls then
      Gen.frequency [(1, Gen.nat (.linear 100000 3000000)), (3, Gen.element [10 ^ 12, 10 ^ 14])]
    else Gen.frequency [(2, Gen.nat (.linear 0 40000)), (1, pure 1000000)])
  pure do
    let code : ByteArray := ⟨program.toArray⟩
    let accounts : List PreAccount := [⟨callerAddress, 0, 10 ^ 18, .empty, []⟩,
      ⟨targetAddress, 1, 1000, code, []⟩]
    let (got, error) := runEthLib fork.1 false false gas 0 .empty code accounts
    let answer ← oracle.ask (runCommand fork.2 false false gas 0 .empty code accounts)
    let (want, wantError) := splitAnswer answer
    annotate s!"EthLib's error: {error}; the reference's: {wantError}"
    sameFields fieldNames got want
    let (trace, ended) := traceMessage fork.1 false false gas 0 .empty code accounts
    label (if deepCalls then "calls itself" else "fills the stack")
    label (if trace.depth = 1024 then "reaches depth 1024" else if trace.depth ≥ 100 then
      "reaches depth 100 to 1023" else if trace.depth ≥ 1 then "reaches depth 1 to 99"
      else "stays in the first frame")
    for (depth, name) in trace.halts.toList.eraseDups do
      label s!"{if depth = 0 then "the first frame" else "a deeper frame"} halts: {name}"
    for (op, result) in trace.calls.toList.eraseDups do
      label s!"{opName op} {result}"
    let least (percent : Nat) : Nat := if asked then percent else 0
    cover (least 3) "a call at depth 1024 runs no message"
      (trace.depth = 1024 ∧ trace.calls.any (·.2 = "runs no message"))
    cover (least 5) "the stack overflows" (trace.halts.any (·.2 = "stack overflow"))
    cover (least 3) "a stack of 1021 to 1024 words, and the frame ends well"
      (!deepCalls ∧ (ended.map (·.error.isNone)).getD false)

/-- Print the share of the programs of each fork that ran each opcode the fork has.

The summary names the cells with no program, and `full` prints every cell.

A cell is a share in percent, or without `percent` the number of programs, at most 999. -/
def printOpCounts (title : String) (counts : OpCounts) (full : Bool) (percent : Bool := true) :
    IO Unit := do
  if counts.programs.isEmpty then return
  let names := (forks.map (·.1)).eraseDups ++ [.glamsterdam]
  let mut never : Array String := #[]
  let mut least : Nat × String := (1000, "")
  if full then
    IO.println s!"opcodes of {title}, in {if percent then "percent" else "number"} of the \
      programs of each fork"
    IO.println ("opcode        " ++ " ".intercalate (names.map fun f => (f.name.take 4).toString))
  for byte in (List.range 256).map UInt8.ofNat do
    if (Op.decode byte).isNone then continue
    let mut row := (opName byte).pushn ' ' (14 - (opName byte).length)
    for fork in names do
      let programs := counts.programs.getD fork.name 0
      if !hasOp fork byte || programs = 0 then row := row ++ "   . "
      else
        let ran := counts.ran.getD (fork.name, byte) 0
        let share := if percent then 100 * ran / programs else min ran 999
        row := row ++ s!"{if share < 10 then "  " else if share < 100 then " " else ""}{share}  "
        if share = 0 then never := never.push s!"{opName byte} at {fork.name}"
        if share < least.1 then least := (share, s!"{opName byte} at {fork.name}")
    if full then IO.println row
  let programs := counts.programs.fold (init := 0) fun sum _ n => sum + n
  let unit := if percent then "%" else " runs"
  IO.println s!"opcodes of {title}: {programs} programs at {counts.programs.size} forks; the \
    least share is {least.1}{unit} ({least.2}); {never.size} opcodes of a fork ran in no program"
  if !never.isEmpty then IO.println s!"  never: {", ".intercalate (never.toList.take 40)}"

end EvmProperty

import Property.Evm.Program

/-!
# One frame, stepped

Two state machine tests drive one frame of EthLib through straight-line code.

- `storageMachine` is a `StateMachine`.
  Its model is the gas and the refund of SLOAD and SSTORE, with no reference process.
  The model is written from the EIPs (EIP-150, EIP-1884, EIP-2200, EIP-2929, EIP-3529).
- `frameScenario` is a scenario of `Command`s, one type per family of instructions.
  It runs in madhouse mode against a frame that the Python execution-specs step in the oracle.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Evm

namespace EvmProperty

/-- The accounts of a stepped frame, those of `Frame` in `oracle/evm.py`. -/
def frameAccounts : List PreAccount := [
  ⟨callerAddress, 0, 10 ^ 18, .empty, []⟩, ⟨targetAddress, 1, 10 ^ 9, .empty, [(1, 1)]⟩]

/-- A frame at its start, with gas, over the accounts above. -/
def newFrame (fork : Fork) (gas : Nat) (static : Bool) : Evm fork Nat :=
  let data : ByteArray := ⟨(List.replicate 40 (0xaa : UInt8)).toArray⟩
  startFrame (messageOf fork false static gas 5 data .empty) (txState frameAccounts)
    startSubstate gas

/-- Run code in a frame from its first byte, to its end or to a stop, in at most 100 steps.

An error leaves the frame as it was, so a sequence goes on after a refused instruction. -/
def runCode {fork : Fork} (evm : Evm fork Nat) (code : ByteArray) :
    Except EvmError (Evm fork Nat) :=
  let rec go (fuel : Nat) (evm : Evm fork Nat) : Except EvmError (Evm fork Nat) :=
    match fuel with
    | 0 => .ok evm
    | fuel + 1 =>
      if evm.running && evm.pc < code.size then
        match step fork evm with
        | .ok (.next after) =>
          -- An instruction that keeps its reads gives its halt as a frame.
          match after.error with
          | some e => .error e
          | none => go fuel after
        | .ok (.child ..) => .error (.unspecifiedOpcode 0)
        | .error e => .error e
      else .ok evm
  go 100 { evm with code, pc := 0, validJumpDestinations := validJumpDestinations code }

/-! ## SLOAD and SSTORE against a model of the EIPs -/

/-- A slot as the model sees it. -/
structure Slot where
  original : Nat
  current : Nat
  warm : Bool
  deriving Repr, BEq, Inhabited

/-- The model: the fork, four slots, the gas left and the refund. -/
structure StorageModel where
  fork : Fork
  slots : List Slot
  gas : Nat
  refund : Int
  /-- Whether the last transition ran out of gas, which leaves the model as it was. -/
  refused : Bool

instance : Repr StorageModel where
  reprPrec m _ := s!"{m.fork.name} gas={m.gas} refund={m.refund} slots={reprStr m.slots}"

inductive StorageStep where
  | sload (key : Nat)
  | sstore (key value : Nat)
  deriving Repr, BEq

/-- The price of SLOAD: EIP-150 raises 50 to 200, EIP-1884 to 800, and EIP-2929 splits it. -/
def sloadPrice (fork : Fork) (warm : Bool) : Nat :=
  if fork ≥ .berlin then (if warm then 100 else 2100)
  else if fork ≥ .istanbul then 800
  else if fork ≥ .tangerineWhistle then 200
  else 50

/-- The price and the refund of SSTORE, or none when EIP-2200 refuses it at 2300 gas or less. -/
def sstorePrice (fork : Fork) (slot : Slot) (value gas : Nat) : Option (Nat × Int) :=
  let (original, current) := (slot.original, slot.current)
  if fork < .istanbul then
    -- The Yellow Paper: 20000 to set a zero slot, else 5000, and 15000 back for a clear.
    some (if current = 0 ∧ value ≠ 0 then 20000 else 5000,
      if current ≠ 0 ∧ value = 0 then 15000 else 0)
  else if gas ≤ 2300 then none
  else
    let berlin := fork ≥ .berlin
    -- EIP-2929 makes SLOAD_GAS 100 and takes the cold price out of SSTORE_RESET_GAS.
    let sloadGas := if berlin then 100 else 800
    let reset := if berlin then 5000 - 2100 else 5000
    -- EIP-3529 lowers the refund of a clear to SSTORE_RESET_GAS + ACCESS_LIST_STORAGE_KEY_COST.
    let clear : Int := if fork ≥ .london then 4800 else 15000
    let cold : Nat := if berlin ∧ !slot.warm then 2100 else 0
    let price : Nat :=
      if current = value then sloadGas
      else if original = current then (if original = 0 then 20000 else reset)
      else sloadGas
    let refund : Int :=
      if current = value then 0
      else if original = current then (if original ≠ 0 ∧ value = 0 then clear else 0)
      else
        (if original ≠ 0 then
          (if current = 0 then -clear else 0) + (if value = 0 then clear else 0)
        else 0) +
        (if original = value then
          (if original = 0 then (20000 : Int) - sloadGas else (reset : Int) - sloadGas)
        else 0)
    some (price + cold, refund)

/-- The model after a step: the push of each operand costs 3. -/
def StorageModel.apply (m : StorageModel) : StorageStep → StorageModel
  | .sload key =>
    let slot := m.slots[key]!
    let price := 3 + sloadPrice m.fork slot.warm
    if m.gas < price then { m with refused := true }
    else { m with gas := m.gas - price, slots := m.slots.set key { slot with warm := true },
                  refused := false }
  | .sstore key value =>
    let slot := m.slots[key]!
    match sstorePrice m.fork slot value (m.gas - 6) with
    | none => { m with refused := true }
    | some (price, refund) =>
      if m.gas < 6 + price then { m with refused := true }
      else { m with gas := m.gas - 6 - price, refund := m.refund + refund, refused := false
                    slots := m.slots.set key { slot with current := value, warm := true } }

/-- The storage of the frame before the model starts: slot `i` holds its original word. -/
def storageFrame (m : StorageModel) : Evm m.fork Nat :=
  let accounts := [⟨callerAddress, 0, 10 ^ 18, .empty, []⟩,
    ⟨targetAddress, 1, 10 ^ 9, .empty, (m.slots.zipIdx.map fun (slot, i) => (i, slot.original))⟩]
  startFrame (messageOf m.fork false false m.gas 0 .empty .empty) (txState accounts)
    startSubstate m.gas

/-- The system under test: the frame, and the word the last SLOAD pushed. -/
structure StorageSut (fork : Fork) where
  evm : Evm fork Nat
  refused : Bool

/-- A model at its start: any fork, four slots with small words, and gas. -/
def genStorageModel : Gen StorageModel := do
  let fork ← Gen.element (forks.map (·.1))
  let slots ← Gen.list (.singleton 4) ((fun n => Slot.mk n n false) <$> Gen.nat (.constant 0 2))
  -- Little gas now and then, so the stipend rule of EIP-2200 and out of gas are reached.
  let gas ← Gen.frequency [(3, pure 1000000), (2, Gen.nat (.linear 0 60000))]
  pure ⟨fork, slots, gas, 0, false⟩

/-- The model of storage: SSTORE three times in four, on a key and a word that repeat. -/
def storageModel : Model StorageModel StorageStep where
  initState := genStorageModel
  transitions _ := Gen.frequency [
    (1, StorageStep.sload <$> Gen.nat (.constant 0 3)),
    (3, Gen.zipWith StorageStep.sstore (Gen.nat (.constant 0 3)) (Gen.nat (.constant 0 2)))]
  apply := StorageModel.apply

/-- SLOAD and SSTORE charge and refund what the EIPs say, over any sequence on four slots.

The model is the text of EIP-2200, EIP-2929 and EIP-3529, and of the Yellow Paper before them.

After each step the gas left, the refund counter and the four words are the model's. -/
def storageMachine : StateMachine StorageModel StorageStep (Σ fork, StorageSut fork) IO where
  toModel := storageModel
  initSut m := pure ⟨m.fork, storageFrame m, false⟩
  applySut sut _ t := do
    let ⟨fork, sut⟩ := sut
    let code : ByteArray := match t with
      | .sload key => ⟨#[0x60, UInt8.ofNat key, 0x54]⟩
      | .sstore key value => ⟨#[0x60, UInt8.ofNat value, 0x60, UInt8.ofNat key, 0x55]⟩
    match runCode sut.evm code with
    | .error .outOfGas => pure ⟨fork, { sut with refused := true }⟩
    | .error e => failWith s!"the frame fails with {reprStr e}"
    | .ok evm =>
      match t, evm.stack.val with
      | .sload key, word :: _ =>
        word.toNat === (evm.state.getStorage targetAddress (word32 key)).toNat
      | _, _ => pure ()
      pure ⟨fork, ⟨{ evm with stack := .empty }, false⟩⟩
  invariants sut m := do
    let ⟨_, sut⟩ := sut
    annotate s!"model: {reprStr m} refused={m.refused}"
    sut.refused === m.refused
    sut.evm.gas === m.gas
    sut.evm.substate.refundCounter === m.refund
    (List.range 4).map (fun i => (sut.evm.state.getStorage targetAddress (word32 i)).toNat)
      === m.slots.map (·.current)

/-! ## DUPN, SWAPN and EXCHANGE of EIP-8024 against a list -/

/-- The model: the stack as a list, its top first, and the gas left. -/
structure DeepStack where
  stack : List Nat
  gas : Nat
  refused : Bool

instance : Repr DeepStack where
  reprPrec m _ := s!"depth={m.stack.length} gas={m.gas} refused={m.refused} top={m.stack.take 3}"

inductive DeepStep where
  | push (value : Nat)
  | dupn (immediate : UInt8)
  | swapn (immediate : UInt8)
  | exchange (immediate : UInt8)
  deriving Repr, BEq

/-- `decode_single` of EIP-8024: the bytes from 91 to 127 encode nothing. -/
def decodeSingleModel (x : Nat) : Option Nat :=
  if x ≤ 90 ∨ 128 ≤ x then some ((x + 145) % 256) else none

/-- `decode_pair` of EIP-8024: the bytes from 82 to 127 encode nothing. -/
def decodePairModel (x : Nat) : Option (Nat × Nat) :=
  if x ≤ 81 ∨ 128 ≤ x then
    let k := Nat.xor x 143
    let (q, r) := (k / 16, k % 16)
    some (if q < r then (q + 1, r + 1) else (r + 1, 29 - q))
  else none

/-- A list with the items at two positions exchanged. -/
def swapAt (xs : List Nat) (i j : Nat) : List Nat :=
  (xs.set i (xs.getD j 0)).set j (xs.getD i 0)

/-- The model after a step: each instruction costs 3, and a refused one changes nothing. -/
def DeepStack.apply (m : DeepStack) (t : DeepStep) : DeepStack :=
  let after : Option (List Nat) := match t with
    | .push value => if m.stack.length < 1024 then some (value :: m.stack) else none
    | .dupn x => (decodeSingleModel x.toNat).bind fun n =>
        if n ≤ m.stack.length ∧ m.stack.length < 1024 then some (m.stack.getD (n - 1) 0 :: m.stack)
        else none
    | .swapn x => (decodeSingleModel x.toNat).bind fun n =>
        if n + 1 ≤ m.stack.length then some (swapAt m.stack 0 n) else none
    | .exchange x => (decodePairModel x.toNat).bind fun (n, k) =>
        if k + 1 ≤ m.stack.length then some (swapAt m.stack n k) else none
  match after with
  | some stack => if m.gas < 3 then { m with refused := true }
      else ⟨stack, m.gas - 3, false⟩
  | none => { m with refused := true }

/-- An immediate byte: the edges of the ranges that encode nothing, JUMPDEST, or any byte. -/
def genImmediate : Gen UInt8 :=
  Gen.frequency [(3, Gen.element [0, 80, 81, 82, 90, 91, 0x5b, 127, 128, 143, 255]), (4, genByte)]

/-- The model of a deep stack: it starts at a depth where a decoded index just fits or not. -/
def deepStackModel : Model DeepStack DeepStep where
  initState := do
    let stack ← Gen.frequency [(1, Gen.list (.linear 0 40) (Gen.nat (.constant 0 9))),
      (2, (fun n => (List.range n).map (· + 1)) <$> Gen.element [16, 17, 18, 29, 30, 31, 144, 145,
        234, 235, 236, 237, 1023, 1024])]
    pure ⟨stack, 1000, false⟩
  transitions _ := Gen.frequency [
    (1, DeepStep.push <$> Gen.nat (.constant 0 255)), (3, DeepStep.dupn <$> genImmediate),
    (3, DeepStep.swapn <$> genImmediate), (3, DeepStep.exchange <$> genImmediate)]
  apply := DeepStack.apply

/-- The code of a step. -/
def DeepStep.code : DeepStep → ByteArray
  | .push value => ⟨#[0x60, UInt8.ofNat value]⟩
  | .dupn x => ⟨#[0xe6, x]⟩
  | .swapn x => ⟨#[0xe7, x]⟩
  | .exchange x => ⟨#[0xe8, x]⟩

/-- DUPN, SWAPN and EXCHANGE of Glamsterdam move the stack as EIP-8024 says, over any sequence.

The model is a list and the two decoders of the EIP.

An immediate byte that encodes nothing, a stack too short and a full stack refuse the step. -/
def deepStackMachine : StateMachine DeepStack DeepStep (Evm .glamsterdam Nat × Bool) IO where
  toModel := deepStackModel
  initSut m := do
    let frame := newFrame .glamsterdam m.gas false
    let stack := m.stack.reverse.foldl (init := frame.stack) fun stack word =>
      match stack.push (BitVec.ofNat 256 word) with
      | .ok next => next
      | .error _ => stack
    pure ({ frame with stack }, false)
  applySut sut _ t := do
    match runCode sut.1 t.code with
    | .error e =>
      annotate s!"EthLib refuses with {reprStr e}"
      pure (sut.1, true)
    | .ok evm =>
      evm.pc === 2
      pure (evm, false)
  invariants sut m := do
    annotate s!"model: {reprStr m}"
    sut.2 === m.refused
    sut.1.gas === m.gas
    sut.1.stack.val.map (·.toNat) === m.stack

/-! ## A frame beside the reference, one family of instructions per command -/

/-- The state of a scenario: the frame of EthLib, once the first command started it. -/
structure FrameState where
  frame : Option (Σ fork, Evm fork Nat) := none
  /-- The depth of the stack as a generator can tell it before any command runs.

  `Command.next` moves it and `Command.buildIn` reads it.

  A command that the frame refuses leaves the stack as it was.

  So this depth may be more than the true depth.

  `check` has the last word. -/
  depth : Nat := 0
  deriving Inhabited

/-- The frame of a state at a fork, or none before the first command. -/
def FrameState.evm (s : FrameState) (fork : Fork) : Option (Evm fork Nat) :=
  match s.frame with
  | some ⟨held, evm⟩ => if h : held = fork then some (h ▸ evm) else none
  | none => none

/-- What commands are built from: the fork under its two names, and the oracle. -/
structure FrameContext where
  fork : Fork × String
  oracle : Oracle
  gas : Nat
  /-- The share of sequences, in percent, in which a DUP or a SWAP must run.

  A run of few sequences stays at small sizes, where sequences are short and the share is low.

  So a short run asks for none. -/
  minimum : Nat := 0

/-- What a frame shows after code ran, in the text form of the oracle. -/
def showFrame {fork : Fork} (evm : Evm fork Nat) : String :=
  let stack := evm.stack.val.map fun w => hexNat w.toNat
  " ".intercalate ["ok", toString evm.gas, toString evm.pc, toString evm.memory.size,
    hexVec (Cryptography.Hash.Keccak.keccak256 evm.memory),
    if stack.isEmpty then "-" else ",".intercalate stack,
    toString evm.substate.refundCounter, showLogs evm.substate.logs,
    if evm.running then "1" else "0", hex evm.output]

/-- Run code in the frame of EthLib and in the frame of the reference, and compare what they show.

The frames start on the first command.  A refused code leaves both frames as they were. -/
def stepBoth (ctx : FrameContext) (code : ByteArray) (s : FrameState) : TestT IO FrameState := do
  let evm ← match s.evm ctx.fork.1 with
    | some evm => pure evm
    | none => do
      let _ ← ctx.oracle.ask ["frame", ctx.fork.2, toString ctx.gas, "0"]
      pure (newFrame ctx.fork.1 ctx.gas false)
  let answer ← ctx.oracle.ask ["op", hex code]
  annotate s!"code {hex code}: the reference says {answer}"
  match runCode evm code with
  | .error e =>
    annotate s!"EthLib fails with {reprStr e}"
    (if e == .revert then "revert" else "halt") === (answer.splitOn " ").head!
    pure { s with frame := some ⟨_, evm⟩ }
  | .ok after =>
    showFrame after === answer
    pure { s with frame := some ⟨_, { after with running := true }⟩ }

/-- The code of an instruction after pushes of its operands. -/
def opCode (byte : UInt8) (args : List Nat) : ByteArray :=
  ⟨(args.reverse.flatMap pushBytes ++ [byte]).toArray⟩

/-- A command: its family, and the code it runs. -/
structure FrameCommand (family : String) where
  ctx : FrameContext
  name : String
  code : ByteArray

/-- A command of a family, from the instructions of that family that the fork may have. -/
def buildFrameCommand (family : String) (bytes : List UInt8) (ctx : FrameContext) :
    Gen (FrameCommand family) := do
  let table := instructions ++ nullary.map fun byte => (byte, [])
  let (byte, kinds) ← Gen.element (table.filter fun (byte, _) => bytes.contains byte)
  let args ← Gen.sequence (kinds.map genOperand)
  pure ⟨ctx, s!"{family} {hexNat byte.toNat} {args.map hexNat}", opCode byte args⟩

/-- The families of instructions, each a type of command. -/
def families : List (String × List UInt8) := [
  ("ARITHMETIC", [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b]),
  ("BITWISE", [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d,
    0x1e]),
  ("MEMORY", [0x20, 0x35, 0x37, 0x39, 0x3e, 0x51, 0x52, 0x53, 0x59, 0x5e]),
  ("STORAGE", [0x54, 0x55, 0x5c, 0x5d]),
  ("ENVIRONMENT", nullary ++ [0x31, 0x3b, 0x3c, 0x3f, 0x40, 0x49]),
  ("LOG", [0xa0, 0xa1, 0xa2, 0xa3, 0xa4]),
  ("STACK", [0x50]),
  ("END", [0xf3, 0xfd])]

/-- The bytes of a family. -/
def familyBytes (family : String) : List UInt8 :=
  ((families.find? fun (name, _) => name = family).map (·.2)).getD []

/-- The instructions that leave one word more than their operands took: the others leave none.

A command pushes the operands of its instruction itself, so this is what it adds to the stack. -/
def leavesWord (byte : UInt8) : Bool :=
  (familyBytes "ARITHMETIC" ++ familyBytes "BITWISE" ++ familyBytes "ENVIRONMENT" ++
    [0x20, 0x35, 0x51, 0x59, 0x54, 0x5c]).contains byte

instance {family : String} : Command (FrameCommand family) FrameState FrameContext IO where
  apply c s := stepBoth c.ctx c.code s
  label c := s!"{c.name} [{hex c.code}]"
  build ctx := buildFrameCommand family (familyBytes family) ctx
  next c s :=
    let byte := c.code.data.back?.getD 0
    if leavesWord byte then { s with depth := s.depth + 1 } else s

/-- DUP and SWAP, which need a stack: the command is skipped on one that is too short. -/
structure StackCommand where
  ctx : FrameContext
  byte : UInt8

instance : Command StackCommand FrameState FrameContext IO where
  check c s :=
    let depth := (s.frame.map (·.2.stack.val.length)).getD 0
    let n := c.byte.toNat % 16
    -- One command in the family reaches one past the stack, to see the underflow.
    if c.byte ≥ 0x90 then n + 1 ≤ depth else n ≤ depth
  apply c s := do
    cover c.ctx.minimum "a DUP or SWAP ran" true
    stepBoth c.ctx ⟨#[c.byte]⟩ s
  label c := s!"{if c.byte ≥ 0x90 then "SWAP" else "DUP"}{c.byte.toNat % 16 + 1}"
  build ctx := StackCommand.mk ctx <$> Gen.integral (.constant 0x80 0x9f)
  next c s := if c.byte ≥ 0x90 then s else { s with depth := s.depth + 1 }
  -- Mostly an instruction that the stack can serve.
  --
  -- That is DUP1 to DUP of the depth, and SWAP1 to SWAP of one less.
  --
  -- The blind draw stays, for the reach of one past the stack.
  buildIn ctx s :=
    let blind := StackCommand.mk ctx <$> Gen.integral (.constant 0x80 0x9f)
    let dup := (fun n => StackCommand.mk ctx (0x80 + UInt8.ofNat n)) <$>
      Gen.nat (.constant 0 (min s.depth 16 - 1))
    let swap := (fun n => StackCommand.mk ctx (0x90 + UInt8.ofNat n)) <$>
      Gen.nat (.constant 0 (min (s.depth - 1) 16 - 1))
    if s.depth = 0 then blind
    else if s.depth = 1 then Gen.frequency [(4, dup), (1, blind)]
    else Gen.frequency [(3, dup), (3, swap), (1, blind)]

/-- A frame steps in EthLib as it steps in the reference, over any sequence of instructions.

After each command the gas left, the program counter and the memory are the reference's.

So are the whole stack, the refund, the logs and the output.

A sequence carries the memory, the warm slots and the storage from one instruction to the next.

One instruction alone does not show that. -/
def frameScenario (mode : Mode) (ctx : FrameContext) : Property IO :=
  scenario mode ctx [
    Command.gen (FrameCommand "ARITHMETIC"), Command.gen (FrameCommand "BITWISE"),
    Command.gen (FrameCommand "MEMORY"), Command.gen (FrameCommand "STORAGE"),
    Command.gen (FrameCommand "ENVIRONMENT"), Command.gen (FrameCommand "LOG"),
    Command.gen (FrameCommand "STACK"), Command.gen StackCommand,
    Command.gen (FrameCommand "MEMORY"), Command.gen (FrameCommand "STORAGE"),
    Command.gen (FrameCommand "END")]

end EvmProperty

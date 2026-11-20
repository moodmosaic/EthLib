import Property.Evm.Program
import Property.Evm.Trace

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

It gives the frame after the code and the opcodes that ran.

An error leaves the frame as it was, so a sequence goes on after a refused instruction. -/
def runTraced {fork : Fork} (evm : Evm fork Nat) (code : ByteArray) :
    Except EvmError (Evm fork Nat × List UInt8) :=
  let rec go (fuel : Nat) (evm : Evm fork Nat) (ran : List UInt8) :
      Except EvmError (Evm fork Nat × List UInt8) :=
    match fuel with
    | 0 => .ok (evm, ran)
    | fuel + 1 =>
      if evm.running && evm.pc < code.size then
        match step fork evm with
        | .ok (.next after) =>
          -- An instruction that keeps its reads gives its halt as a frame.
          match after.error with
          | some e => .error e
          | none => go fuel after (code[evm.pc]! :: ran)
        | .ok (.child ..) => .error (.unspecifiedOpcode 0)
        | .error e => .error e
      else .ok (evm, ran)
  go 100 { evm with code, pc := 0, validJumpDestinations := validJumpDestinations code } []

/-- Run code in a frame, as `runTraced` does, and give the frame only. -/
def runCode {fork : Fork} (evm : Evm fork Nat) (code : ByteArray) :
    Except EvmError (Evm fork Nat) :=
  (·.1) <$> runTraced evm code

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
def storageMachine (asked : Bool) :
    StateMachine StorageModel StorageStep (Σ fork, StorageSut fork) IO where
  toModel := storageModel
  initSut m := pure ⟨m.fork, storageFrame m, false⟩
  applySut sut before after t := do
    let ⟨fork, sut⟩ := sut
    label (if fork < .tangerineWhistle then "before Tangerine Whistle"
      else if fork < .istanbul then "Tangerine Whistle to Petersburg"
      else if fork < .berlin then "Istanbul and Muir Glacier"
      else if fork < .london then "Berlin" else "London and later")
    match t with
    | .sload key =>
      let slot := before.slots[key]!
      label (if after.refused then "SLOAD out of gas"
        else if fork < .berlin then "SLOAD" else if slot.warm then "SLOAD warm" else "SLOAD cold")
    | .sstore key value =>
      let slot := before.slots[key]!
      let access := if fork < .berlin then "" else if slot.warm then ", warm" else ", cold"
      if after.refused then
        label (if fork ≥ .istanbul ∧ before.gas - 6 ≤ 2300 then "SSTORE refused at the stipend"
          else "SSTORE out of gas")
      else
        label s!"{sstoreClass slot.original slot.current value}{access}"
        -- The share is of the sequences in which a write of the class ran.
        let least := if asked then 3 else 0
        for kind in ["SSTORE leaves the word", "SSTORE sets a clean zero slot",
            "SSTORE clears a clean slot", "SSTORE changes a clean slot",
            "SSTORE resets a dirty slot to its zero", "SSTORE resets a dirty slot to its word",
            "SSTORE writes a slot that was cleared", "SSTORE clears a dirty slot",
            "SSTORE changes a dirty slot"] do
          cover least kind (kind = sstoreClass slot.original slot.current value)
      classify "the refund falls" (after.refund < before.refund)
      classify "the refund rises" (after.refund > before.refund)
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
def deepStackMachine (asked : Bool) :
    StateMachine DeepStack DeepStep (Evm .glamsterdam Nat × Bool) IO where
  toModel := deepStackModel
  initSut m := do
    let frame := newFrame .glamsterdam m.gas false
    let stack := m.stack.reverse.foldl (init := frame.stack) fun stack word =>
      match stack.push (BitVec.ofNat 256 word) with
      | .ok next => next
      | .error _ => stack
    pure ({ frame with stack }, false)
  applySut sut before after t := do
    let depth := before.stack.length
    let refusal (needs : Option Nat) (pushes : Bool) : String :=
      match needs with
      | none => "refused: the immediate encodes nothing"
      | some n => if n > depth then "refused: the stack is too short"
        else if pushes ∧ depth = 1024 then "refused: the stack is full"
        else if before.gas < 3 then "refused: out of gas" else "runs"
    label (match t with
      | .push _ => if after.refused then "PUSH refused" else "PUSH runs"
      | .dupn x => s!"DUPN {refusal (decodeSingleModel x.toNat) true}"
      | .swapn x => s!"SWAPN {refusal ((decodeSingleModel x.toNat).map (· + 1)) false}"
      | .exchange x => s!"EXCHANGE {refusal ((decodePairModel x.toNat).map (·.2 + 1)) false}")
    let reach : Option Nat := match t with
      | .push _ => none
      | .dupn x => decodeSingleModel x.toNat
      | .swapn x => (decodeSingleModel x.toNat).map (· + 1)
      | .exchange x => (decodePairModel x.toNat).map (·.2 + 1)
    let least := if asked then 2 else 0
    cover least "it reaches the deepest item" (reach = some depth)
    cover least "it reaches one past the deepest item" (reach = some (depth + 1))
    cover (5 * least) "DUPN runs" (!after.refused ∧ t matches .dupn _)
    cover (5 * least) "SWAPN runs" (!after.refused ∧ t matches .swapn _)
    cover (5 * least) "EXCHANGE runs" (!after.refused ∧ t matches .exchange _)
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

/-! ## A frame beside the reference, one kind of code per command -/

/-- The state of a scenario: the frame of EthLib.

`Command.next` runs a command in it, so `Command.buildIn` sees the stack and the memory it meets. -/
structure FrameState (fork : Fork) where
  evm : Evm fork Nat

/-- What commands are built from: the name of the fork in the reference, and the oracle. -/
structure FrameContext (fork : Fork) where
  name : String
  oracle : Oracle
  /-- The opcodes that ran, over the sequences of the fork. -/
  counts : IO.Ref OpCounts
  /-- Whether the property requires the minimum share of each class.

  A run of few sequences stays at small sizes, where sequences are short and the shares low. -/
  asked : Bool := false

/-- What a frame shows after code ran, in the text form of the oracle. -/
def showFrame {fork : Fork} (evm : Evm fork Nat) : String :=
  let stack := evm.stack.val.map fun w => hexNat w.toNat
  " ".intercalate ["ok", toString evm.gas, toString evm.pc, toString evm.memory.size,
    hexVec (Cryptography.Hash.Keccak.keccak256 evm.memory),
    if stack.isEmpty then "-" else ",".intercalate stack,
    toString evm.substate.refundCounter, showLogs evm.substate.logs,
    if evm.running then "1" else "0", hex evm.output]

/-- The frame of a state after code, as far as EthLib tells: a refused code leaves it. -/
def FrameState.after {fork : Fork} (s : FrameState fork) (code : ByteArray) : FrameState fork :=
  match runCode s.evm code with
  | .ok after => ⟨{ after with running := true }⟩
  | .error _ => s

/-- Run code in the frame of EthLib and in the frame of the reference, and compare what they show.

A refused code leaves both frames as they were.

`kind` names the command, for the shares of the report. -/
def stepBoth {fork : Fork} (ctx : FrameContext fork) (kind : String) (code : ByteArray)
    (s : FrameState fork) : TestT IO (FrameState fork) := do
  let answer ← ctx.oracle.ask ["op", hex code]
  annotate s!"code {hex code}: the reference says {answer}"
  match runTraced s.evm code with
  | .error e =>
    annotate s!"EthLib fails with {reprStr e}"
    label s!"{kind} halts: {errorName e}"
    (if e == .revert then "revert" else "halt") === (answer.splitOn " ").head!
    pure s
  | .ok (after, ran) =>
    label s!"{kind} runs"
    let trace : Trace := ran.foldl (init := {}) fun trace byte =>
      { trace with ran := trace.ran.modify byte.toNat (· + 1) }
    evalIO (ctx.counts.modify (·.add fork.name trace))
    showFrame after === answer
    pure ⟨{ after with running := true }⟩

/-- A snippet of the whole programs, which leaves the stack as it found it.

Its writes to memory, to storage and to the logs stay for the commands after it. -/
structure Snippet (fork : Fork) where
  snip : Snip

instance {fork : Fork} : Command (Snippet fork) (FrameState fork) (FrameContext fork) IO where
  apply ctx c s := stepBoth ctx "a snippet" (assemble [c.snip]) s
  label c := reprStr c.snip
  build _ := Snippet.mk <$> Gen.frequency ([(50, genOp fork), (20, genNullary fork),
    (33, genPush fork), (16, genDup), (16, genSwap), (3, genSkip), (4, genSkipIf), (3, genLoop),
    (6, genSlot fork)] ++
    -- RETURNDATACOPY of no byte: a stepped frame runs no call, so its return data is empty.
    if hasOp fork 0x3e then
      [(3, pure (Snip.ofBytes "RETURNDATACOPY of no byte" [0x60, 0, 0x60, 0, 0x60, 0, 0x3e]))]
    else [])
  next _ c s := s.after (assemble [c.snip])

/-- An instruction after pushes of its operands, whose result stays on the stack. -/
structure Operate (fork : Fork) where
  byte : UInt8
  args : List Nat

/-- The code of an instruction after pushes of its operands. -/
def opCode (byte : UInt8) (args : List Nat) : ByteArray := ⟨(pushes args ++ [byte]).toArray⟩

instance {fork : Fork} : Command (Operate fork) (FrameState fork) (FrameContext fork) IO where
  apply ctx c s := stepBoth ctx "an instruction that leaves its result" (opCode c.byte c.args) s
  label c := s!"{opName c.byte} {c.args.map hexNat}"
  build _ := do
    let table := (instructions ++ nullary.map (·, [])).filter fun (byte, _) =>
      hasOp fork byte && pushesWord byte
    let (byte, kinds) ← Gen.element table
    Operate.mk byte <$> genArgs kinds
  next _ c s := s.after (opCode c.byte c.args)

/-- DUP, SWAP or POP on the words that the stack holds. -/
structure StackCommand (fork : Fork) where
  byte : UInt8

/-- The words that DUP, SWAP or POP needs on the stack. -/
def stackNeeds (byte : UInt8) : Nat :=
  if byte = 0x50 then 1 else if byte ≥ 0x90 then byte.toNat - 0x8e else byte.toNat - 0x7f

instance {fork : Fork} : Command (StackCommand fork) (FrameState fork) (FrameContext fork) IO where
  -- An instruction may reach one word past the stack, to see the underflow.
  check _ c s := stackNeeds c.byte ≤ s.evm.stack.val.length + 1
  apply ctx c s := do
    let fits := stackNeeds c.byte ≤ s.evm.stack.val.length
    let least := if ctx.asked then 3 else 0
    cover (3 * least) "DUP on the stack it meets" (fits ∧ c.byte ≥ 0x80 ∧ c.byte < 0x90)
    cover (3 * least) "SWAP on the stack it meets" (fits ∧ c.byte ≥ 0x90)
    cover least "POP on the stack it meets" (fits ∧ c.byte = 0x50)
    classify "DUP9 to DUP16 on the stack it meets" (fits ∧ c.byte ≥ 0x88 ∧ c.byte < 0x90)
    classify "SWAP9 to SWAP16 on the stack it meets" (fits ∧ c.byte ≥ 0x98)
    stepBoth ctx (if c.byte = 0x50 then "POP" else if c.byte ≥ 0x90 then "SWAP" else "DUP")
      ⟨#[c.byte]⟩ s
  label c := opName c.byte
  build _ := StackCommand.mk <$> Gen.integral (.constant 0x80 0x9f)
  next _ c s := s.after ⟨#[c.byte]⟩
  -- Mostly an instruction that the stack can serve, and now and then one that reaches one past it.
  buildIn _ s :=
    let depth := s.evm.stack.val.length
    let dup (most : Nat) := (fun n => StackCommand.mk (UInt8.ofNat (0x7f + n))) <$>
      Gen.nat (.constant 1 most)
    let swap (most : Nat) := (fun n => StackCommand.mk (UInt8.ofNat (0x8f + n))) <$>
      Gen.nat (.constant 1 most)
    let past := Gen.element ((if depth < 16 then [StackCommand.mk (UInt8.ofNat (0x80 + depth))]
      else []) ++ (if depth < 17 ∧ depth ≥ 1 then [StackCommand.mk (UInt8.ofNat (0x8f + depth))]
      else []) ++ [StackCommand.mk (if depth = 0 then 0x50 else 0x80)])
    if depth = 0 then past
    else if depth = 1 then Gen.frequency [(6, dup 1), (1, pure ⟨0x50⟩), (1, past)]
    else Gen.frequency [(5, dup (min depth 16)), (5, swap (min (depth - 1) 16)), (1, pure ⟨0x50⟩),
      (1, past)]

/-- An instruction on the words that the stack holds, with no push of its own.

So the results of the commands before it are its operands. -/
structure Consume (fork : Fork) where
  byte : UInt8

/-- The instructions that compute a word from words, with the number they take. -/
def pureOps : List (UInt8 × Nat) :=
  instructions.filterMap fun (byte, kinds) =>
    if byte.toNat ≤ 0x1e then some (byte, kinds.length) else none

instance {fork : Fork} : Command (Consume fork) (FrameState fork) (FrameContext fork) IO where
  check _ c s := ((pureOps.lookup c.byte).getD 4) ≤ s.evm.stack.val.length
  apply ctx c s := do
    cover (if ctx.asked then 5 else 0) "an instruction on the words of the stack" true
    stepBoth ctx "an instruction on the stack" ⟨#[c.byte]⟩ s
  label c := s!"{opName c.byte} on the stack"
  build _ :=
    Consume.mk <$> Gen.element ((pureOps.filter fun (byte, _) => hasOp fork byte).map (·.1))
  next _ c s := s.after ⟨#[c.byte]⟩
  buildIn _ s := Consume.mk <$> Gen.element (((pureOps.filter fun (byte, needs) =>
    hasOp fork byte && needs ≤ max 1 s.evm.stack.val.length).map (·.1)))

/-- An instruction on a range of memory that ends around the size of the memory it meets.

A range that ends at the size costs no growth, and one byte more costs a word. -/
structure MemoryEdge (fork : Fork) where
  byte : UInt8
  args : List Nat
  /-- Where the range ends, less the size of the memory. -/
  past : Int

instance {fork : Fork} : Command (MemoryEdge fork) (FrameState fork) (FrameContext fork) IO where
  apply ctx c s := do
    let least := if ctx.asked then 3 else 0
    cover least "a range that ends at the size of the memory" (c.past = 0)
    cover least "a range that ends one byte past the memory" (c.past = 1)
    cover least "a range that ends inside the memory" (c.past < 0)
    stepBoth ctx "an instruction at the edge of the memory" (opCode c.byte c.args) s
  label c := s!"{opName c.byte} {c.args.map hexNat} (the range ends {c.past} past the memory)"
  build _ := pure ⟨0x51, [0], 32⟩
  next _ c s := s.after (opCode c.byte c.args)
  buildIn _ s := do
    let size := s.evm.memory.size
    let past ← Gen.element [(0 : Int), 1, -1, -32, 31, 32, 33]
    let stop := ((size : Int) + past).toNat
    let length ← Gen.element ([1, 32, 33].filter (· ≤ stop) ++ [stop])
    let start := stop - length
    let word ← genWord
    -- Each instruction with its range from `start` to `stop`: a word or a byte for the fixed ones.
    let choices : List (UInt8 × List Nat × Nat) := [
      (0x51, [stop - 32], 32), (0x52, [stop - 32, word], 32), (0x53, [stop - 1, word], 1),
      (0x20, [start, length], length), (0x37, [start, 0, length], length),
      (0x39, [start, 0, length], length), (0xa0, [start, length], length),
      (0xa1, [start, length, word], length), (0x5e, [start, 0, length], length),
      (0x5e, [0, start, length], length), (0xf3, [start, length], length),
      (0xfd, [start, length], length)]
    let fit := choices.filter fun (byte, _, needs) => hasOp fork byte && needs ≤ stop
    match fit with
    | [] => pure ⟨0x51, [0], (32 : Int) - size⟩
    | first :: rest =>
      let (byte, args, _) ← Gen.element (first :: rest)
      pure ⟨byte, args, past⟩

/-- A snippet that halts the frame, which both sides refuse and undo. -/
structure Spoil (fork : Fork) where
  snip : Snip

instance {fork : Fork} : Command (Spoil fork) (FrameState fork) (FrameContext fork) IO where
  apply ctx c s := stepBoth ctx "a spoiler" (assemble [c.snip]) s
  label c := reprStr c.snip
  build _ := Spoil.mk <$> Gen.frequency ([(3, genInvalid fork), (3, genUnderflow fork false),
    (3, genBadJump), (3, genHugeMemory fork false), (2, genEnding fork),
    (1, pure (Snip.ofBytes "STOP" [0x00]))] ++
    if hasOp fork 0x3e then [(2, genBadReturnData)] else [])
  next _ c s := s.after (assemble [c.snip])

/-- The frame at the start of a scenario: mostly with gas for every command, now and then static.

A static frame exists from Byzantium. -/
def genFrameStart (fork : Fork) : Gen (Nat × Bool) :=
  Gen.zip (Gen.frequency [(6, pure 3000000), (1, Gen.nat (.linear 0 100000))])
    (if fork ≥ .byzantium then Gen.frequency [(7, pure false), (1, pure true)] else pure false)

/-- A frame steps in EthLib as it steps in the reference, over any sequence of commands.

After each command the gas left, the program counter and the memory are the reference's.

So are the whole stack, the refund, the logs and the output.

A sequence carries the memory, the stack, the warm slots and the storage from one to the next.

One instruction alone does not show that. -/
def frameScenario (mode : Mode) (fork : Fork) (ctx : FrameContext fork)
    (range : Range Nat := .linear 1 40) : Property IO :=
  scenarioFrom ((fun (gas, static) => FrameState.mk (newFrame fork gas static)) <$>
      genFrameStart fork) mode ctx
    [Command.gen (Snippet fork), Command.gen (Snippet fork), Command.gen (Snippet fork),
      Command.gen (Operate fork), Command.gen (Operate fork), Command.gen (Operate fork),
      Command.gen (StackCommand fork), Command.gen (StackCommand fork),
      Command.gen (StackCommand fork), Command.gen (Consume fork), Command.gen (MemoryEdge fork),
      Command.gen (MemoryEdge fork), Command.gen (Spoil fork)]
    range fun s => do
      let static := s.evm.message.isStatic
      let _ ← ctx.oracle.ask ["frame", ctx.name, toString s.evm.gas, if static then "1" else "0"]
      label (if static then "a static frame" else "a frame that may write")
      label (if s.evm.gas < 3000000 then "a frame with little gas" else "a frame with ample gas")
      pure s

end EvmProperty

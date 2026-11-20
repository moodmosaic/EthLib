import Property.Evm.Run

/-!
# What a run reached

A property that passes may test little: the generator may halt most programs at their first byte.

So each run is observed, and the property names what the run reached.

`processMessageWith` of EthLib shows each step of each frame to an observer.

The observer here keeps a trace: the opcodes that ran, how each frame ended, the calls and results.

The trace only classifies a case, and the comparison with the reference does not read it.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Evm

namespace EvmProperty

/-- The name of an error, without its values. -/
def errorName : EvmError → String
  | .stackUnderflow => "stack underflow"
  | .stackOverflow => "stack overflow"
  | .outOfGas => "out of gas"
  | .invalidOpcode _ => "invalid opcode"
  | .invalidJumpDest _ => "invalid jump"
  | .writeInStaticContext => "static violation"
  | .outOfBoundsRead .. => "return data out of bounds"
  | .invalidParameter _ => "invalid immediate"
  | .invalidContractPrefix => "code starts with 0xef"
  | .addressCollision _ => "address collision"
  | .precompile _ => "precompile failure"
  | .revert => "revert"
  | .state _ => "state error"
  | .unspecifiedOpcode _ => "unspecified opcode"
  | .encoding _ => "encoding error"
  | .forkNotYetSpecified _ => "fork not specified"

/-- The mnemonic of a byte: that of its opcode at any fork, or `INVALID` with the byte. -/
def opName (byte : UInt8) : String :=
  let b := byte.toNat
  match Op.decode byte with
  | none => s!"INVALID_{hexNat b}"
  | some (.push _) => s!"PUSH{b - 0x5f}"
  | some (.dup _) => s!"DUP{b - 0x7f}"
  | some (.swap _) => s!"SWAP{b - 0x8f}"
  | some (.log _) => s!"LOG{b - 0xa0}"
  | some op => (((reprStr op).splitOn ".").getLastD "").toUpper

/-- The family of an opcode, for the shares of a report. -/
def opFamily (byte : UInt8) : String :=
  let b := byte.toNat
  if b = 0 then "STOP"
  else if b ≤ 0x0b then "arithmetic"
  else if 0x10 ≤ b ∧ b ≤ 0x1e then "comparison and bitwise"
  else if b = 0x20 then "KECCAK256"
  else if 0x30 ≤ b ∧ b ≤ 0x3f then "environment"
  else if 0x40 ≤ b ∧ b ≤ 0x4b then "block"
  else if b = 0x54 ∨ b = 0x55 then "storage"
  else if b = 0x5c ∨ b = 0x5d then "transient storage"
  else if b = 0x56 ∨ b = 0x57 ∨ b = 0x5b ∨ b = 0x58 then "control flow"
  else if 0x50 ≤ b ∧ b ≤ 0x5e then "stack and memory"
  else if 0x5f ≤ b ∧ b ≤ 0x7f then "PUSH"
  else if 0x80 ≤ b ∧ b ≤ 0x8f then "DUP"
  else if 0x90 ≤ b ∧ b ≤ 0x9f then "SWAP"
  else if 0xa0 ≤ b ∧ b ≤ 0xa4 then "LOG"
  else if 0xe6 ≤ b ∧ b ≤ 0xe8 then "EIP-8024"
  else if b = 0xf0 ∨ b = 0xf5 then "creation"
  else if b = 0xf1 ∨ b = 0xf2 ∨ b = 0xf4 ∨ b = 0xfa then "call"
  else if b = 0xf3 ∨ b = 0xfd then "RETURN and REVERT"
  else if b = 0xff then "SELFDESTRUCT"
  else "invalid"

/-- The opcodes that start a message. -/
def messageOps : List UInt8 := [0xf0, 0xf1, 0xf2, 0xf4, 0xf5, 0xfa]

/-- What an observer has seen of a run. -/
structure Trace where
  /-- The steps that gave a next frame or a message, over every frame. -/
  steps : Nat := 0
  /-- The same, for the first frame only. -/
  topSteps : Nat := 0
  /-- How often the step of each byte succeeded. -/
  ran : Array Nat := Array.replicate 256 0
  /-- How often the step of each byte failed. -/
  refused : Array Nat := Array.replicate 256 0
  /-- The error of each frame that halted, with the depth of the frame. -/
  halts : Array (Nat × String) := #[]
  /-- Each call or creation: its opcode and its result. -/
  calls : Array (UInt8 × String) := #[]
  /-- The calls whose message runs: the depth of the caller and the opcode, the last first. -/
  pending : List (Nat × UInt8) := []
  /-- How the last frame ended, for the caller that goes on after it. -/
  lastEnd : String := ""
  /-- The deepest frame that ran a step. -/
  depth : Nat := 0
  /-- Whether a step grew the memory of its frame. -/
  memoryGrew : Bool := false
  /-- The kinds of SSTORE that ran, by the original, current and new words of the slot. -/
  sstores : Array String := #[]
  /-- Whether an access of each kind ran, from Berlin. -/
  coldSlot : Bool := false
  warmSlot : Bool := false
  coldAccount : Bool := false
  warmAccount : Bool := false
  deriving Inhabited

/-- The class of a write by SSTORE, in the terms of EIP-2200. -/
def sstoreClass (original current new : Nat) : String :=
  if current = new then "SSTORE leaves the word"
  else if original = current then
    (if original = 0 then "SSTORE sets a clean zero slot"
    else if new = 0 then "SSTORE clears a clean slot"
    else "SSTORE changes a clean slot")
  else if original = new then
    (if original = 0 then "SSTORE resets a dirty slot to its zero"
    else "SSTORE resets a dirty slot to its word")
  else if original ≠ 0 ∧ current = 0 then "SSTORE writes a slot that was cleared"
  else if original ≠ 0 ∧ new = 0 then "SSTORE clears a dirty slot"
  else "SSTORE changes a dirty slot"

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The trace after the step of a frame. -/
def Trace.see (t : Trace) (evm : Evm fork Meter)
    (result : Except EvmError (StepResult fork Meter)) : Trace :=
  let depth := evm.message.depth
  let byte : UInt8 := if h : evm.pc < evm.code.size then evm.code[evm.pc] else 0
  let top (i : Nat) : Nat := (evm.stack.val[i]?.map (·.toNat)).getD 0
  -- A caller that goes on tells how its message ended: the word it got is on top.
  let pending := t.pending.dropWhile fun (d, _) => d > depth
  let t := match pending with
    | (d, op) :: rest =>
      if d = depth then
        let result := if top 0 ≠ 0 then "succeeds"
          else if t.lastEnd = "" then "fails in a precompile"
          else if t.lastEnd = "stopped" then "fails at the deposit of code"
          else t.lastEnd
        { t with pending := rest, calls := t.calls.push (op, result) }
      else { t with pending }
    | [] => { t with pending }
  let t := { t with depth := max t.depth depth }
  -- The accesses that EIP-2929 prices.
  let t := if fork ≥ .berlin then
      if byte = 0x54 ∨ byte = 0x55 then
        let keys := evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅
        if U256.toBeBytes (BitVec.ofNat 256 (top 0)) ∈ keys then { t with warmSlot := true }
        else { t with coldSlot := true }
      else
        let word : Option Nat :=
          if ([0x31, 0x3b, 0x3c, 0x3f, 0xff] : List UInt8).contains byte then some (top 0)
          else if ([0xf1, 0xf2, 0xf4, 0xfa] : List UInt8).contains byte then some (top 1)
          else none
        match word with
        | some word =>
          if toAddressMasked (BitVec.ofNat 256 word) ∈ evm.substate.accessedAddresses then
            { t with warmAccount := true }
          else { t with coldAccount := true }
        | none => t
    else t
  let ended (t : Trace) (after : Evm fork Meter) : Trace :=
    if after.running then t
    else match after.error with
      | none => { t with lastEnd := "stopped" }
      | some .revert => { t with lastEnd := "reverts" }
      | some e => { t with lastEnd := "halts", halts := t.halts.push (depth, errorName e) }
  match result with
  | .error e =>
    { t with refused := t.refused.modify byte.toNat (· + 1), lastEnd := "halts"
             halts := t.halts.push (depth, errorName e) }
  | .ok (.next after) =>
    let t := { t with steps := t.steps + 1, ran := t.ran.modify byte.toNat (· + 1)
                      topSteps := if depth = 0 then t.topSteps + 1 else t.topSteps
                      memoryGrew := t.memoryGrew || after.memory.size > evm.memory.size }
    let t := if byte = 0x55 ∧ after.error.isNone then
        let address := evm.message.currentTarget
        let key := U256.toBeBytes (BitVec.ofNat 256 (top 0))
        { t with sstores := t.sstores.push (sstoreClass
            (evm.state.getStorageOriginal address key).toNat
            (evm.state.getStorage address key).toNat (top 1)) }
      else t
    -- A call or a creation that gives the next frame at once ran no message.
    let t := if messageOps.contains byte ∧ after.error.isNone then
        { t with calls := t.calls.push (byte, "runs no message") }
      else t
    ended t after
  | .ok (.child caller _ _) =>
    { t with steps := t.steps + 1, ran := t.ran.modify byte.toNat (· + 1)
             topSteps := if depth = 0 then t.topSteps + 1 else t.topSteps
             memoryGrew := t.memoryGrew || caller.memory.size > evm.memory.size
             pending := (depth, byte) :: t.pending, lastEnd := "" }

/-- The observer that keeps a trace. -/
def traceObserver : StepObserver (StateT Trace (Except EvmError)) fork Meter :=
  fun evm result => modify fun t => t.see evm result

/-- The trace of a message of a scenario, with the frame that ends it. -/
def traceMessage (fork : Fork) (create static : Bool) (gas value : Nat) (data code : ByteArray)
    (accounts : List PreAccount) (big : Bool := false) : Trace × Option (Evm fork Nat) :=
  let message := messageOf fork create static gas value data code big
  let state := txState accounts
  let run : StateT Trace (Except EvmError) (Evm fork Nat) :=
    if create then
      Subtype.val <$> processCreateMessageWith (Meter := Nat) fork traceObserver message state
        startSubstate
    else
      Subtype.val <$> processMessageWith (Meter := Nat) fork traceObserver message state
        startSubstate
  match run.run {} with
  | .ok (evm, trace) => (trace, some evm)
  | .error _ => ({}, none)

/-- The trace of a call at Glamsterdam with a reservoir, and the frame that ends it. -/
def traceGlamsterdam (static : Bool) (gas reservoir value : Nat) (data code : ByteArray)
    (accounts : List PreAccount) : Trace × Option (Evm .glamsterdam StateGasMeter) :=
  let message := { messageOf .glamsterdam false static gas value data code with reservoir }
  let run : StateT Trace (Except EvmError) (Evm .glamsterdam StateGasMeter) :=
    Subtype.val <$> processMessageWith (Meter := StateGasMeter) .glamsterdam traceObserver message
      (txState accounts) startSubstate
  match run.run {} with
  | .ok (evm, trace) => (trace, some evm)
  | .error _ => ({}, none)

/-- How many steps a run made, as a class. -/
def stepClass (steps : Nat) : String :=
  if steps = 0 then "0" else if steps ≤ 5 then "1 to 5" else if steps ≤ 20 then "6 to 20"
  else if steps ≤ 100 then "21 to 100" else "over 100"

/-- The counts of a campaign: for each fork, its programs and those that ran each opcode. -/
structure OpCounts where
  programs : Std.HashMap String Nat := {}
  ran : Std.HashMap (String × UInt8) Nat := {}

/-- The counts with one more program at a fork, and the opcodes its trace ran. -/
def OpCounts.add (counts : OpCounts) (fork : String) (trace : Trace) : OpCounts :=
  let ran := (List.range 256).foldl (init := counts.ran) fun ran b =>
    if trace.ran[b]! > 0 then
      ran.insert (fork, UInt8.ofNat b) (ran.getD (fork, UInt8.ofNat b) 0 + 1)
    else ran
  { programs := counts.programs.insert fork (counts.programs.getD fork 0 + 1), ran }

/-- Name what the trace of a run reached, for the shares of the report. -/
def labelTrace {m : Type → Type} [Monad m] (trace : Trace) (error : Option EvmError)
    (output : ByteArray) (refund : Int) (logs : Nat) : TestT m Unit := do
  label (match error with
    | none => if output.isEmpty then "ends: stops with no output" else "ends: returns data"
    | some .revert => "ends: reverts"
    | some e => s!"ends: halts, {errorName e}")
  label s!"steps of the first frame: {stepClass trace.topSteps}"
  label s!"steps of all frames: {stepClass trace.steps}"
  for (_, name) in trace.halts.toList do
    label s!"a frame halts: {name}"
  for (op, result) in trace.calls.toList do
    label s!"{opName op} {result}"
  for name in trace.sstores.toList do
    label name
  for family in ((List.range 256).filter (trace.ran[·]! > 0)).map (opFamily ∘ UInt8.ofNat) do
    label s!"ran: {family}"
  classify "a frame at depth 1" (trace.depth ≥ 1)
  classify "a frame at depth 2 or more" (trace.depth ≥ 2)
  classify "memory grows" trace.memoryGrew
  classify "a cold slot" trace.coldSlot
  classify "a warm slot" trace.warmSlot
  classify "a cold account" trace.coldAccount
  classify "a warm account" trace.warmAccount
  classify "a refund" (refund > 0)
  classify "a log" (logs > 0)

end EvmProperty

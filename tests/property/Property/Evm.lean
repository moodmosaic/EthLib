import Property.Evm.Program
import Property.Evm.Precompile
import Property.Evm.Machine
import Property.Evm.Fees
import Property.Evm.Pure
import Property.Evm.Glamsterdam

/-!
# The EVM, on generated inputs

Each property generates inputs and requires an answer that EthLib did not compute.

It is that of the Python execution-specs (`oracle/evm.py`), or of a model written from the EIPs.

    lake exe evm-property            # 100 cases of each
    lake exe evm-property 1000
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Evm

namespace EvmProperty

/-! ## Whole programs -/

/-- A run: the fork, the message and the state before it. -/
structure Scenario where
  fork : Fork × String
  create : Bool
  static : Bool
  gas : Nat
  value : Nat
  data : ByteArray
  program : List Snip
  callees : List (List Snip)
  delegate : Nat
  slots : List (Nat × Nat)

instance : Repr Scenario where
  reprPrec s _ := s!"fork={s.fork.2} ({s.fork.1.name}) create={s.create} static={s.static} \
    gas={s.gas} value={s.value} data={hex s.data}\n  code={hex (assemble s.program)}\n  \
    program={reprStr s.program}\n  callees={s.callees.map fun c => hex (assemble c)} \
    delegate={hexNat s.delegate} slots={s.slots}"

/-- The accounts of a scenario: the caller, the target with the program, and what it may call.

The third callee holds a delegation designator of EIP-7702. -/
def Scenario.accounts (s : Scenario) : List PreAccount :=
  let designator : ByteArray :=
    ⟨(([0xef, 0x01, 0x00] : List UInt8) ++ beBytes 20 s.delegate).toArray⟩
  let callee (i : Nat) : ByteArray := assemble (s.callees.getD i [])
  [⟨callerAddress, 0, 10 ^ 18, .empty, []⟩,
   ⟨targetAddress, if s.create then 0 else 1, if s.create then 0 else 1000,
     if s.create then .empty else assemble s.program, if s.create then [] else s.slots⟩,
   ⟨addressOf 0xa1 0xa1, 1, 7, callee 0, [(0, 1)]⟩,
   ⟨addressOf 0xa2 0xa2, 0, 0, callee 1, []⟩,
   ⟨addressOf 0xa3 0xa3, 1, 1, designator, []⟩]

/-- A scenario: any fork, mostly a call with enough gas, and programs for that fork. -/
def genScenario : Gen Scenario := do
  let fork ← genFork
  let create ← Gen.frequency [(5, pure false), (1, pure true)]
  let static ← Gen.frequency [(9, pure false), (1, pure true)]
  let gas ← Gen.frequency [(2, Gen.nat (.exponential 0 3000000)), (1, Gen.nat (.linear 0 60000)),
    (4, Gen.nat (.linear 100000 3000000))]
  let value ← Gen.frequency [(3, pure 0), (1, Gen.nat (.linear 1 100))]
  let data ← genBytes (.linear 0 70)
  let program ← genProgram fork.1
  let callees ← Gen.list (.constant 2 2) (genProgram fork.1 12)
  let delegate ← Gen.frequency [
    (4, addressNat <$> Gen.element (auxAddresses ++ [targetAddress])),
    (2, Gen.element [1, 2, 4, 9, 0x100, 0])]
  let slots ← Gen.list (.linear 0 3) (Gen.zip (Gen.nat (.constant 0 3)) (Gen.nat (.constant 0 2)))
  -- No message is static before STATICCALL exists.
  pure ⟨fork, create, static && !create && fork.1 ≥ .byzantium, gas, value, data, program, callees,
    delegate, slots⟩

/-- The fields of two results agree, and the report names the first that does not. -/
def sameFields (got want : String) : TestT IO Unit := do
  let names := ["status", "gas left", "output", "refund", "logs", "accounts to delete",
    "touched accounts", "state", "transient storage"]
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

/-- A message leaves in EthLib what it leaves in the reference.

This covers the status, the gas left, the output, the refund, the logs and the accounts to delete.

It also covers each account with its nonce, its balance, its code and its storage. -/
def wholeProgram (oracle : Oracle) : Property IO := propertyM do
  let s ← forAll genScenario
  pure do
    let code := assemble s.program
    let accounts := s.accounts
    let (got, error) := runEthLib s.fork.1 s.create s.static s.gas s.value s.data code accounts
    let answer ← oracle.ask
      (runCommand s.fork.2 s.create s.static s.gas s.value s.data code accounts)
    let (want, wantError) := match answer.splitOn "\t" with
      | [want, error] => (want, error)
      | _ => (answer, "")
    annotate s!"EthLib's error: {error}; the reference's: {wantError}"
    sameFields got want

/-- The fields of two results of Glamsterdam agree, and the report names the first that differs. -/
def sameGlamsterdam (got want : String) : TestT IO Unit := do
  let names := ["status", "gas left", "state gas left", "output", "refund", "logs",
    "accounts to delete", "state", "account reads", "storage reads", "transient storage"]
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

/-- A call at Glamsterdam leaves what the branch `forks/amsterdam` of the reference leaves.

This covers the status, the gas left, the state gas left of EIP-8037, the output and the refund.

It also covers the logs with the transfer logs of EIP-7708, the accounts to delete and the state. -/
def glamsterdam (oracle : Oracle) : Property IO := propertyM do
  let s ← forAll (do
    let s ← genScenario
    let program ← genProgram .glamsterdam
    let callees ← Gen.list (.constant 2 2) (genProgram .glamsterdam 12)
    pure { s with fork := (.glamsterdam, "amsterdam"), create := false, program, callees })
  let reservoir ← forAll (Gen.frequency [(2, pure 0), (2, Gen.nat (.linear 0 400000)),
    (1, Gen.element [97920, 97919, 183600, 183599])])
  pure do
    let code := assemble s.program
    let accounts := s.accounts
    let (got, error) := runGlamsterdam s.static s.gas reservoir s.value s.data code accounts
    let answer ← oracle.ask ["run", if s.static then "1" else "0", toString s.gas,
      toString reservoir, toString s.value, hex s.data, hex code,
      ";".intercalate (accounts.map (·.show))]
    let (want, wantError) := match answer.splitOn "\t" with
      | [want, error] => (want, error)
      | _ => (answer, "")
    annotate s!"EthLib's error: {error}; the reference's: {wantError}"
    sameGlamsterdam got want

/-- FINDING: a frame that runs DELEGATECALL or STATICCALL records a read of its own account.

The reference reads the balance of the running account only for CALL and CALLCODE, which send value.

The frame here is alone, so the account is in the reads for no other reason. -/
def delegatecallReads (oracle : Oracle) : Property IO := propertyM do
  let call ← forAll (Gen.element [(0xf4 : UInt8), 0xfa, 0xf1, 0xf2])
  pure do
    let callee := addressNat (addressOf 0xa1 0xa1)
    let args := if call = 0xf1 || call = 0xf2 then [0, callee, 0, 0, 0, 0, 0]
      else [0, callee, 0, 0, 0, 0]
    let code := assemble [.op call args none]
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

/-- The snippets of raw bytes. -/
def rawSnips (bytes : List UInt8) : List Snip := bytes.map Snip.raw

/-- A program that calls itself with all its gas, so the depth of calls reaches its limit.

Each level may first count itself in storage, and keeps the result of its call in memory. -/
def genRecursion (fork : Fork) : Gen (List Snip) := do
  let call ← Gen.element ([0xf1, 0xf2, 0xf4, 0xfa].filter (hasOp fork))
  let count ← Gen.bool
  let value ← Gen.frequency [(3, pure 0), (1, pure 1)]
  let counter : List UInt8 := if count then [0x60, 0, 0x54, 0x60, 1, 0x01, 0x60, 0, 0x55] else []
  let args := [0, 0, 0, 0] ++ (if call = 0xf1 || call = 0xf2 then [value] else [])
  -- The operands of the call, the gas on top: all the gas, to this account.
  pure (rawSnips counter ++ rawSnips (args.flatMap fun (a : Nat) => [0x60, UInt8.ofNat a]) ++
    rawSnips [0x30, 0x5a, call, 0x60, 0, 0x52])

/-- A program that pushes words until the stack is full, in a loop or in a line. -/
def genDeepStack : Gen (List Snip) := do
  let pusher ← Gen.element [[0x60, 1], [0x30], [0x58], [0x5a], [0x59], [0x80], [0x8f]]
  let line ← Gen.bool
  let count ← Gen.element [1021, 1022, 1023, 1024, 1025]
  let seed ← Gen.element [[], [0x60, 7], [0x60, 7, 0x60, 8]]
  if line then pure (rawSnips (seed ++ (List.replicate count pusher).flatten))
  else pure (rawSnips (seed ++ [0x5b] ++ pusher ++ [0x60, UInt8.ofNat seed.length, 0x56]))

/-- A message that fills the stack or the depth of calls leaves what the reference leaves.

The limits are 1024 items and 1024 frames, and a random program reaches neither. -/
def deepLimits (oracle : Oracle) : Property IO := propertyM do
  let fork ← forAllWith (·.2) genFork
  let deepCalls ← forAll Gen.bool
  let program ← forAll (if deepCalls then genRecursion fork.1 else genDeepStack)
  -- All but one 64th of the gas goes down from Tangerine Whistle, so depth 1024 needs a lot.
  let gas ← forAll (if deepCalls then
      Gen.frequency [(1, Gen.nat (.linear 100000 3000000)), (2, Gen.element [10 ^ 10, 10 ^ 12])]
    else Gen.frequency [(2, Gen.nat (.linear 0 40000)), (1, pure 1000000)])
  let s : Scenario := ⟨fork, false, false, gas, 0, .empty, program, [[], []], 0, []⟩
  pure do
    let code := assemble program
    let accounts := s.accounts
    let (got, error) := runEthLib fork.1 false false gas 0 .empty code accounts
    let answer ← oracle.ask (runCommand fork.2 false false gas 0 .empty code accounts)
    let (want, wantError) := match answer.splitOn "\t" with
      | [want, error] => (want, error)
      | _ => (answer, "")
    annotate s!"EthLib's error: {error}; the reference's: {wantError}"
    sameFields got want

/-- Print how the generated runs end in EthLib, to judge the generator. -/
def stats (n : Nat) : IO Unit := do
  let mut counts : Std.HashMap String Nat := {}
  for _ in [0:n] do
    let s ← Gen.sample (Gen.resize 80 genScenario)
    let (got, error) := runEthLib s.fork.1 s.create s.static s.gas s.value s.data
      (assemble s.program) s.accounts
    let key := s!"{(got.splitOn " ").head!} {((error.splitOn " ").take 2)}"
    counts := counts.insert key (counts.getD key 0 + 1)
    -- What a run that ended well did: accounts created, logs, deletions, refunds.
    let fields := got.splitOn " "
    if fields.head! = "ok" then
      let marks : List (String × Bool) := [
        ("created an account", ((fields.getD 7 "").splitOn ";").length > 5),
        ("wrote a log", fields.getD 4 "-" != "-"), ("deleted an account", fields.getD 5 "-" != "-"),
        ("has a refund", fields.getD 3 "0" != "0"), ("returned data", fields.getD 2 "-" != "-")]
      for (mark, holds) in marks do
        if holds then counts := counts.insert mark (counts.getD mark 0 + 1)
  for (key, count) in counts.toList do
    IO.println s!"{count}\t{key}"

end EvmProperty

open EvmProperty in
def main (args : List String) : IO UInt32 := do
  if args.contains "stats" then
    stats (casesOf args)
    return 0
  let cases := casesOf args
  let oracle ← Oracle.start "evm"
  -- A word among the arguments keeps the properties whose name holds it.
  let words := args.filter fun arg => arg.toNat?.isNone
  let wanted (name : String) : Bool :=
    words.isEmpty || words.any fun w => (name.splitOn w).length > 1
  let properties : List (String × Property IO) := [
    ("a message leaves what the reference leaves", (wholeProgram oracle).withTests cases),
    ("a full stack and a full depth of calls leave what the reference leaves",
      (deepLimits oracle).withTests (cases / 10)),
    ("a precompile answers bytes as the reference", (precompileBytes oracle).withTests cases),
    ("a precompile answers a near-valid input as the reference",
      (precompileRecipe oracle fastKinds).withTests cases),
    ("a pairing precompile answers a near-valid input as the reference",
      (precompileRecipe oracle slowKinds).withTests (cases / 10)),
    ("arithmetic and bitwise instructions on integers", arithmetic.withTests (10 * cases)),
    ("EXP is the power modulo 2^256", exponent.withTests cases),
    ("the valid jump destinations", (jumpDests oracle).withTests cases),
    ("the addresses of CREATE and CREATE2", (contractAddress oracle).withTests cases),
    ("the growth of memory", (memoryGrowth oracle).withTests cases),
    ("the base fee of EIP-1559", (baseFee oracle).withTests cases),
    ("a gas limit may follow its parent's", (gasLimitRule oracle).withTests cases),
    ("fakeExponential is fake_exponential of EIP-4844", (fakeExponential oracle).withTests cases),
    ("the excess blob gas and the blob gas price", (blobGas oracle).withTests cases)]
  -- The branch of the reference with Glamsterdam is installed apart, so it may be absent.
  let specs := (← IO.getEnv "ETHLIB_AMSTERDAM_SPECS").getD ".venv/evm-amsterdam"
  let properties ← if ← System.FilePath.pathExists specs then do
      let amsterdam ← Oracle.start "evm_amsterdam"
      pure (properties ++ [("a call at Glamsterdam leaves what the branch of the reference leaves",
        (glamsterdam amsterdam).withTests cases)])
    else do
      IO.println s!"no reference of Glamsterdam at {specs}: its property is skipped"
      pure properties
  let machines : List (String × Property IO) :=
    ("SLOAD and SSTORE follow the model of the EIPs (StateMachine)",
      (storageMachine.property (.linear 1 40)).withTests cases) ::
    ("DUPN, SWAPN and EXCHANGE follow the list of EIP-8024 (StateMachine)",
      (deepStackMachine.property (.linear 1 30)).withTests cases) ::
    ([4, 5, 8, 11, 12, 17, 19, 20, 21].filterMap fun i => forks[i]?).flatMap fun fork =>
      [(s!"a frame steps as the reference at {fork.2} (Command, madhouse)",
        (frameScenario .madhouse
          ⟨fork, oracle, 3000000, if cases ≥ 300 then 5 else 0⟩).withTests cases),
       (s!"a frame steps as the reference at {fork.2} (Command, in order)",
        frameScenario .deterministic ⟨fork, oracle, 100000, 0⟩)]
  let properties := properties ++ machines
  let ok ← checkGroup "evm" (properties.filter fun (name, _) => wanted name)
  -- What the campaign found: these fail by design, and show their counterexample.
  if (← System.FilePath.pathExists specs) && (words.isEmpty || words.contains "findings") then
    let amsterdam ← Oracle.start "evm_amsterdam"
    let _ ← checkGroup "evm: findings" [
      ("DELEGATECALL and STATICCALL record no read of the running account",
        (delegatecallReads amsterdam).withTests 20)]
  pure (if ok then 0 else 1)

import Property.Evm.Machine
import Property.Evm.Precompile
import Property.Evm.Fees

/-!
# Every value of a table, not a sample

A table that a fork indexes holds a bug at the fork that a sample skips.

So each property here walks a whole table and compares every entry with the reference.

- The opcodes of each fork, and what each of the 256 bytes does at each fork.
- The precompiles of each fork.
- The gas constants of each fork, by name.
- SSTORE at every original, current and new word of zero, one and two, cold and warm.
- EXP at every byte length of its exponent.
- All but one 64th of every gas from 0 to 130.
- The discount of the multi-scalar multiplications at every number of pairs.

A walk is one test case: a failure names the entry, and nothing shrinks.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Evm
open EthLib.Execution.Fees

namespace EvmProperty

/-- The forks of the branch of the reference: those of the release, BPO3 to BPO5 and Glamsterdam. -/
def branchForks : List (Fork × String) :=
  forks ++ [(.bpo3, "bpo3"), (.bpo4, "bpo4"), (.bpo5, "bpo5"), (.glamsterdam, "amsterdam")]

/-- A list of numbers as the oracle writes it. -/
def showNats (values : List Nat) : String :=
  if values.isEmpty then "-" else ",".intercalate (values.map toString)

/-- The bytes that are opcodes at a fork. -/
def opcodesOf (fork : Fork) : List Nat :=
  (List.range 256).filter fun b => (Op.ofByte fork (UInt8.ofNat b)).isSome

/-- The opcodes of each fork are those of the reference, no more and no less.

An opcode that a fork has one fork early or late shows here, and nowhere in a sample of programs.

`oracle` is the release, and `branch` the branch with BPO3 to BPO5 and Glamsterdam. -/
def opcodeSets (oracle : Oracle) (branch : Option Oracle) : Property IO := propertyM do
  pure do
    let mut before : List Nat := []
    for (fork, name) in branchForks do
      let release := forks.any (·.2 = name)
      let source := if release then some oracle else branch
      match source with
      | none => pure ()
      | some source =>
        let want ← source.ask ["opcodes", name]
        let got := opcodesOf fork
        let added := got.filter (!before.contains ·)
        let news := if added.isEmpty || before.isEmpty then ""
          else ", new: " ++ " ".intercalate (added.map fun b => opName (UInt8.ofNat b))
        evalIO (IO.println s!"    {fork.name} ({name}): {got.length} opcodes{news}")
        annotate s!"the opcodes of {fork.name}, against {name}"
        showNats got === want
        before := got

/-- Each of the 256 bytes is an instruction at a fork exactly when the reference runs it.

The byte follows seventeen pushes of zero, so no instruction lacks operands.

This runs the byte, where `opcodeSets` reads the table of the reference. -/
def byteKinds (oracle : Oracle) : Property IO := propertyM do
  pure do
    for (fork, name) in forks do
      let want ← oracle.ask ["bytes", name]
      let got := String.ofList ((List.range 256).map fun b =>
        let code : ByteArray := ⟨((List.replicate 17 [0x60, 0x00]).flatten ++
          [UInt8.ofNat b]).toArray⟩
        match runCode (newFrame fork (10 ^ 9) false) code with
        | .error (.invalidOpcode _) => 'i'
        | _ => 'o')
      annotate s!"the bytes of {fork.name}, against {name}"
      got === want

/-- The precompiles of each fork are those of the reference, among the addresses below 512.

Four addresses far from them are precompiles at no fork. -/
def precompileSets (oracle : Oracle) (branch : Option Oracle) : Property IO := propertyM do
  pure do
    for (fork, name) in branchForks do
      let source := if forks.any (·.2 = name) then some oracle else branch
      match source with
      | none => pure ()
      | some source =>
        let want ← source.ask ["precompiles", name]
        let got := (List.range 512).filter (Precompiles.isPrecompile fork)
        evalIO (IO.println s!"    {fork.name} ({name}): precompiles {showNats got}")
        annotate s!"the precompiles of {fork.name}, against {name}"
        showNats got === want
        for far in [2 ^ 160 + 1, 2 ^ 160 + 0x100, 2 ^ 8 + 2 ^ 16, 2 ^ 255 + 1] do
          ensure (!Precompiles.isPrecompile fork far) s!"{far} is a precompile at {fork.name}"

/-- The gas constants of EthLib at a fork, under the names of the reference.

A price that EthLib computes from the fork stands under the name of the constant it replaces. -/
def gasCostsOf (fork : Fork) : List (String × Nat) :=
  let s := gasSchedule fork
  let blob : List (String × Nat) :=
    if h : .dencun ≤ fork then
      let schedule := BlobBaseFee.blobSchedule fork h
      [("BLOB_SCHEDULE_TARGET", schedule.target), ("BLOB_SCHEDULE_MAX", schedule.max),
        ("BLOB_BASE_FEE_UPDATE_FRACTION", schedule.baseFeeUpdateFraction),
        ("BLOB_TARGET_GAS_PER_BLOCK", BlobBaseFee.GAS_PER_BLOB * schedule.target)]
    else []
  open GasCosts in
  blob ++ [
    ("BASE", BASE), ("VERY_LOW", VERY_LOW), ("LOW", LOW), ("MID", MID), ("HIGH", HIGH),
    ("WARM_ACCESS", WARM_ACCESS), ("COLD_STORAGE_ACCESS", COLD_STORAGE_ACCESS),
    ("STORAGE_SET", STORAGE_SET), ("COLD_STORAGE_WRITE", COLD_STORAGE_WRITE),
    ("STORAGE_WRITE", STORAGE_WRITE), ("CALL_STIPEND", CALL_STIPEND),
    ("ACCOUNT_WRITE", ACCOUNT_WRITE), ("NEW_ACCOUNT", NEW_ACCOUNT),
    ("CODE_DEPOSIT_PER_BYTE", CODE_DEPOSIT_PER_BYTE), ("CODE_INIT_PER_WORD", CODE_INIT_PER_WORD),
    ("AUTH_PER_EMPTY_ACCOUNT", AUTH_PER_EMPTY_ACCOUNT), ("ZERO", ZERO),
    ("MEMORY_PER_WORD", MEMORY_PER_WORD), ("FAST_STEP", FAST_STEP),
    ("REFUND_AUTH_PER_EXISTING_ACCOUNT", REFUND_AUTH_PER_EXISTING_ACCOUNT),
    ("TX_DATA_PER_ZERO", TX_DATA_PER_ZERO), ("TX_DATA_TOKEN_STANDARD", TX_DATA_TOKEN_STANDARD),
    ("TX_MAX_GAS_LIMIT", TX_MAX_GAS_LIMIT), ("TX_VALUE_COST", TX_VALUE_COST),
    ("EXECUTION_PER_AUTH_BASE_COST", EXECUTION_PER_AUTH_BASE_COST),
    ("TX_MAX_TOTAL_GAS_LIMIT", TX_MAX_TOTAL_GAS_LIMIT), ("CREATE_ACCESS", CREATE_ACCESS),
    -- The prices that EthLib computes from the fork.
    ("CALL_VALUE", callValueCost fork 1),
    ("TX_BASE", if fork ≥ .glamsterdam then TX_BASE_COST else TX_BASE),
    ("SLOAD", sloadCost fork false), ("OPCODE_BALANCE", balanceCost fork false),
    ("OPCODE_EXTERNAL_BASE", externalBaseCost fork false),
    ("OPCODE_EXTCODEHASH", extcodehashCost fork false),
    ("OPCODE_CALL_BASE", callBaseCost fork false),
    ("OPCODE_CREATE_BASE", OPCODE_CREATE_BASE),
    ("OPCODE_EXP_PER_BYTE", s.OPCODE_EXP_PER_BYTE),
    ("OPCODE_SELFDESTRUCT_BASE", s.OPCODE_SELFDESTRUCT_BASE),
    ("OPCODE_SELFDESTRUCT_NEW_ACCOUNT", s.OPCODE_SELFDESTRUCT_NEW_ACCOUNT),
    ("TX_CREATE", s.TX_CREATE), ("TX_DATA_PER_NON_ZERO", s.TX_DATA_PER_NON_ZERO),
    ("TX_DATA_TOKEN_FLOOR", s.TX_DATA_TOKEN_FLOOR),
    ("TX_ACCESS_LIST_ADDRESS", s.TX_ACCESS_LIST_ADDRESS),
    ("TX_ACCESS_LIST_STORAGE_KEY", s.TX_ACCESS_LIST_STORAGE_KEY),
    ("COLD_ACCOUNT_ACCESS", s.COLD_ACCOUNT_ACCESS),
    ("REFUND_STORAGE_CLEAR", s.REFUND_STORAGE_CLEAR),
    ("REFUND_SELF_DESTRUCT", s.REFUND_SELF_DESTRUCT),
    -- The instructions.
    ("OPCODE_ADD", OPCODE_ADD), ("OPCODE_SUB", OPCODE_SUB), ("OPCODE_MUL", OPCODE_MUL),
    ("OPCODE_DIV", OPCODE_DIV), ("OPCODE_SDIV", OPCODE_SDIV), ("OPCODE_MOD", OPCODE_MOD),
    ("OPCODE_SMOD", OPCODE_SMOD), ("OPCODE_ADDMOD", OPCODE_ADDMOD),
    ("OPCODE_MULMOD", OPCODE_MULMOD), ("OPCODE_SIGNEXTEND", OPCODE_SIGNEXTEND),
    ("OPCODE_LT", OPCODE_LT), ("OPCODE_GT", OPCODE_GT), ("OPCODE_SLT", OPCODE_SLT),
    ("OPCODE_SGT", OPCODE_SGT), ("OPCODE_EQ", OPCODE_EQ), ("OPCODE_ISZERO", OPCODE_ISZERO),
    ("OPCODE_AND", OPCODE_AND), ("OPCODE_OR", OPCODE_OR), ("OPCODE_XOR", OPCODE_XOR),
    ("OPCODE_NOT", OPCODE_NOT), ("OPCODE_BYTE", OPCODE_BYTE), ("OPCODE_SHL", OPCODE_SHL),
    ("OPCODE_SHR", OPCODE_SHR), ("OPCODE_SAR", OPCODE_SAR), ("OPCODE_CLZ", OPCODE_CLZ),
    ("OPCODE_JUMP", OPCODE_JUMP), ("OPCODE_JUMPI", OPCODE_JUMPI),
    ("OPCODE_JUMPDEST", OPCODE_JUMPDEST), ("OPCODE_CALLDATALOAD", OPCODE_CALLDATALOAD),
    ("OPCODE_BLOCKHASH", OPCODE_BLOCKHASH), ("OPCODE_COINBASE", OPCODE_COINBASE),
    ("OPCODE_POP", OPCODE_POP), ("OPCODE_MSIZE", OPCODE_MSIZE), ("OPCODE_PC", OPCODE_PC),
    ("OPCODE_GAS", OPCODE_GAS), ("OPCODE_ADDRESS", OPCODE_ADDRESS),
    ("OPCODE_ORIGIN", OPCODE_ORIGIN), ("OPCODE_CALLER", OPCODE_CALLER),
    ("OPCODE_CALLVALUE", OPCODE_CALLVALUE), ("OPCODE_CALLDATASIZE", OPCODE_CALLDATASIZE),
    ("OPCODE_CODESIZE", OPCODE_CODESIZE), ("OPCODE_GASPRICE", OPCODE_GASPRICE),
    ("OPCODE_TIMESTAMP", OPCODE_TIMESTAMP), ("OPCODE_NUMBER", OPCODE_NUMBER),
    ("OPCODE_GASLIMIT", OPCODE_GASLIMIT), ("OPCODE_PREVRANDAO", OPCODE_PREVRANDAO),
    ("OPCODE_DIFFICULTY", OPCODE_PREVRANDAO), ("OPCODE_RETURNDATASIZE", OPCODE_RETURNDATASIZE),
    ("OPCODE_CHAINID", OPCODE_CHAINID), ("OPCODE_SELFBALANCE", OPCODE_SELFBALANCE),
    ("OPCODE_BASEFEE", OPCODE_BASEFEE), ("OPCODE_BLOBBASEFEE", OPCODE_BLOBBASEFEE),
    ("OPCODE_SLOTNUM", OPCODE_SLOTNUM), ("OPCODE_BLOBHASH", OPCODE_BLOBHASH),
    ("OPCODE_PUSH", OPCODE_PUSH), ("OPCODE_PUSH0", OPCODE_PUSH0), ("OPCODE_DUP", OPCODE_DUP),
    ("OPCODE_SWAP", OPCODE_SWAP), ("OPCODE_DUPN", OPCODE_DUPN), ("OPCODE_SWAPN", OPCODE_SWAPN),
    ("OPCODE_EXCHANGE", OPCODE_EXCHANGE), ("OPCODE_TLOAD", OPCODE_TLOAD),
    ("OPCODE_TSTORE", OPCODE_TSTORE), ("OPCODE_RETURNDATACOPY_BASE", OPCODE_RETURNDATACOPY_BASE),
    ("OPCODE_RETURNDATACOPY_PER_WORD", OPCODE_RETURNDATACOPY_PER_WORD),
    ("OPCODE_CALLDATACOPY_BASE", OPCODE_CALLDATACOPY_BASE),
    ("OPCODE_CODECOPY_BASE", OPCODE_CODECOPY_BASE), ("OPCODE_MCOPY_BASE", OPCODE_MCOPY_BASE),
    ("OPCODE_MLOAD_BASE", OPCODE_MLOAD_BASE), ("OPCODE_MSTORE_BASE", OPCODE_MSTORE_BASE),
    ("OPCODE_MSTORE8_BASE", OPCODE_MSTORE8_BASE), ("OPCODE_COPY_PER_WORD", OPCODE_COPY_PER_WORD),
    ("OPCODE_EXP_BASE", OPCODE_EXP_BASE), ("OPCODE_KECCAK256_BASE", OPCODE_KECCAK256_BASE),
    ("OPCODE_KECCAK256_PER_WORD", OPCODE_KECCAK256_PER_WORD), ("OPCODE_LOG_BASE", OPCODE_LOG_BASE),
    ("OPCODE_LOG_DATA_PER_BYTE", OPCODE_LOG_DATA_PER_BYTE), ("OPCODE_LOG_TOPIC", OPCODE_LOG_TOPIC),
    -- The precompiles.
    ("PRECOMPILE_ECRECOVER", Precompiles.Ecrecover.GAS_ECRECOVER),
    ("PRECOMPILE_P256VERIFY", Precompiles.P256Verify.GAS_P256VERIFY),
    ("PRECOMPILE_SHA256_BASE", Precompiles.Sha256.GAS_BASE),
    ("PRECOMPILE_SHA256_PER_WORD", Precompiles.Sha256.GAS_PER_WORD),
    ("PRECOMPILE_RIPEMD160_BASE", Precompiles.Ripemd160.GAS_BASE),
    ("PRECOMPILE_RIPEMD160_PER_WORD", Precompiles.Ripemd160.GAS_PER_WORD),
    ("PRECOMPILE_IDENTITY_BASE", Precompiles.Identity.GAS_BASE),
    ("PRECOMPILE_IDENTITY_PER_WORD", Precompiles.Identity.GAS_PER_WORD),
    ("PRECOMPILE_BLAKE2F_PER_ROUND", Precompiles.Blake2f.GAS_PER_ROUND),
    ("PRECOMPILE_POINT_EVALUATION", Precompiles.PointEvaluation.GAS_POINT_EVALUATION),
    ("PRECOMPILE_BLS_G1ADD", Precompiles.Bls12381.GAS_G1ADD),
    ("PRECOMPILE_BLS_G1MUL", Precompiles.Bls12381.GAS_G1MUL),
    ("PRECOMPILE_BLS_G1MAP", Precompiles.Bls12381.GAS_G1MAP),
    ("PRECOMPILE_BLS_G2ADD", Precompiles.Bls12381.GAS_G2ADD),
    ("PRECOMPILE_BLS_G2MUL", Precompiles.Bls12381.GAS_G2MUL),
    ("PRECOMPILE_BLS_G2MAP", Precompiles.Bls12381.GAS_G2MAP),
    ("PRECOMPILE_ECADD", Precompiles.AltBn128.ecaddGas fork),
    ("PRECOMPILE_ECMUL", Precompiles.AltBn128.ecmulGas fork),
    ("PRECOMPILE_ECPAIRING_BASE", Precompiles.AltBn128.ecpairingGas fork 0),
    ("PRECOMPILE_ECPAIRING_PER_POINT",
      Precompiles.AltBn128.ecpairingGas fork 192 - Precompiles.AltBn128.ecpairingGas fork 0),
    -- The blobs and the gas limit.
    ("PER_BLOB", BlobBaseFee.GAS_PER_BLOB), ("BLOB_BASE_COST", BlobBaseFee.BLOB_BASE_COST),
    ("BLOB_MIN_GASPRICE", BlobBaseFee.MIN_BASE_FEE_PER_BLOB_GAS),
    ("LIMIT_ADJUSTMENT_FACTOR", GasLimit.LIMIT_ADJUSTMENT_FACTOR),
    ("LIMIT_MINIMUM", GasLimit.LIMIT_MINIMUM)]

/-- Each gas constant of the reference at a fork has the value EthLib gives it, by its name.

The branch of the reference names its constants as EthLib does, at every fork from Frontier.

A name of the reference with no entry here is printed, and a name it lacks at a fork is skipped. -/
def gasConstants (branch : Oracle) : Property IO := propertyM do
  pure do
    let mut unknown : List String := []
    let mut compared := 0
    for (fork, name) in branchForks do
      let answer ← branch.ask ["gascosts", name]
      let ours := gasCostsOf fork
      for entry in answer.splitOn "," do
        match entry.splitOn "=" with
        | [constant, value] =>
          match ours.lookup constant with
          | some got =>
            compared := compared + 1
            if toString got ≠ value then
              annotate s!"{constant} at {fork.name}, against {name}"
              toString got === value
          | none => if !unknown.contains constant then unknown := unknown ++ [constant]
        | _ => failWith s!"the oracle gave no constants at {name}: {answer}"
    evalIO (IO.println s!"    {compared} constants compared at {branchForks.length} forks; \
      with no entry in EthLib's table: {unknown}")
    ensure (compared > 2500) s!"only {compared} constants were compared"

/-- A frame whose slot 1 has an original and a current word, warm or cold. -/
def slotFrame (fork : Fork) (original current gas : Nat) (warm : Bool) :
    Except String (Evm fork Nat) := do
  let accounts : List PreAccount := [⟨callerAddress, 0, 10 ^ 18, .empty, []⟩,
    ⟨targetAddress, 1, 10 ^ 9, .empty, [(1, original)]⟩]
  let evm : Evm fork Nat := startFrame
    (messageOf fork false false gas 5 ⟨(List.replicate 40 (0xaa : UInt8)).toArray⟩ .empty)
    (txState accounts) startSubstate gas
  let state ← (evm.state.setStorage targetAddress (word32 1) (BitVec.ofNat 256 current)).mapError
    fun e => reprStr e
  let keys : Std.ExtTreeSet Bytes32 := (∅ : Std.ExtTreeSet Bytes32).insert (word32 1)
  let warmed := evm.substate.accessedStorageKeys.insert targetAddress keys
  let substate := if warm then { evm.substate with accessedStorageKeys := warmed }
    else evm.substate
  pure { evm with state, substate }

/-- SSTORE charges and refunds what the reference does at every class of slot, at every fork.

The original, the current and the new word are each 0, 1 or 2: zero, equal or different, each way.

The slot is cold or warm, and the gas is ample, or 2300 and 2301 at the check of EIP-2200. -/
def sstoreTable (oracle : Oracle) : Property IO := propertyM do
  pure do
    for (fork, name) in forks do
      for original in [0, 1, 2] do
        for current in [0, 1, 2] do
          for new in [0, 1, 2] do
            for warm in [false, true] do
              -- The two pushes before SSTORE cost 6.
              for gas in [100000, 2306, 2307] do
                let want ← oracle.ask ["sstore", name, toString original, toString current,
                  toString new, if warm then "1" else "0", toString gas]
                let code : ByteArray := ⟨#[0x60, UInt8.ofNat new, 0x60, 0x01, 0x55]⟩
                let got := match slotFrame fork original current gas warm with
                  | .error e => s!"no frame: {e}"
                  | .ok evm => match runCode evm code with
                    | .error _ => "halt"
                    | .ok after => showFrame after
                let want := if want.startsWith "halt" then "halt" else want
                if got ≠ want then
                  annotate s!"SSTORE at {fork.name}: original {original}, current {current}, \
                    new {new}, warm {warm}, gas {gas}"
                  got === want

/-- EXP charges for each byte of its exponent, at every length from 0 to 32, at every fork.

The exponent is the least and the greatest of each length, so each boundary of a byte is met.

One frame of each side runs them all, and the power goes to memory, so each step shows it. -/
def expTable (oracle : Oracle) : Property IO := propertyM do
  pure do
    for (fork, name) in forks do
      let _ ← oracle.ask ["frame", name, "100000000", "0"]
      let mut evm := newFrame fork 100000000 false
      for length in List.range 33 do
        for exponent in (if length = 0 then [0] else [256 ^ (length - 1), 256 ^ length - 1]) do
          for base in [0, 1, 2, 3, 2 ^ 256 - 1] do
            let code : ByteArray := ⟨(pushes [base, exponent] ++ [0x0a, 0x60, 0x00, 0x52]).toArray⟩
            let want ← oracle.ask ["op", hex code]
            match runCode evm code with
            | .error e => failWith s!"EXP fails at {fork.name} with {reprStr e}"
            | .ok after =>
              if showFrame after ≠ want then
                annotate s!"EXP at {fork.name}: base {base}, an exponent of {length} bytes"
                showFrame after === want
              evm := { after with running := true }

/-- All but one 64th of the gas, at every gas from 0 to 130 and around the powers of two. -/
def allButOne64th (oracle : Oracle) : Property IO := propertyM do
  pure do
    let edges := (List.range 257).flatMap fun k => [2 ^ k - 1, 2 ^ k, 2 ^ k + 1]
    let values := List.range 131 ++ [191, 192, 193, 4095, 4096, 4097] ++ edges
    let want ← oracle.ask ("allbut64" :: values.map toString)
    showNats (values.map maxMessageCallGas) === want

/-- The gas of a call is the reference's: what it pays, and what the callee gets.

The gas asked is around all but one 64th of what is left after the extra price and the memory.

The gas left is around that price, where the reference stops bounding the gas asked.

The forks are those from Tangerine Whistle, where the rule starts. -/
def callGas (oracle : Oracle) (asked : Bool) : Property IO := propertyM do
  let fork ← forAllWith (·.2) (Gen.element (forks.filter (·.1 ≥ .tangerineWhistle)))
  let value ← forAll (Gen.element [0, 1, 2 ^ 256 - 1])
  let memory ← forAll (Gen.frequency [(2, pure 0), (2, Gen.nat (.linear 0 200))])
  let extra ← forAll (Gen.element [0, 40, 100, 700, 2600, 9700, 34700])
  let left ← forAll (Gen.frequency [(2, genNear (extra + memory)), (3, Gen.nat (.linear 0 200000)),
    (1, (extra + memory + ·) <$> Gen.nat (.constant 0 130))])
  let room := left - memory - extra
  let gas ← forAll (Gen.frequency [(3, genNear (room - room / 64)), (1, genNear room),
    (1, Gen.element [0, 2 ^ 64, 2 ^ 256 - 1]), (2, Gen.nat (.linear 0 200000))])
  let least (percent : Nat) : Nat := if asked then percent else 0
  cover (least 5) "the frame cannot pay the extra price and the memory" (left < extra + memory)
  cover (least 3) "the frame has exactly the extra price and the memory" (left = extra + memory)
  let bound := room - room / 64
  cover (least 10) "the gas asked is above the bound" (extra + memory ≤ left ∧ gas > bound)
  cover (least 3) "the gas asked is the bound" (extra + memory ≤ left ∧ gas = bound)
  cover (least 10) "the gas asked is below the bound" (extra + memory ≤ left ∧ gas < bound)
  cover (least 10) "a call with value, which adds the stipend" (value ≠ 0)
  pure do
    let got := messageCallGas fork.1 (BitVec.ofNat 256 value) gas left memory extra
    let want ← oracle.ask ["callgas", fork.2, toString value, toString gas, toString left,
      toString memory, toString extra]
    s!"{got.cost} {got.subCall}" === want

/-- The price of a multi-scalar multiplication at every number of pairs, by the discount table.

The input is pairs of the point at infinity and the scalar zero, which is valid.

With EthLib's price the reference answers and keeps no gas, and with one less it fails. -/
def msmDiscounts (oracle : Oracle) : Property IO := propertyM do
  pure do
    for (address, size) in [(12, Precompiles.Bls12381.LENGTH_PER_PAIR_G1),
        (14, Precompiles.Bls12381.LENGTH_PER_PAIR_G2)] do
      for pairs in List.range 131 ++ [200, 255, 256, 257] do
        let data : ByteArray := ⟨(List.replicate (pairs * size) (0 : UInt8)).toArray⟩
        let price := (Precompiles.price .fusaka address data).getD 0
        for gas in [price, price - 1] do
          let answer ← oracle.ask ["pre", "osaka", toString address, toString gas, hex data]
          let want := if answer.startsWith "halt" then "halt" else answer
          if precompileEthLib .fusaka address data gas ≠ want then
            annotate s!"{precompileName address} of {pairs} pairs with gas {gas}"
            precompileEthLib .fusaka address data gas === want

/-- The properties that walk a whole table: one case each. -/
def tableProperties (oracle : Oracle) (branch : Option Oracle) : List (String × Property IO) :=
  [("the opcodes of every fork are the reference's", (opcodeSets oracle branch).withTests 1),
   ("each of the 256 bytes is an instruction at a fork as in the reference",
    (byteKinds oracle).withTests 1),
   ("the precompiles of every fork are the reference's",
    (precompileSets oracle branch).withTests 1),
   ("SSTORE at every original, current and new word, at every fork",
    (sstoreTable oracle).withTests 1),
   ("EXP at every byte length of its exponent, at every fork", (expTable oracle).withTests 1),
   ("all but one 64th of every gas", (allButOne64th oracle).withTests 1),
   ("the discount of G1MSM and G2MSM at every number of pairs",
    (msmDiscounts oracle).withTests 1)] ++
  match branch with
  | some branch =>
    [("every gas constant of every fork, by its name", (gasConstants branch).withTests 1)]
  | none => []

end EvmProperty

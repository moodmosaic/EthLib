# The EVM: what the property tests found

The driver is `Property/Evm.lean` with its modules under `Property/Evm/`.
It covers `EthLib/Execution/Evm/`, `Evm/Precompiles/` and `Execution/Fees/`.

```bash
cd tests/property
.venv/bin/pip install --no-deps ethereum-execution==2.20.0   # See oracle/requirements-evm.txt.
lake build evm-property
lake exe evm-property 1000              # Every property, then the findings.
HEDGEHOG_ONLY="a message" lake exe evm-property 5000   # The properties whose name holds a part.
EVM_OPCODE_TABLE=1 lake exe evm-property 1000          # Also the opcodes that ran, by fork.
```

Round 3 replaced the word filter and the `stats` mode of round 1 by `HEDGEHOG_ONLY` and by the labels of each property.

## The references

- `oracle/evm.py` drives the Python execution-specs (EELS), `ethereum-execution` 2.20.0.
  It has every fork from Frontier to BPO2, and was written apart from EthLib.
  A fork that changes only the consensus layer (Phase 0, Altair, Bellatrix) runs against the
  execution fork before it, and Petersburg against Constantinople, which is EELS's Petersburg.
- `oracle/evm_amsterdam.py` drives the branch `forks/amsterdam` of EELS, at the revision that `oracle/requirements-evm.txt` names.
  No release has Glamsterdam, and the fork is not final.
  EthLib's state tracker has the names of that branch, so the two are not fully independent.
- `oracle/evm_inputs.py` builds call data for the precompiles from a recipe, with `py_ecc`,
  `eth-keys` and `cryptography`: a valid input from three numbers, then one rule broken.
- Three models are written from the source text, with no reference process: the arithmetic of the
  Yellow Paper on `Nat` and `Int`, the gas and refund of SLOAD and SSTORE, and the list of EIP-8024.

## What was tested

This is the table of round 1.
Cases are those of `lake exe evm-property 1000`; the last column gives the largest run made.
Every row passes.
Round 3 measured what each row reached, changed the generators and added rows: see "Round 3: the coverage audit" below, which has the table of what is tested now.

| Property | EthLib definitions | Answer from | Cases | Largest run |
| --- | --- | --- | --- | --- |
| A message leaves what the reference leaves | `processMessage`, `processCreateMessage`, `step`, every instruction, calls, creations, SELFDESTRUCT, delegation, precompiles by CALL, at 24 forks | EELS | 1,000 | 40,000 |
| A full stack and a full depth of calls | `Stack.push` at 1024, `genericCall` at depth 1024, the 63/64 rule over 1024 frames | EELS | 100 | 300 |
| A precompile answers bytes as the reference | `Precompiles.run`, `price`, `isPrecompile`; MODEXP lengths and gas of EIP-198, 2565, 7823, 7883; BLAKE2F; the hashes | EELS | 1,000 | 3,000 |
| A precompile answers a near-valid input | ECRECOVER, alt_bn128 add and mul, BLS12-381 add, MSM and maps, P256VERIFY | EELS on inputs from `py_ecc` | 1,000 | 1,000 |
| A pairing precompile answers a near-valid input | alt_bn128 pairing, BLS12-381 pairing, point evaluation | EELS | 100 | 100 |
| Arithmetic and bitwise instructions on integers | `add` to `signextend`, `getByte`, the shifts, `countLeadingZeros` | `Nat`/`Int` model | 10,000 | 20,000 |
| EXP is the power modulo 2^256 | `exp` | `Nat` model | 1,000 | 2,000 |
| The valid jump destinations | `validJumpDestinations`, `isValidJumpDest` | EELS | 1,000 | 2,000 |
| The addresses of CREATE and CREATE2 | `createAddress`, `create2Address` | EELS | 1,000 | 2,000 |
| The growth of memory | `extendMemory`, `memoryGasCost` | EELS | 1,000 | 2,000 |
| The base fee of EIP-1559 | `calculateBaseFeePerGas` | EELS, London to BPO2 | 1,000 | 2,000 |
| A gas limit may follow its parent's | `checkGasLimit` | EELS | 1,000 | 3,000 |
| `fakeExponential` | `fakeExponential` and its fuel | EELS `taylor_exponential` | 1,000 | 2,000 |
| The excess blob gas and the blob gas price | `calcExcessBlobGas`, `getBaseFeePerBlobGas`, `blobSchedule`, the reserve price of EIP-7918 | EELS, Cancun to BPO2 | 1,000 | 2,000 |
| A call at Glamsterdam | `processMessage` with `StateGasMeter`: EIP-8037, 8038, 7708, 7928 reads, 8024, 7843 | EELS branch | 1,000 | 6,000 |
| SLOAD and SSTORE follow the EIPs (`StateMachine`) | `sloadStep`, `sstoreStep`, `sstoreCost`, `sstoreRefund`, warm and cold slots, at 24 forks | model of EIP-2200, 2929, 3529 | 1,000 sequences of up to 40 | 3,000 |
| DUPN, SWAPN and EXCHANGE (`StateMachine`) | `decodeSingle`, `decodePair`, `dupnStep`, `swapnStep`, `exchangeStep` | list model of EIP-8024 | 1,000 sequences of up to 30 | 3,000 |
| A frame steps as the reference (`Command`, madhouse) | `step` on one frame kept over a sequence: gas, pc, memory, whole stack, refund, logs, output | EELS frame stepped in the oracle | 9 forks, 1,000 sequences of up to 15 each | 9 x 1,000 |
| The same scenario in order (`Command`, deterministic) | as above | EELS | 9 forks, 1 sequence each | 9 x 1 |

The whole-program generator is not uniform bytes.
A program is a list of snippets, and most are an instruction with its operands pushed and its
result written to memory, which the program returns at its end.
So the result of each instruction reaches the comparison, and not only the gas.
Operands are drawn by their use: offsets at word boundaries and huge, zero lengths, the code size
limits, the addresses of five accounts and of the precompiles, block numbers around the 256-block
window, gas around the stipend.
One account holds a delegation designator of EIP-7702, to a contract, a precompile, itself or
nothing.
The `stats` mode of round 1 said how runs end: about half succeed, one in twelve creates an account, one in seven writes a log.
Round 3 found that this generator ran few instructions and few opcodes, and replaced it.

## Findings

No property found a place where EthLib computes another value than its reference.
One difference of a tracker was found, with no effect that I could show on a block.

### 1. OPEN: DELEGATECALL and STATICCALL record a read of the running account

- Definition: `finishCall`, `EthLib/Execution/Evm/Call/Instructions.lean:252` (`let evm := recordAccountRead evm current`, before the balance check, for every kind of call).
- Counterexample: at Glamsterdam, a frame at `c0de...` whose code is `PUSH1 0` five times, `PUSH20 a1a1...`, `PUSH1 0`, `DELEGATECALL`, with 100,000 gas.
- EthLib's account reads after the frame: `a1a1...`, `c0de...`.
- The reference's: `a1a1...`.
- The reference reads the balance of the running account only in `call` and `callcode` (`sender_balance = get_account(tx_state, evm.current_target).balance`, `vm/instructions/system.py` of the branch), since only they send value.
  `delegatecall` and `staticcall` have no such read.
- Why OPEN and not BUG: EIP-7928 lists the accounts that a block accesses, and the running account is always among them already.
  It is the recipient of the transaction, the target of the call that started the frame, or an account that a creation wrote.
  So the extra read changes the read set of one frame, and I found no block access list that it changes.
  What would decide it: whether EthLib's theorems or its `eth_simulate` output expose the read set of a frame by itself.
- Command: `HEDGEHOG_ONLY="record no read" lake exe evm-property`, which runs the group that must fail.

### Harness mistakes, each fixed

- A static frame before Byzantium, which no caller can make.
- The reference crashes with `OverflowError` on a MODEXP length near 2^256, where the price is out of reach: counted as a failure of the call.
- The oracle's own reads of the state were counted as reads of EIP-7928.
- An instruction that `keepReads` halts gives a frame with an error, not an `Except` error: the stepping harness now reads it.

## Not covered

- CREATE as the first frame at Glamsterdam (`processCreateMessage` with `StateGasMeter`): only CREATE and CREATE2 inside a call are compared there.
- BPO3, BPO4 and BPO5: the release has no module for them, and EthLib gives them the rules of BPO2.
- Which error halts a frame: only success, revert and halt are compared, since the two sides name errors differently.
- The warm sets after a run are seen only through the gas of later instructions.
- `simulatedLogs`, the precompile overrides of a simulation and `blobGasPrice`: no reference.
- `chainBlobSchedule` and `checkGasLimitAcross` at the London block: they are compositions of tested functions with chain configuration.
- The transaction level (intrinsic gas, refunds at the end, deletion of touched accounts, the warm precompiles): another layer.
- `Measure.lean` holds proofs of termination, with nothing to run.
- Point evaluation is compared on constant polynomials only, whose proof is the point at infinity; a proof of a real blob needs the trusted setup in the oracle.
- BLAKE2F above 300 rounds runs only to the out-of-gas answer: EthLib takes 1.5 s for 65,536 rounds in the test binary.
- `fakeExponential` with a denominator of 0, which the docstring sets to 0 and the EIP leaves undefined.
- A MODEXP with a base, exponent or modulus above 1024 bytes is priced, but its power is computed only up to 200 bytes of body.

## Notes on lean-hedgehog, from round 1

These notes are about the version of round 1, before coverage, the selection and the context in `apply`.
The notes on 0.3.0 are at the end of round 3.

What worked well:

- Integrated shrinking through `do` blocks gave small counterexamples with no shrinker written.
  The DELEGATECALL finding shrank in 31 steps from a 40-snippet program with two callees to one snippet whose operands are all zero but the address.
  A harness bug in the SSTORE model shrank to one transition, `sstore 0 0`, at gas 6, the least gas that pays two pushes.
- `Gen.frequency` with `Gen.element` made edge-biased operands short to write, and `Gen.zip` kept shrinking both sides.
- `StateMachine` with `initState` as a generator: the fork, the slots and the gas of the model are drawn and shrunk with the sequence.
  A system under test that depends on the fork fits as a `Σ fork, ...`.
- `propertyM` with `oracle.ask` in the test: generators stay pure and each shrink asks the oracle again, which is what a stateful oracle needs.
- `forAllWith` to show bytes in hexadecimal.

What was awkward or missing:

- `Command`: the state `σ` is an `outParam`, so it cannot depend on a value of the context.
  A frame indexed by its fork (`Evm fork Nat`) had to be hidden in a `Σ` and checked at each command.
- `Command.apply` does not receive the context, so every command stores the context it was built from.
- `scenario` starts from `default` only.
  There is no generator of the initial state and no hook to start or release a system under test, so the first command that runs starts the frame in the oracle, and nothing releases it.
- Madhouse sequences are 1 to 15 commands, with no argument for the range, as `StateMachine.property` has.
  Bugs that need a long history of one frame are out of reach.
- `Mode.deterministic` with `Command.gen` draws each command once: one test of one random sequence, which says little.
  It is useful only with `Command.fixed`.
- A command whose `check` fails is skipped in silence, and a sequence of skipped commands passes; no count of executed commands is reported.
- No coverage (`classify`, `cover`, `label`).
  I wrote a `stats` mode with `Gen.sample`; it showed that my first generator halted four runs in five, which the passing property did not.
- `Gen.sample` runs at size 30 only; I wrapped the generator in `Gen.resize`.
- `checkGroup` has no selection of properties, and `recheck` is a function to call from code: the report prints `recheck 26 ⟨...⟩ <property>`, and replaying it means editing the driver.
  A filter and a replay from the command line would help a campaign.
- `===` on two long strings prints both with no diff (NEWS lists it as not ported).
  I split results into named fields and compared them one by one.
- No time limit on a test: a reference that hangs, hangs the run with no report of the input.
  I put an alarm in the oracle.
- `StateMachine.applySut` and `invariants` see the model state after the transition only.
  A model that refuses a transition must carry a flag in its state.
- Tests start at size 0 and grow by one, so a property run at 30 or 100 cases, as the slow ones are, sees no size above 29 or 99 and mostly small inputs.

Bugs in the library: none met.

The shrunk counterexamples were minimal or one step from it in every failure I had (about ten, all but one in my harness).
`Gen.element` shrinks to the first element, so in the findings property the opcode shrank to DELEGATECALL because it is listed first, not because it is the smallest in any other sense.

## Round 3: the coverage audit

The properties above were written before lean-hedgehog had coverage, and all passed.
This round asks what they reached.
Each property now names the classes of its cases with `classify` and `label`, and `cover` requires the ones that matter.
For a whole program an observer of `processMessageWith` keeps a trace (`Property/Evm/Trace.lean`): the opcodes whose step succeeded, how each frame ended, each call with its result, each SSTORE by its original, current and new word.
The trace classifies a case only; the comparison with the reference does not read it.

```bash
lake exe evm-property 1000                          # Every property, with the shares.
HEDGEHOG_ONLY="a message leaves" EVM_OPCODE_TABLE=1 lake exe evm-property 1000
```

`EVM_OPCODE_TABLE=1` prints, for each opcode and each fork, the share of the programs of that fork in which the opcode ran.

### Before: what the generators of round 1 reached

These are the shares of `lake exe evm-property 1000` with the generators of round 1 unchanged and only the labels added.
A class under 3% is marked: a property that passes says little about it.
Every property passed.

#### Whole programs: the opcodes

Of the opcodes that a fork has, 1,368 of about 3,300 pairs of fork and opcode ran in no program of the 1,000.
The table gives, for each opcode, the least, the median and the greatest share over the forks that have it, and the number of forks where it ran in no program.
RETURNDATACOPY ran at no fork: every one of its steps failed, out of the bounds of the return data.
JUMP ran in no program at 18 of the 24 forks.
Each DUP and SWAP ran in no program at most forks, and so did each PUSH2 to PUSH32 at about half of them.
SLOTNUM, DUPN, SWAPN and EXCHANGE were in no generated program: the Glamsterdam property drew from a table without them.

| Opcode | Least | Median | Most | Forks at 0% | Opcode | Least | Median | Most | Forks at 0% |
| --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| STOP | 1% | 8% | 19% | 0 of 24 | COINBASE | 0% | 1% | 7% | 11 of 24 |
| ADD | 0% | 4% | 18% | 5 of 24 | TIMESTAMP | 0% | 1% | 7% | 10 of 24 |
| MUL | 0% | 4% | 10% | 4 of 24 | NUMBER | 0% | 3% | 10% | 6 of 24 |
| SUB | 0% | 5% | 20% | 3 of 24 | PREVRANDAO | 0% | 3% | 8% | 9 of 24 |
| DIV | 0% | 4% | 10% | 3 of 24 | GASLIMIT | 0% | 3% | 13% | 8 of 24 |
| SDIV | 0% | 4% | 14% | 5 of 24 | CHAINID | 0% | 1% | 6% | 7 of 16 |
| MOD | 0% | 4% | 14% | 6 of 24 | SELFBALANCE | 0% | 2% | 5% | 2 of 16 |
| SMOD | 0% | 4% | 12% | 3 of 24 | BASEFEE | 0% | 1% | 6% | 4 of 12 |
| ADDMOD | 0% | 3% | 13% | 8 of 24 | BLOBHASH | 1% | 3% | 10% | 0 of 5 |
| MULMOD | 0% | 4% | 12% | 4 of 24 | BLOBBASEFEE | 0% | 0% | 6% | 3 of 5 |
| EXP | 0% | 3% | 9% | 4 of 24 | POP | 0% | 4% | 11% | 3 of 24 |
| SIGNEXTEND | 0% | 3% | 13% | 4 of 24 | MLOAD | 0% | 2% | 9% | 8 of 24 |
| LT | 0% | 4% | 11% | 3 of 24 | MSTORE | 45% | 64% | 77% | 0 of 24 |
| GT | 0% | 3% | 13% | 6 of 24 | MSTORE8 | 0% | 4% | 13% | 2 of 24 |
| SLT | 0% | 4% | 18% | 6 of 24 | SLOAD | 0% | 4% | 11% | 3 of 24 |
| SGT | 0% | 4% | 11% | 6 of 24 | SSTORE | 0% | 3% | 11% | 7 of 24 |
| EQ | 0% | 4% | 10% | 4 of 24 | JUMP | 0% | 0% | 5% | 18 of 24 |
| ISZERO | 0% | 4% | 18% | 3 of 24 | JUMPI | 0% | 7% | 14% | 2 of 24 |
| AND | 0% | 4% | 10% | 4 of 24 | PC | 0% | 1% | 7% | 11 of 24 |
| OR | 0% | 3% | 11% | 5 of 24 | MSIZE | 27% | 46% | 61% | 0 of 24 |
| XOR | 0% | 4% | 13% | 6 of 24 | GAS | 0% | 0% | 11% | 12 of 24 |
| NOT | 0% | 3% | 11% | 5 of 24 | JUMPDEST | 20% | 36% | 50% | 0 of 24 |
| BYTE | 0% | 3% | 16% | 6 of 24 | TLOAD | 0% | 2% | 6% | 1 of 5 |
| SHL | 0% | 4% | 11% | 3 of 18 | TSTORE | 1% | 3% | 4% | 0 of 5 |
| SHR | 0% | 3% | 15% | 4 of 18 | MCOPY | 1% | 2% | 3% | 0 of 5 |
| SAR | 0% | 3% | 10% | 4 of 18 | PUSH0 | 0% | 1% | 4% | 2 of 6 |
| CLZ | 0% | 2% | 7% | 1 of 3 | PUSH1 | 84% | 91% | 100% | 0 of 24 |
| KECCAK256 | 0% | 3% | 13% | 6 of 24 | LOG0 | 0% | 3% | 13% | 9 of 24 |
| ADDRESS | 0% | 1% | 6% | 11 of 24 | LOG1 | 0% | 3% | 14% | 5 of 24 |
| BALANCE | 0% | 3% | 10% | 6 of 24 | LOG2 | 0% | 3% | 9% | 7 of 24 |
| ORIGIN | 0% | 2% | 9% | 7 of 24 | LOG3 | 0% | 2% | 8% | 6 of 24 |
| CALLER | 0% | 2% | 14% | 8 of 24 | LOG4 | 0% | 3% | 12% | 7 of 24 |
| CALLVALUE | 0% | 1% | 10% | 6 of 24 | CREATE | 0% | 3% | 9% | 7 of 24 |
| CALLDATALOAD | 0% | 3% | 18% | 5 of 24 | CALL | 0% | 5% | 9% | 1 of 24 |
| CALLDATASIZE | 0% | 1% | 7% | 9 of 24 | CALLCODE | 0% | 2% | 9% | 7 of 24 |
| CALLDATACOPY | 0% | 4% | 11% | 3 of 24 | RETURN | 33% | 49% | 63% | 0 of 24 |
| CODESIZE | 0% | 0% | 7% | 13 of 24 | DELEGATECALL | 0% | 4% | 20% | 6 of 23 |
| CODECOPY | 0% | 4% | 15% | 2 of 24 | CREATE2 | 0% | 1% | 5% | 6 of 18 |
| GASPRICE | 0% | 1% | 11% | 8 of 24 | STATICCALL | 0% | 3% | 8% | 5 of 19 |
| EXTCODESIZE | 0% | 3% | 16% | 2 of 24 | REVERT | 0% | 3% | 10% | 6 of 19 |
| EXTCODECOPY | 0% | 3% | 18% | 6 of 24 | SELFDESTRUCT | 0% | 5% | 20% | 5 of 24 |
| RETURNDATASIZE | 0% | 1% | 5% | 6 of 19 | PUSH2 to PUSH32 | 0% | 1% | 80% | 318 of 744 |
| RETURNDATACOPY | 0% | 0% | 0% | 19 of 19 | DUP1 to DUP16 | 0% | 0% | 7% | 305 of 384 |
| EXTCODEHASH | 0% | 3% | 7% | 6 of 18 | SWAP1 to SWAP16 | 0% | 0% | 11% | 298 of 384 |
| BLOCKHASH | 0% | 4% | 8% | 3 of 24 |  | | | |  |

#### Whole programs: how they ran and ended

Three programs in ten ran five instructions or fewer, and one in sixteen ran none.
A second SSTORE to a slot, a warm slot, a negative refund and a call that reverts were each under 0.5%.

#### a message leaves what the reference leaves (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 93.3% | ran: PUSH | 5.0% | ran: creation |
| 79.5% | ran: stack and memory | 4.7% | ends: reverts |
| 77.4% | a call | 4.0% | ends: halts, return data out of bounds |
| 68.8% | memory grows | 4.0% | a frame halts: return data out of bounds |
| 54.4% | ran: RETURN and REVERT | 3.2% | ran: KECCAK256 |
| 38.4% | ran: comparison and bitwise | 3.1% | SSTORE sets a clean zero slot |
| 37.5% | ran: control flow | 3.0% | steps of all frames: over 100 |
| 37.2% | steps of the first frame: 21 to 100 | 2.5% **<3%** | CALL succeeds |
| 36.8% | steps of all frames: 21 to 100 | 2.4% **<3%** | DELEGATECALL succeeds |
| 34.0% | ran: arithmetic | 2.4% **<3%** | CREATE succeeds |
| 33.9% | ends: returns data | 2.4% **<3%** | ran: transient storage |
| 32.5% | steps of the first frame: 6 to 20 | 2.3% **<3%** | steps of the first frame: over 100 |
| 32.2% | steps of all frames: 6 to 20 | 1.9% **<3%** | CREATE2 succeeds |
| 31.0% | ran: environment | 1.9% **<3%** | CALLCODE succeeds |
| 26.8% | ends: halts, out of gas | 1.8% **<3%** | STATICCALL succeeds |
| 26.5% | a frame halts: out of gas | 1.5% **<3%** | ends: halts, static violation |
| 21.8% | steps of the first frame: 1 to 5 | 1.5% **<3%** | a frame halts: static violation |
| 21.8% | steps of all frames: 1 to 5 | 0.8% **<3%** | a refund |
| 21.2% | a cold account | 0.8% **<3%** | ends: halts, invalid jump |
| 19.3% | ran: block | 0.8% **<3%** | a frame halts: invalid jump |
| 17.8% | ends: stops with no output | 0.8% **<3%** | CALLCODE halts |
| 15.7% | a log | 0.6% **<3%** | CALL halts |
| 15.7% | ran: LOG | 0.6% **<3%** | DELEGATECALL halts |
| 15.6% | ran: call | 0.5% **<3%** | a frame at depth 2 or more |
| 15.5% | a creation | 0.5% **<3%** | STATICCALL fails in a precompile |
| 12.2% | a frame at depth 1 | 0.4% **<3%** | CALL runs no message |
| 10.2% | ran: DUP | 0.4% **<3%** | STATICCALL halts |
| 9.8% | ran: STOP | 0.4% **<3%** | SSTORE changes a clean slot |
| 9.2% | ran: SWAP | 0.4% **<3%** | CALLCODE runs no message |
| 8.2% | ran: storage | 0.4% **<3%** | CALL fails in a precompile |
| 7.1% | a static call | 0.4% **<3%** | CREATE2 halts |
| 6.8% | a cold slot | 0.4% **<3%** | CREATE2 runs no message |
| 6.2% | steps of the first frame: 0 | 0.3% **<3%** | a warm slot |
| 6.2% | steps of all frames: 0 | 0.3% **<3%** | DELEGATECALL fails in a precompile |
| 5.9% | a frame halts: invalid opcode | 0.3% **<3%** | CALLCODE fails in a precompile |
| 5.7% | a frame halts: stack underflow | 0.3% **<3%** | SSTORE leaves the word |
| 5.5% | a warm account | 0.1% **<3%** | CREATE halts |
| 5.4% | ran: SELFDESTRUCT | 0.1% **<3%** | DELEGATECALL reverts |
| 5.3% | ends: halts, stack underflow | 0.0% **<3%** | a negative refund |
| 5.2% | ends: halts, invalid opcode |  |  |

#### a full stack and a full depth of calls leave what the reference leaves (passed 100 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 54.0% | the first frame ends well | 11.0% | DELEGATECALL halts |
| 54.0% | calls itself | 11.0% | CALLCODE halts |
| 51.0% | stays in the first frame | 9.0% | a call at depth 1024 runs no message |
| 46.0% | fills the stack | 9.0% | reaches depth 1024 |
| 32.0% | a deeper frame halts: out of gas | 8.0% | a deeper frame halts: static violation |
| 29.0% | reaches depth 100 to 1023 | 8.0% | the first frame halts: stack underflow |
| 20.0% | the first frame halts: out of gas | 7.0% | STATICCALL succeeds |
| 18.0% | the first frame halts: stack overflow | 6.0% | CALL halts |
| 15.0% | DELEGATECALL succeeds | 6.0% | CALL succeeds |
| 13.0% | CALLCODE succeeds | 4.0% | DELEGATECALL runs no message |
| 12.0% | STATICCALL halts | 3.0% | STATICCALL runs no message |
| 11.0% | reaches depth 1 to 99 | 2.0% **<3%** | CALLCODE runs no message |

#### a call at Glamsterdam leaves what the branch of the reference leaves (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 92.9% | ran: PUSH | 4.7% | ran: SELFDESTRUCT |
| 78.5% | ran: stack and memory | 4.5% | state gas is spent from the reservoir |
| 68.2% | memory grows | 3.8% | a frame halts: invalid opcode |
| 60.6% | a reservoir | 3.7% | ends: halts, invalid opcode |
| 54.0% | ran: RETURN and REVERT | 3.3% | ends: reverts |
| 40.9% | ran: control flow | 3.3% | ran: KECCAK256 |
| 39.4% | no reservoir | 2.9% **<3%** | the reservoir ends empty, from one that was not |
| 39.4% | ran: comparison and bitwise | 2.6% **<3%** | a frame halts: static violation |
| 38.9% | a log | 2.5% **<3%** | ends: halts, static violation |
| 36.7% | ends: returns data | 2.4% **<3%** | steps of all frames: over 100 |
| 35.0% | steps of the first frame: 6 to 20 | 2.3% **<3%** | SSTORE sets a clean zero slot |
| 34.9% | steps of all frames: 6 to 20 | 2.2% **<3%** | DELEGATECALL succeeds |
| 34.1% | steps of the first frame: 21 to 100 | 2.2% **<3%** | CREATE2 succeeds |
| 33.9% | steps of all frames: 21 to 100 | 2.1% **<3%** | steps of the first frame: over 100 |
| 32.4% | ran: arithmetic | 2.0% **<3%** | CREATE succeeds |
| 30.7% | ran: environment | 1.6% **<3%** | STATICCALL succeeds |
| 25.4% | a frame halts: out of gas | 1.5% **<3%** | CALLCODE succeeds |
| 25.0% | a cold account | 1.4% **<3%** | DELEGATECALL fails in a precompile |
| 23.9% | ends: halts, out of gas | 1.3% **<3%** | CALL succeeds |
| 23.2% | ran: block | 1.2% **<3%** | STATICCALL fails in a precompile |
| 22.9% | steps of the first frame: 1 to 5 | 1.2% **<3%** | CALL fails in a precompile |
| 22.9% | steps of all frames: 1 to 5 | 1.0% **<3%** | STATICCALL halts |
| 18.0% | ends: stops with no output | 1.0% **<3%** | CALLCODE fails in a precompile |
| 14.8% | ran: LOG | 0.6% **<3%** | SSTORE changes a clean slot |
| 12.3% | ran: call | 0.6% **<3%** | CREATE runs no message |
| 9.1% | a frame at depth 1 | 0.6% **<3%** | ends: halts, invalid jump |
| 8.7% | ran: DUP | 0.6% **<3%** | a frame halts: invalid jump |
| 8.5% | ran: SWAP | 0.4% **<3%** | CALL halts |
| 8.1% | a cold slot | 0.4% **<3%** | DELEGATECALL halts |
| 7.3% | ran: STOP | 0.4% **<3%** | CALL runs no message |
| 7.2% | ran: transient storage | 0.3% **<3%** | a warm slot |
| 6.9% | ran: storage | 0.3% **<3%** | CALLCODE halts |
| 6.7% | a warm account | 0.3% **<3%** | SSTORE leaves the word |
| 6.0% | a frame halts: stack underflow | 0.2% **<3%** | a frame at depth 2 or more |
| 6.0% | ran: creation | 0.2% **<3%** | CREATE2 runs no message |
| 5.9% | steps of the first frame: 0 | 0.2% **<3%** | CREATE halts |
| 5.9% | steps of all frames: 0 | 0.1% **<3%** | ends: halts, invalid immediate |
| 5.7% | ends: halts, stack underflow | 0.1% **<3%** | a frame halts: invalid immediate |
| 5.5% | ends: halts, return data out of bounds | 0.0% **<3%** | a refund |
| 5.5% | a frame halts: return data out of bounds | 0.0% **<3%** | a negative refund |

#### The precompiles

The property on bytes spends six cases in ten on MODEXP and two on BLAKE2F.
SHA-256 answered in 15 cases of 1,000, RIPEMD-160 in 8 and IDENTITY in 7, so the word rounding of their prices was all but untested.

#### a precompile answers bytes as the reference (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 35.8% | gas: plenty | 0.9% **<3%** | G1ADD: no precompile at the fork |
| 34.2% | MODEXP body shorter than the lengths say | 0.9% **<3%** | MAP_FP2_TO_G2: no precompile at the fork |
| 30.0% | MODEXP base length: 1 to 32 | 0.9% **<3%** | MAP_FP_TO_G1: no precompile at the fork |
| 28.8% | MODEXP exponent length: 1 to 32 | 0.8% **<3%** | BN_PAIRING: refuses, invalidInputLength |
| 28.1% | MODEXP modulus length: 1 to 32 | 0.8% **<3%** | RIPEMD160: answers |
| 26.6% | gas: the price | 0.8% **<3%** | address 257: no precompile at the fork |
| 23.9% | MODEXP at the gas of EIP-2565 | 0.7% **<3%** | ECRECOVER: answers nothing |
| 20.7% | gas: one less than the price | 0.7% **<3%** | G2MSM: refuses, invalidInputLength |
| 18.8% | MODEXP: refuses, outOfGas | 0.7% **<3%** | IDENTITY: answers |
| 13.3% | MODEXP at the gas of EIP-7883 | 0.7% **<3%** | POINT_EVALUATION: no precompile at the fork |
| 10.9% | MODEXP modulus length: 0 | 0.6% **<3%** | BLS_PAIRING: no precompile at the fork |
| 10.2% | MODEXP: answers zero | 0.6% **<3%** | G2ADD: no precompile at the fork |
| 9.5% | MODEXP exponent length: 0 | 0.5% **<3%** | IDENTITY: refuses, outOfGas |
| 9.4% | MODEXP at the gas of EIP-198 | 0.5% **<3%** | BN_ADD: answers zero |
| 9.1% | gas: one more than the price | 0.5% **<3%** | MAP_FP2_TO_G2: refuses, invalidInputLength |
| 8.8% | MODEXP base length: 33 to 1024 | 0.5% **<3%** | G1MSM: refuses, invalidInputLength |
| 8.6% | MODEXP exponent length: 33 to 1024 | 0.4% **<3%** | BN_MUL: refuses, invalidFieldElement |
| 8.2% | BLAKE2F: answers | 0.4% **<3%** | BN_MUL: no precompile at the fork |
| 7.8% | gas: none | 0.4% **<3%** | BN_PAIRING: refuses, outOfGas |
| 7.6% | MODEXP: answers | 0.4% **<3%** | RIPEMD160: refuses, outOfGas |
| 6.8% | MODEXP header cut short | 0.4% **<3%** | POINT_EVALUATION: refuses, invalidInputLength |
| 6.8% | MODEXP base length: 0 | 0.4% **<3%** | SHA256: refuses, outOfGas |
| 6.8% | MODEXP before Byzantium | 0.4% **<3%** | G1ADD: refuses, invalidInputLength |
| 6.8% | MODEXP: no precompile at the fork | 0.4% **<3%** | G2ADD: refuses, invalidInputLength |
| 6.6% | MODEXP modulus length: 33 to 1024 | 0.4% **<3%** | G2MSM: no precompile at the fork |
| 6.2% | MODEXP base length: 2^32 or more | 0.3% **<3%** | MODEXP body longer than the lengths say |
| 5.9% | MODEXP modulus length: 2^32 or more | 0.3% **<3%** | MAP_FP_TO_G1: refuses, invalidInputLength |
| 5.9% | MODEXP: answers nothing | 0.3% **<3%** | BLS_PAIRING: refuses, invalidInputLength |
| 5.1% | MODEXP exponent length: 2^32 or more | 0.3% **<3%** | BN_ADD: refuses, outOfGas |
| 4.1% | MODEXP: refuses, lengthTooLarge | 0.2% **<3%** | BN_ADD: refuses, invalidFieldElement |
| 4.1% | BLAKE2F: refuses, invalidInputLength | 0.2% **<3%** | ECRECOVER: refuses, outOfGas |
| 4.0% | BLAKE2F: no precompile at the fork | 0.2% **<3%** | BN_ADD: no precompile at the fork |
| 2.4% **<3%** | address 255: no precompile at the fork | 0.2% **<3%** | P256VERIFY: answers nothing |
| 2.2% **<3%** | BLAKE2F: refuses, outOfGas | 0.1% **<3%** | BN_PAIRING: answers |
| 1.9% **<3%** | MODEXP modulus length: 1025 to 2^32 | 0.1% **<3%** | BN_MUL: refuses, outOfGas |
| 1.8% **<3%** | BLAKE2F: refuses, invalidFlag | 0.1% **<3%** | BN_MUL: answers zero |
| 1.6% **<3%** | MODEXP base length: 1025 to 2^32 | 0.1% **<3%** | BN_ADD: refuses, notOnCurve |
| 1.5% **<3%** | SHA256: answers | 0.1% **<3%** | BN_MUL: refuses, notOnCurve |
| 1.4% **<3%** | MODEXP exponent length: 1025 to 2^32 | 0.1% **<3%** | BN_PAIRING: no precompile at the fork |
| 1.3% **<3%** | address 18: no precompile at the fork | 0.1% **<3%** | IDENTITY: answers nothing |
| 1.3% **<3%** | G1MSM: no precompile at the fork | 0.1% **<3%** | P256VERIFY: refuses, outOfGas |
| 1.3% **<3%** | P256VERIFY: no precompile at the fork | 0.1% **<3%** | IDENTITY: answers zero |
| 1.2% **<3%** | address 0: no precompile at the fork |  |  |

The property on near-valid inputs draws one of ten precompiles, one of fifteen mutations, a fork and a gas.
Each pair of precompile and mutation whose body ran had 1 to 4 cases of 1,000: none reached 0.5%.
The table leaves those 260 classes out and keeps the outcome of each precompile.

#### a precompile answers a near-valid input as the reference (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 36.4% | gas: plenty | 1.2% **<3%** | BN_ADD: refuses, notOnCurve |
| 30.5% | gas: the price | 1.1% **<3%** | G2MSM: refuses, outOfGas |
| 16.0% | gas: one less than the price | 1.0% **<3%** | MAP_FP2_TO_G2: refuses, outOfGas |
| 8.8% | gas: one more than the price | 1.0% **<3%** | G1MSM: refuses, outOfGas |
| 8.3% | gas: none | 1.0% **<3%** | MAP_FP2_TO_G2: refuses, invalidFieldElement |
| 5.5% | BN_ADD: answers | 1.0% **<3%** | G2ADD: refuses, invalidInputLength |
| 5.3% | P256VERIFY: no precompile at the fork | 0.9% **<3%** | MAP_FP_TO_G1: refuses, invalidFieldElement |
| 5.3% | MAP_FP2_TO_G2: no precompile at the fork | 0.9% **<3%** | G1ADD: refuses, outOfGas |
| 5.1% | G2MSM: no precompile at the fork | 0.9% **<3%** | P256VERIFY: refuses, outOfGas |
| 5.1% | BN_MUL: answers | 0.8% **<3%** | MAP_FP2_TO_G2: refuses, invalidInputLength |
| 5.0% | MAP_FP_TO_G1: no precompile at the fork | 0.8% **<3%** | MAP_FP_TO_G1: refuses, outOfGas |
| 5.0% | G1MSM: no precompile at the fork | 0.8% **<3%** | G1MSM: answers zero |
| 4.2% | G2ADD: no precompile at the fork | 0.7% **<3%** | BN_MUL: refuses, invalidFieldElement |
| 3.9% | G1ADD: no precompile at the fork | 0.7% **<3%** | MAP_FP_TO_G1: refuses, invalidInputLength |
| 3.7% | ECRECOVER: answers nothing | 0.5% **<3%** | G2MSM: refuses, invalidFieldElement |
| 3.4% | ECRECOVER: answers | 0.5% **<3%** | G2ADD: refuses, invalidFieldElement |
| 2.6% **<3%** | BN_ADD: refuses, outOfGas | 0.4% **<3%** | G2MSM: answers zero |
| 2.5% **<3%** | G1MSM: answers | 0.4% **<3%** | MAP_FP2_TO_G2: refuses, invalidPadding |
| 2.1% **<3%** | P256VERIFY: answers nothing | 0.4% **<3%** | G1MSM: refuses, invalidFieldElement |
| 2.1% **<3%** | ECRECOVER: refuses, outOfGas | 0.4% **<3%** | BN_MUL: refuses, notOnCurve |
| 2.1% **<3%** | G1ADD: answers | 0.3% **<3%** | G2MSM: refuses, notOnCurve |
| 2.0% **<3%** | BN_MUL: refuses, outOfGas | 0.3% **<3%** | G1ADD: refuses, invalidFieldElement |
| 1.9% **<3%** | MAP_FP_TO_G1: answers | 0.3% **<3%** | BN_ADD: no precompile at the fork |
| 1.9% **<3%** | G2MSM: answers | 0.3% **<3%** | BN_ADD: answers zero |
| 1.9% **<3%** | MAP_FP2_TO_G2: answers | 0.3% **<3%** | BN_MUL: no precompile at the fork |
| 1.7% **<3%** | G1MSM: refuses, invalidInputLength | 0.2% **<3%** | G1ADD: refuses, invalidPadding |
| 1.6% **<3%** | G2ADD: answers | 0.2% **<3%** | G1MSM: refuses, notInSubgroup |
| 1.5% **<3%** | P256VERIFY: answers | 0.2% **<3%** | G2MSM: refuses, invalidPadding |
| 1.5% **<3%** | BN_MUL: answers zero | 0.2% **<3%** | G2ADD: refuses, invalidPadding |
| 1.3% **<3%** | BN_ADD: refuses, invalidFieldElement | 0.2% **<3%** | G1MSM: refuses, invalidPadding |
| 1.3% **<3%** | G1ADD: refuses, invalidInputLength | 0.1% **<3%** | MAP_FP_TO_G1: refuses, invalidPadding |
| 1.2% **<3%** | G2MSM: refuses, invalidInputLength | 0.1% **<3%** | G2ADD: answers zero |
| 1.2% **<3%** | G2ADD: refuses, outOfGas |  |  |

#### a pairing precompile answers a near-valid input as the reference (passed 100 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 44.0% | gas: plenty | 4.0% | BN_PAIRING: refuses, invalidFieldElement |
| 25.0% | gas: the price | 3.0% | BLS_PAIRING: refuses, outOfGas |
| 18.0% | gas: one less than the price | 3.0% | POINT_EVALUATION: refuses, versionedHashMismatch |
| 15.0% | POINT_EVALUATION: no precompile at the fork | 3.0% | BLS_PAIRING: refuses, invalidInputLength |
| 15.0% | BN_PAIRING: answers | 3.0% | BN_PAIRING: refuses, notOnCurve |
| 11.0% | BLS_PAIRING: no precompile at the fork | 2.0% **<3%** | BN_PAIRING: answers zero |
| 9.0% | POINT_EVALUATION: answers | 2.0% **<3%** | BN_PAIRING: refuses, invalidInputLength |
| 8.0% | gas: none | 2.0% **<3%** | POINT_EVALUATION: refuses, proofRejected |
| 7.0% | POINT_EVALUATION: refuses, outOfGas | 2.0% **<3%** | BLS_PAIRING: refuses, invalidFieldElement |
| 6.0% | BN_PAIRING: refuses, outOfGas | 1.0% **<3%** | BLS_PAIRING: refuses, notOnCurve |
| 5.0% | gas: one more than the price | 1.0% **<3%** | BLS_PAIRING: answers zero |
| 5.0% | BLS_PAIRING: answers | 1.0% **<3%** | BN_PAIRING: no precompile at the fork |
| 4.0% | POINT_EVALUATION: refuses, invalidInputLength | 1.0% **<3%** | POINT_EVALUATION: refuses, invalidFieldElement |

#### The functions under the instructions

SDIV of `-2^255` by `-1` did not occur in 10,000 cases.
A range of memory that ends exactly at the size, or one byte past it, occurred in one case of 1,000.

#### arithmetic and bitwise instructions on integers (passed 10000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 68.2% | a shift of 1 to 255 | 29.7% | CLZ of a word with its top bit |
| 63.4% | MUL wraps | 29.5% | SIGNEXTEND of byte 0 to 30, sign clear |
| 62.2% | MULMOD has a product of 2^256 or more, and a modulus | 29.3% | SMOD of a negative dividend |
| 55.1% | SIGNEXTEND of byte 31 or more | 20.7% | a shift above 256 |
| 53.6% | BYTE of index 32 or more | 15.4% | SIGNEXTEND of byte 0 to 30, sign set |
| 49.7% | SUB borrows | 9.5% | a shift of 256 |
| 46.4% | BYTE of index 0 to 31 | 2.1% **<3%** | a modulus of 0 |
| 40.7% | SDIV of signs that differ | 1.8% **<3%** | CLZ of 0 |
| 33.6% | ADD wraps | 1.7% **<3%** | a divisor of 0 |
| 32.9% | ADDMOD has a sum of 2^256 or more, and a modulus | 1.6% **<3%** | a shift of 0 |
| 29.9% | SMOD of a negative divisor | 0.0% **<3%** | SDIV of -2^255 by -1 |
| 29.7% | SAR of a negative word |  |  |

#### EXP is the power modulo 2^256 (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 82.1% | exponent of 1 byte | 14.0% | base 1 |
| 36.1% | the power wraps | 6.1% | exponent of 32 bytes |
| 35.3% | an odd base | 5.5% | exponent of 9 to 31 bytes |
| 26.1% | an even base | 3.5% | exponent of 2 to 8 bytes |
| 24.6% | base 0 | 2.8% **<3%** | exponent 0 |

#### the valid jump destinations (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 86.1% | a PUSH whose data may run past the code | 21.1% | a PUSH32 |
| 79.0% | a JUMPDEST byte in push data | 12.2% | no JUMPDEST byte |
| 58.8% | a valid destination | 6.8% | no code |
| 21.5% | a PUSH0 |  |  |

#### the addresses of CREATE and CREATE2 (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 41.2% | nonce of one byte, itself | 5.6% | a nonce of 2^64 - 1 |
| 23.5% | nonce of 8 bytes | 2.1% **<3%** | init code over 55 bytes |
| 19.3% | nonce of 1 bytes | 1.0% **<3%** | nonce of 3 bytes |
| 13.7% | a sender that starts with a zero byte | 0.8% **<3%** | nonce of 7 bytes |
| 6.2% | nonce 0 | 0.7% **<3%** | nonce of 4 bytes |
| 6.1% | no init code | 0.6% **<3%** | nonce of 6 bytes |
| 6.1% | nonce of 2 bytes | 0.6% **<3%** | nonce of 5 bytes |

#### the growth of memory (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 79.6% | no growth | 3.9% | a later range grows more |
| 59.8% | 0 ranges | 2.2% **<3%** | a size of 2^22 or more |
| 28.3% | 1 ranges | 1.9% **<3%** | a range that ends at a word |
| 25.8% | the quadratic part is above 0 | 1.0% **<3%** | a range that ends one past a word |
| 14.2% | a range inside the memory | 0.7% **<3%** | growth of a word |
| 13.5% | a range of size 0 | 0.5% **<3%** | a range of size 0 at a huge start |
| 11.6% | 2 ranges | 0.3% **<3%** | 3 ranges |
| 11.3% | an empty memory before | 0.1% **<3%** | a range that ends one past the size |
| 10.1% | growth of words | 0.0% **<3%** | a range that ends at the size |
| 9.6% | growth of 2^16 bytes or more |  |  |

#### The fee functions

#### the base fee of EIP-1559 (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 43.8% | the parent is below its target | 11.7% | the rise is more than 1 |
| 30.0% | the parent is at its target | 11.1% | the parent is full |
| 26.2% | the parent is above its target | 9.5% | a base fee of 0 |
| 23.0% | the fall is 0 | 4.6% | one above the target |
| 20.8% | the fall is more than 0 | 3.1% | one below the target |
| 17.6% | the parent is empty | 2.9% **<3%** | the rise is an eighth, the most |
| 14.5% | the rise is the least, 1 |  |  |

#### a gas limit may follow its parent's (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 48.4% | refused: too high | 14.3% | at 5000 |
| 36.7% | refused: too low | 9.1% | accepted |
| 28.7% | at the upper bound, refused | 5.8% | refused: below 5000 |
| 27.1% | at the lower bound, refused | 4.9% | one above the lower bound |
| 22.6% | a parent below 1024, with no room | 4.6% | one below the upper bound |
| 19.9% | the limit of the parent | 3.1% | at 4999 |

#### fakeExponential is fake_exponential of EIP-4844 (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 70.6% | ratio 1 to 60 | 5.0% | ratio below 1 |
| 69.3% | factor 1 | 1.9% **<3%** | numerator 0 |
| 67.3% | a denominator of a fork | 1.4% **<3%** | a denominator of 1 |
| 29.7% | factor above 1 | 1.0% **<3%** | factor 0 |
| 22.5% | ratio above 60 |  |  |

#### the excess blob gas and the blob gas price (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 72.7% | the blob gas price is 1 | 19.9% | at prague |
| 44.4% | above the target: the rule of EIP-4844 | 18.6% | below the target: the excess is 0 |
| 33.8% | an excess of 0 in the parent | 17.7% | at bpo2 |
| 22.2% | the reserve price of EIP-7918 rules | 14.8% | at the target: the excess is 0 |
| 21.6% | the reserve price meets the blob base fee | 8.1% | the parent used the most blobs |
| 21.1% | at bpo1 | 6.7% | the parent used no blob |
| 20.7% | at osaka | 1.0% **<3%** | one below the target |
| 20.6% | at cancun |  |  |

#### The state machines

The shares of a state machine are of sequences: the share of the sequences in which the class occurred at least once.

#### SLOAD and SSTORE follow the model of the EIPs (StateMachine) (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 57.7% | the refund rises | 15.6% | SSTORE sets a clean zero slot, cold |
| 53.5% | London and later | 15.4% | SSTORE changes a clean slot, warm |
| 33.9% | SLOAD | 14.8% | SSTORE clears a clean slot, warm |
| 32.1% | SLOAD cold | 13.2% | SSTORE sets a clean zero slot, warm |
| 30.4% | SLOAD warm | 12.9% | SSTORE resets a dirty slot to its word |
| 29.6% | SSTORE leaves the word, cold | 12.2% | SSTORE clears a dirty slot, warm |
| 28.6% | SSTORE leaves the word, warm | 12.0% | before Tangerine Whistle |
| 26.7% | SSTORE leaves the word | 11.7% | SSTORE writes a slot that was cleared, warm |
| 22.0% | SSTORE out of gas | 11.2% | Istanbul and Muir Glacier |
| 21.7% | the refund falls | 11.0% | SSTORE resets a dirty slot to its zero, warm |
| 20.8% | SSTORE clears a clean slot, cold | 8.8% | SSTORE changes a dirty slot, warm |
| 20.6% | SSTORE changes a clean slot | 8.5% | SLOAD out of gas |
| 20.4% | SSTORE changes a clean slot, cold | 7.5% | SSTORE writes a slot that was cleared |
| 19.5% | SSTORE clears a clean slot | 7.4% | SSTORE resets a dirty slot to its zero |
| 19.3% | Tangerine Whistle to Petersburg | 7.4% | SSTORE clears a dirty slot |
| 17.3% | SSTORE sets a clean zero slot | 5.4% | SSTORE changes a dirty slot |
| 17.0% | SSTORE refused at the stipend | 4.0% | Berlin |
| 16.9% | SSTORE resets a dirty slot to its word, warm |  |  |

#### DUPN, SWAPN and EXCHANGE follow the list of EIP-8024 (StateMachine) (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 52.7% | EXCHANGE runs | 31.6% | SWAPN runs |
| 48.1% | DUPN refused: the stack is too short | 26.6% | DUPN runs |
| 46.6% | SWAPN refused: the stack is too short | 24.6% | EXCHANGE refused: the stack is too short |
| 41.7% | PUSH runs | 7.0% | it reaches the deepest item |
| 41.3% | EXCHANGE refused: the immediate encodes nothing | 5.7% | DUPN refused: the stack is full |
| 34.5% | DUPN refused: the immediate encodes nothing | 5.5% | it reaches one past the deepest item |
| 32.2% | SWAPN refused: the immediate encodes nothing | 3.5% | PUSH refused |

#### The frame scenario

The nine forks give similar shares; these are London's.
A family ran in about three sequences in ten, so one of its eleven or so instructions in about three in a hundred.
SWAP ran in 2.5% of the sequences and DUP in 8.9%.
Half of the STORAGE commands were TLOAD and TSTORE, which London does not have.

#### a frame steps as the reference at london (Command, madhouse) (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 41.9% | MEMORY runs | 5.4% | ENVIRONMENT halts: invalid opcode |
| 30.1% | STORAGE halts: invalid opcode | 3.5% | DUP halts: stack underflow |
| 29.7% | LOG runs | 2.5% **<3%** | SWAP runs |
| 29.3% | STACK runs | 2.3% **<3%** | BITWISE halts: invalid opcode |
| 29.2% | STORAGE runs | 2.1% **<3%** | MEMORY halts: out of gas |
| 29.1% | ARITHMETIC runs | 1.6% **<3%** | SWAP halts: stack underflow |
| 28.2% | BITWISE runs | 1.5% **<3%** | END halts: out of gas |
| 28.0% | ENVIRONMENT runs | 1.5% **<3%** | LOG halts: out of gas |
| 25.6% | MEMORY grows memory | 1.0% **<3%** | ENVIRONMENT grows memory |
| 17.7% | LOG grows memory | 0.1% **<3%** | ENVIRONMENT halts: out of gas |
| 16.1% | END halts: revert | 0.0% **<3%** | BITWISE grows memory |
| 15.3% | a DUP or SWAP ran, at least 5% | 0.0% **<3%** | STORAGE grows memory |
| 15.0% | END runs | 0.0% **<3%** | ARITHMETIC grows memory |
| 8.9% | DUP runs | 0.0% **<3%** | STACK grows memory |
| 8.8% | END grows memory | 0.0% **<3%** | DUP grows memory |
| 7.7% | MEMORY halts: invalid opcode | 0.0% **<3%** | SWAP grows memory |
| 7.0% | MEMORY halts: return data out of bounds |  |  |

### What changed in the generators

- A program is now a body of snippets, at most one spoiler at a drawn place, and an ending (`Property/Evm/Program.lean`).
  A snippet pushes its operands and keeps or drops its result, so the stack is as it found it and the program runs every snippet up to its ending.
  In round 1 any snippet could halt the frame: an offset of `2^64` among the operands, an opcode of another fork, a DUP over too few words.
- The body draws from a list of templates, one for each opcode of the fork and one for each idiom, each in or out, where round 1 drew forty times among sixty.
  So no opcode waits for a lucky draw: each runs in about a quarter of the programs of each fork.
- The idioms: DUP and SWAP over words of their own, a jump over bytes that never run, JUMPI taken and not, a loop that counts down, a call and then its return data, a creation and then a use of the new address, writes and a read of one slot.
- A spoiler halts the frame by one named rule: a stack one word short, a full stack, a jump into push data or past `2^16`, `2^32`, `2^64` and `2^255` from a true JUMPDEST, an opcode of a later fork with its operands, memory past any gas, RETURNDATACOPY one byte past the data or with a sum of `2^256`, an immediate of EIP-8024 that encodes nothing.
- An ending is RETURN of the whole memory, STOP, the end of the code, RETURN or REVERT of a range, or SELFDESTRUCT.
- The gas is ample, or a part of what EthLib uses with ample gas, or exactly that, one less and one more, so gas runs out at any instruction and at the last unit.
  EthLib only places the draw there: the reference decides what the gas buys.
- The block has numbers near the top of their types in one case of four: a chain identifier of `2^64 - 1`, a number above `2^63`, a time above `2^255`, a difficulty above `2^200`, a base fee above `2^100`.
  An instruction that cut one of them to 64 bits would not show on block 1000.
  The excess blob gas is one at which each blob schedule gives another price, where round 1 had one that gave 1 at every fork.
- The forks are drawn each as often as another, an empty account exists, each of the four slots starts at 0, 1 or 2, and the nonce of the program is now and then `2^64 - 2` or `2^64 - 1`, the limit of EIP-2681.
- A property of its own runs programs of calls and creations that end by SELFDESTRUCT, whose rules change at five forks.
- Each precompile has a property of its own, with forks that have it, so a mutation of its input has tens of cases and not one.
- The frame scenario runs at each of the 24 forks.
  Its commands are a snippet of the whole programs, an instruction whose result stays on the stack, DUP, SWAP and POP on the stack that is there, an instruction on the words of the stack, an instruction on a range that ends around the size of the memory, and a spoiler.
  `next` runs a command in EthLib's frame, so `buildIn` sees the stack and the memory the next command meets.
- Each property has `cover` minimums, at about a third of the shares below, asked of a run of 500 cases or more.

### After: what the generators reach now

These are the shares of `lake exe evm-property 1000` with the generators of this round.
A class with a minimum shows it, and the property fails when a run of 500 cases or more stays under it.
Every property passes.

#### Whole programs: the opcodes

The run had 2000 programs at 25 forks; the least share is 3% (REVERT at petersburg); 0 opcodes of a fork ran in no program.
The programs of Glamsterdam are those of the property against the branch, which now draws SLOTNUM, DUPN, SWAPN and EXCHANGE.

| Opcode | Least | Median | Most | Forks at 0% | Opcode | Least | Median | Most | Forks at 0% |
| --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| STOP | 24% | 48% | 61% | 0 of 25 | NUMBER | 15% | 28% | 43% | 0 of 25 |
| ADD | 17% | 29% | 40% | 0 of 25 | PREVRANDAO | 10% | 27% | 38% | 0 of 25 |
| MUL | 10% | 25% | 45% | 0 of 25 | GASLIMIT | 12% | 27% | 38% | 0 of 25 |
| SUB | 36% | 48% | 64% | 0 of 25 | CHAINID | 18% | 29% | 46% | 0 of 17 |
| DIV | 12% | 25% | 41% | 0 of 25 | SELFBALANCE | 14% | 25% | 42% | 0 of 17 |
| SDIV | 6% | 26% | 37% | 0 of 25 | BASEFEE | 17% | 28% | 40% | 0 of 13 |
| MOD | 10% | 26% | 38% | 0 of 25 | BLOBHASH | 21% | 25% | 35% | 0 of 6 |
| SMOD | 18% | 28% | 38% | 0 of 25 | BLOBBASEFEE | 16% | 26% | 36% | 0 of 6 |
| ADDMOD | 15% | 28% | 37% | 0 of 25 | SLOTNUM | 25% | 25% | 25% | 0 of 1 |
| MULMOD | 18% | 29% | 38% | 0 of 25 | POP | 82% | 94% | 100% | 0 of 25 |
| EXP | 13% | 25% | 34% | 0 of 25 | MLOAD | 17% | 28% | 57% | 0 of 25 |
| SIGNEXTEND | 17% | 25% | 38% | 0 of 25 | MSTORE | 86% | 95% | 100% | 0 of 25 |
| LT | 15% | 27% | 41% | 0 of 25 | MSTORE8 | 18% | 32% | 46% | 0 of 25 |
| GT | 18% | 28% | 37% | 0 of 25 | SLOAD | 37% | 48% | 65% | 0 of 25 |
| SLT | 12% | 25% | 38% | 0 of 25 | SSTORE | 42% | 55% | 68% | 0 of 25 |
| SGT | 15% | 26% | 42% | 0 of 25 | JUMP | 23% | 33% | 46% | 0 of 25 |
| EQ | 15% | 27% | 38% | 0 of 25 | JUMPI | 30% | 43% | 58% | 0 of 25 |
| ISZERO | 17% | 37% | 56% | 0 of 25 | PC | 17% | 35% | 52% | 0 of 25 |
| AND | 16% | 27% | 35% | 0 of 25 | MSIZE | 37% | 46% | 60% | 0 of 25 |
| OR | 21% | 27% | 40% | 0 of 25 | GAS | 24% | 31% | 46% | 0 of 25 |
| XOR | 15% | 28% | 57% | 0 of 25 | JUMPDEST | 39% | 54% | 79% | 0 of 25 |
| NOT | 10% | 26% | 44% | 0 of 25 | TLOAD | 31% | 41% | 45% | 0 of 6 |
| BYTE | 17% | 26% | 44% | 0 of 25 | TSTORE | 39% | 43% | 54% | 0 of 6 |
| SHL | 17% | 28% | 58% | 0 of 19 | MCOPY | 21% | 23% | 34% | 0 of 6 |
| SHR | 18% | 29% | 35% | 0 of 19 | PUSH0 | 16% | 21% | 29% | 0 of 7 |
| SAR | 17% | 25% | 43% | 0 of 19 | PUSH1 | 93% | 100% | 100% | 0 of 25 |
| CLZ | 15% | 28% | 37% | 0 of 4 | LOG0 | 14% | 26% | 40% | 0 of 25 |
| KECCAK256 | 11% | 28% | 37% | 0 of 25 | LOG1 | 14% | 23% | 41% | 0 of 25 |
| ADDRESS | 16% | 31% | 40% | 0 of 25 | LOG2 | 13% | 27% | 43% | 0 of 25 |
| BALANCE | 19% | 31% | 46% | 0 of 25 | LOG3 | 17% | 25% | 37% | 0 of 25 |
| ORIGIN | 18% | 30% | 41% | 0 of 25 | LOG4 | 5% | 28% | 37% | 0 of 25 |
| CALLER | 16% | 28% | 53% | 0 of 25 | DUPN | 28% | 28% | 28% | 0 of 1 |
| CALLVALUE | 15% | 24% | 38% | 0 of 25 | SWAPN | 30% | 30% | 30% | 0 of 1 |
| CALLDATALOAD | 16% | 26% | 43% | 0 of 25 | EXCHANGE | 27% | 27% | 27% | 0 of 1 |
| CALLDATASIZE | 15% | 28% | 38% | 0 of 25 | CREATE | 13% | 31% | 48% | 0 of 25 |
| CALLDATACOPY | 15% | 27% | 45% | 0 of 25 | CALL | 22% | 34% | 53% | 0 of 25 |
| CODESIZE | 11% | 29% | 41% | 0 of 25 | CALLCODE | 21% | 29% | 45% | 0 of 25 |
| CODECOPY | 17% | 25% | 38% | 0 of 25 | RETURN | 24% | 41% | 52% | 0 of 25 |
| GASPRICE | 15% | 28% | 40% | 0 of 25 | DELEGATECALL | 18% | 30% | 42% | 0 of 24 |
| EXTCODESIZE | 14% | 31% | 43% | 0 of 25 | CREATE2 | 14% | 24% | 42% | 0 of 19 |
| EXTCODECOPY | 13% | 24% | 38% | 0 of 25 | STATICCALL | 15% | 28% | 36% | 0 of 20 |
| RETURNDATASIZE | 53% | 63% | 76% | 0 of 20 | REVERT | 3% | 12% | 22% | 0 of 20 |
| RETURNDATACOPY | 43% | 57% | 76% | 0 of 20 | SELFDESTRUCT | 5% | 13% | 28% | 0 of 25 |
| EXTCODEHASH | 21% | 35% | 50% | 0 of 19 | PUSH2 to PUSH32 | 8% | 28% | 95% | 0 of 775 |
| BLOCKHASH | 16% | 26% | 37% | 0 of 25 | DUP1 to DUP16 | 10% | 27% | 72% | 0 of 400 |
| COINBASE | 11% | 28% | 40% | 0 of 25 | SWAP1 to SWAP16 | 4% | 26% | 66% | 0 of 400 |
| TIMESTAMP | 17% | 27% | 41% | 0 of 25 |  | | | |  |

#### Whole programs: how they run and end

#### a message leaves what the reference leaves (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 99.4% | ran: PUSH | 9.0% | ends: stops with no output |
| 96.8% | ran: stack and memory | 8.0% | SSTORE resets a dirty slot to its zero |
| 95.8% | memory grows, at least 5% | 7.6% | SSTORE changes a dirty slot |
| 90.5% | the first frame runs over 20 steps, at least 15% | 7.6% | a static call |
| 84.1% | ran: environment | 7.5% | static violation, at least 1% |
| 83.8% | ran: DUP | 7.5% | a frame halts: static violation |
| 81.9% | ran: SWAP | 7.4% | ends: halts, invalid opcode |
| 79.5% | a call | 7.2% | stack underflow, at least 1% |
| 78.8% | ran: comparison and bitwise | 7.2% | a frame halts: stack underflow |
| 76.7% | ran: arithmetic | 6.8% | gas: less than the run uses, by 1, 2 or 2300 |
| 72.1% | ran: block | 6.3% | a frame at depth 2 or more, at least 3% |
| 71.3% | steps of all frames: over 100 | 6.3% | gas: exactly what the run uses |
| 70.9% | steps of the first frame: over 100 | 6.3% | CALL halts |
| 62.2% | gas: ample | 6.0% | ends: halts, static violation |
| 60.9% | a frame at depth 1 | 5.9% | gas: little |
| 60.8% | ran: call | 5.9% | SSTORE writes a slot that was cleared |
| 60.3% | ran: storage | 5.8% | a call reverts, at least 1% |
| 59.9% | ran: control flow | 5.7% | CALLCODE halts |
| 58.1% | a log, at least 3% | 5.7% | gas: more than the run uses, by 1 or 2300 |
| 58.1% | ran: LOG | 5.6% | steps of the first frame: 6 to 20 |
| 53.7% | a call succeeds, at least 1% | 5.6% | SSTORE clears a dirty slot |
| 46.9% | ran: RETURN and REVERT | 5.5% | steps of all frames: 6 to 20 |
| 46.6% | ran: STOP | 5.4% | STATICCALL halts |
| 41.8% | ran: creation | 5.3% | invalid jump, at least 1% |
| 39.8% | a cold account | 5.3% | CREATE2 runs no message |
| 38.3% | out of gas, at least 3% | 5.3% | a frame halts: invalid jump |
| 38.3% | a frame halts: out of gas | 5.0% | DELEGATECALL halts |
| 32.8% | SSTORE leaves the word | 5.0% | CREATE halts |
| 32.6% | a cold slot | 4.7% | ends: halts, stack underflow |
| 31.9% | ends: halts, out of gas | 4.7% | ends: halts, invalid jump |
| 29.9% | a refund, at least 3% | 4.1% | it reverts, at least 1% |
| 27.7% | ran: KECCAK256 | 4.1% | ends: reverts |
| 25.5% | a call halts, at least 1% | 3.9% | a frame halts: stack overflow |
| 25.5% | CALL succeeds | 3.9% | stack overflow, at least 1% |
| 25.5% | SSTORE sets a clean zero slot | 3.8% | ends: halts, stack overflow |
| 25.2% | it returns data, at least 10% | 3.8% | a frame halts: return data out of bounds |
| 25.2% | ends: returns data | 3.3% | steps of the first frame: 1 to 5 |
| 24.8% | a block with numbers near the top of their types | 3.3% | steps of all frames: 1 to 5 |
| 24.4% | a warm account | 3.3% | CREATE runs no message |
| 23.4% | a warm slot | 3.3% | CREATE fails at the deposit of code |
| 21.3% | DELEGATECALL succeeds | 3.2% | ends: halts, return data out of bounds |
| 19.6% | steps of the first frame: 21 to 100 | 3.2% | DELEGATECALL fails in a precompile |
| 19.3% | steps of all frames: 21 to 100 | 3.2% | CALL runs no message |
| 19.0% | CALLCODE succeeds | 3.2% | CALLCODE runs no message |
| 18.3% | invalid opcode, at least 1% | 3.0% | CREATE reverts |
| 18.3% | a frame halts: invalid opcode | 2.6% **<3%** | CREATE2 fails at the deposit of code |
| 18.0% | CREATE succeeds | 2.5% **<3%** | CALL fails in a precompile |
| 16.6% | SSTORE clears a clean slot | 2.5% **<3%** | CREATE2 halts |
| 15.9% | SSTORE changes a clean slot | 2.3% **<3%** | CREATE2 reverts |
| 14.7% | ran: SELFDESTRUCT | 2.3% **<3%** | CALLCODE fails in a precompile |
| 14.2% | STATICCALL succeeds | 2.2% **<3%** | STATICCALL fails in a precompile |
| 13.1% | gas: a part of what the run uses | 0.6% **<3%** | steps of the first frame: 0 |
| 12.9% | a creation | 0.6% **<3%** | steps of all frames: 0 |
| 12.6% | a call runs no message, at least 1% | 0.4% **<3%** | DELEGATECALL reverts |
| 10.5% | CREATE2 succeeds | 0.4% **<3%** | CALLCODE reverts |
| 10.1% | ran: transient storage | 0.2% **<3%** | STATICCALL reverts |
| 9.3% | SSTORE resets a dirty slot to its word | 0.1% **<3%** | CALL reverts |

#### a message of accounts that destroy themselves leaves what the reference leaves (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 100.0% | gas: ample | 9.8% | SSTORE leaves the word |
| 89.6% | ran: PUSH | 9.7% | CREATE2 succeeds |
| 87.4% | a call | 8.9% | a frame at depth 2 or more |
| 84.3% | ends: stops with no output | 8.5% | a warm slot |
| 82.2% | ran: SELFDESTRUCT | 8.5% | ends: halts, out of gas |
| 82.2% | SELFDESTRUCT runs, at least 20% | 7.0% | steps of all frames: over 100 |
| 74.4% | ran: stack and memory | 6.2% | CALL halts |
| 70.1% | memory grows | 5.9% | ends: returns data |
| 69.8% | ran: environment | 5.6% | CALLCODE halts |
| 67.8% | an account to delete at the end, at least 10% | 5.5% | STATICCALL halts |
| 60.6% | a frame at depth 1 | 5.4% | Tangerine Whistle |
| 57.3% | ran: call | 5.2% | DELEGATECALL halts |
| 48.0% | steps of the first frame: 21 to 100 | 5.1% | SSTORE clears a clean slot |
| 46.9% | steps of all frames: 21 to 100 | 4.5% | CREATE halts |
| 45.9% | a refund | 4.4% | SSTORE changes a clean slot |
| 44.5% | ran: STOP | 3.5% | a log |
| 41.4% | the refund of SELFDESTRUCT, before London, at least 3% | 3.5% | CREATE fails at the deposit of code |
| 40.0% | a cold account | 3.5% | ran: LOG |
| 38.0% | ran: DUP | 3.3% | CREATE2 runs no message |
| 37.1% | SELFDESTRUCT in a creation, at least 3% | 3.2% | SSTORE resets a dirty slot to its word |
| 37.1% | ran: creation | 3.0% | CREATE2 halts |
| 35.3% | Spurious Dragon to Berlin | 2.9% **<3%** | CALLCODE fails in a precompile |
| 32.1% | a warm account | 2.7% **<3%** | CALLCODE runs no message |
| 30.5% | ran: RETURN and REVERT | 2.4% **<3%** | CALL fails in a precompile |
| 29.0% | steps of the first frame: 1 to 5 | 2.3% **<3%** | CREATE2 fails at the deposit of code |
| 29.0% | steps of all frames: 1 to 5 | 2.3% **<3%** | a frame halts: stack underflow |
| 28.0% | London to Shapella | 2.2% **<3%** | SSTORE changes a dirty slot |
| 24.7% | ran: comparison and bitwise | 2.2% **<3%** | SSTORE resets a dirty slot to its zero |
| 24.3% | a block with numbers near the top of their types | 2.2% **<3%** | DELEGATECALL fails in a precompile |
| 24.3% | ran: arithmetic | 2.1% **<3%** | CALL runs no message |
| 23.7% | CALL succeeds | 2.0% **<3%** | CREATE reverts |
| 22.0% | ran: storage | 2.0% **<3%** | CREATE runs no message |
| 21.4% | steps of the first frame: 6 to 20 | 1.9% **<3%** | STATICCALL fails in a precompile |
| 20.6% | Dencun and later | 1.6% **<3%** | steps of the first frame: over 100 |
| 20.0% | a frame halts: out of gas | 1.5% **<3%** | SSTORE clears a dirty slot |
| 18.2% | CREATE succeeds | 1.4% **<3%** | a frame halts: static violation |
| 17.4% | ran: SWAP | 1.3% **<3%** | ends: reverts |
| 17.3% | CALLCODE succeeds | 1.2% **<3%** | SSTORE writes a slot that was cleared |
| 17.1% | steps of all frames: 6 to 20 | 1.1% **<3%** | ran: block |
| 16.9% | DELEGATECALL succeeds | 1.0% **<3%** | CREATE2 reverts |
| 13.8% | SELFDESTRUCT runs twice or more, at least 5% | 0.7% **<3%** | ran: control flow |
| 12.6% | a creation | 0.7% **<3%** | ran: KECCAK256 |
| 11.6% | a cold slot | 0.4% **<3%** | ran: transient storage |
| 11.3% | STATICCALL succeeds | 0.2% **<3%** | STATICCALL reverts |
| 11.1% | SSTORE sets a clean zero slot | 0.1% **<3%** | CALL reverts |
| 11.1% | a frame halts: invalid opcode | 0.1% **<3%** | DELEGATECALL reverts |
| 10.7% | before Tangerine Whistle |  |  |

#### a full stack and a full depth of calls leave what the reference leaves (passed 100 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 53.0% | calls itself | 11.0% | the first frame halts: stack overflow |
| 49.0% | stays in the first frame | 11.0% | CALL succeeds |
| 47.0% | fills the stack | 10.0% | DELEGATECALL halts |
| 23.0% | a call at depth 1024 runs no message, at least 3% | 8.0% | STATICCALL halts |
| 23.0% | reaches depth 1024 | 8.0% | CALLCODE runs no message |
| 22.0% | a deeper frame halts: out of gas | 8.0% | CALL runs no message |
| 17.0% | a stack of 1021 to 1024 words, and the frame ends well, at least 3% | 7.0% | CALLCODE halts |
| 17.0% | reaches depth 100 to 1023 | 6.0% | a deeper frame halts: static violation |
| 15.0% | the first frame halts: out of gas | 6.0% | the first frame halts: stack underflow |
| 15.0% | CALLCODE succeeds | 5.0% | STATICCALL succeeds |
| 14.0% | DELEGATECALL succeeds | 4.0% | DELEGATECALL runs no message |
| 11.0% | the stack overflows, at least 5% | 3.0% | CALL halts |
| 11.0% | reaches depth 1 to 99 | 3.0% | STATICCALL runs no message |

#### a call at Glamsterdam leaves what the branch of the reference leaves (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 99.3% | ran: PUSH | 8.7% | the reservoir ends empty, from one that was not |
| 96.6% | ran: stack and memory | 8.2% | stack underflow, at least 1% |
| 95.4% | memory grows, at least 5% | 8.2% | a frame halts: stack underflow |
| 92.5% | a call | 7.8% | invalid opcode, at least 1% |
| 91.6% | the first frame runs over 20 steps, at least 15% | 7.8% | a frame halts: invalid opcode |
| 84.8% | ran: DUP | 7.5% | gas: less than the run uses, by 1, 2 or 2300 |
| 83.3% | ran: comparison and bitwise | 7.5% | a static call |
| 82.9% | ran: environment | 7.3% | state gas is spent from the gas left, at least 3% |
| 82.9% | ran: SWAP | 7.1% | DELEGATECALL fails in a precompile |
| 78.6% | ran: arithmetic | 7.0% | gas: little |
| 77.7% | steps of all frames: over 100 | 7.0% | SSTORE writes a slot that was cleared |
| 77.4% | steps of the first frame: over 100 | 6.8% | a call reverts, at least 1% |
| 75.4% | ran: block | 6.7% | CALL fails in a precompile |
| 70.7% | a cold account | 6.6% | a frame at depth 2 or more, at least 3% |
| 70.3% | a log, at least 3% | 6.4% | STATICCALL fails in a precompile |
| 60.6% | ran: control flow | 6.2% | gas: more than the run uses, by 1 or 2300 |
| 60.5% | gas: ample | 6.2% | STATICCALL halts |
| 59.7% | a reservoir | 6.1% | ends: halts, static violation |
| 58.8% | ran: LOG | 6.1% | CALLCODE fails in a precompile |
| 57.4% | ran: call | 6.0% | SSTORE clears a dirty slot |
| 56.8% | a cold slot | 6.0% | gas: exactly what the run uses |
| 54.6% | a frame at depth 1 | 5.7% | CREATE2 runs no message |
| 54.6% | ran: storage | 5.5% | SSTORE resets a dirty slot to its zero |
| 52.8% | ran: EIP-8024 | 4.7% | it reverts, at least 1% |
| 48.7% | a call succeeds, at least 1% | 4.7% | ends: halts, stack underflow |
| 48.2% | ran: transient storage | 4.7% | a frame halts: return data out of bounds |
| 46.8% | ran: RETURN and REVERT | 4.7% | ends: reverts |
| 41.5% | a warm account | 4.6% | ends: halts, return data out of bounds |
| 40.8% | ran: creation | 4.5% | steps of the first frame: 6 to 20 |
| 40.3% | no reservoir | 4.5% | steps of all frames: 6 to 20 |
| 40.1% | out of gas, at least 3% | 4.5% | CALLCODE halts |
| 40.1% | a frame halts: out of gas | 4.5% | SSTORE changes a dirty slot |
| 39.6% | a warm slot | 4.2% | DELEGATECALL halts |
| 38.5% | ran: STOP | 4.1% | CREATE fails at the deposit of code |
| 32.3% | ends: halts, out of gas | 4.1% | CALL halts |
| 31.3% | SSTORE leaves the word | 3.9% | ends: halts, invalid opcode |
| 25.5% | a refund, at least 3% | 3.8% | invalid jump, at least 1% |
| 23.9% | it returns data, at least 10% | 3.8% | a frame halts: invalid immediate |
| 23.9% | ends: returns data | 3.8% | a frame halts: invalid jump |
| 23.6% | ran: KECCAK256 | 3.7% | stack overflow, at least 1% |
| 22.2% | CALL succeeds | 3.7% | a frame halts: stack overflow |
| 20.6% | a call halts, at least 1% | 3.7% | CREATE2 fails at the deposit of code |
| 19.9% | SSTORE changes a clean slot | 3.6% | ends: halts, invalid immediate |
| 19.1% | SSTORE clears a clean slot | 3.6% | ends: halts, stack overflow |
| 18.8% | SSTORE sets a clean zero slot | 3.3% | steps of the first frame: 1 to 5 |
| 15.3% | DELEGATECALL succeeds | 3.3% | steps of all frames: 1 to 5 |
| 15.3% | CREATE succeeds | 3.2% | CREATE runs no message |
| 14.2% | steps of the first frame: 21 to 100 | 3.2% | CREATE halts |
| 14.1% | CALLCODE succeeds | 3.1% | CREATE reverts |
| 13.9% | steps of all frames: 21 to 100 | 2.9% **<3%** | ends: halts, invalid jump |
| 13.8% | STATICCALL succeeds | 2.8% **<3%** | CREATE2 halts |
| 13.4% | ran: SELFDESTRUCT | 2.1% **<3%** | CREATE2 reverts |
| 12.9% | SSTORE resets a dirty slot to its word | 1.7% **<3%** | CALLCODE runs no message |
| 12.8% | gas: a part of what the run uses | 1.1% **<3%** | CALL runs no message |
| 11.9% | CREATE2 succeeds | 1.0% **<3%** | CALLCODE reverts |
| 10.5% | a call runs no message, at least 1% | 0.6% **<3%** | steps of the first frame: 0 |
| 10.4% | state gas is spent from the reservoir, at least 2% | 0.6% **<3%** | steps of all frames: 0 |
| 10.0% | static violation, at least 1% | 0.4% **<3%** | STATICCALL reverts |
| 10.0% | a frame halts: static violation | 0.4% **<3%** | DELEGATECALL reverts |
| 9.7% | ends: stops with no output | 0.3% **<3%** | CALL reverts |

#### The precompiles

Each precompile has a property of its own, so each has its own cases.
The five of BLS12-381 that the reference answers slowly run 200 cases, and the three that pair points 100.

#### MODEXP answers any bytes as the reference (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 62.3% | base length: 1 to 32 | 13.4% | modulus length: 33 to 1024 |
| 57.2% | exponent length: 1 to 32 | 13.2% | exponent length: 0 |
| 55.2% | modulus length: 1 to 32 | 13.0% | an exponent over 32 bytes whose first 32 are zero, at least 2% |
| 51.6% | the gas of EIP-2565 | 12.1% | base length: 0 |
| 44.3% | a body as long as the lengths say, at least 10% | 11.6% | MODEXP: answers nothing |
| 43.8% | a body shorter than the lengths say, at least 5% | 11.5% | modulus length: 2^32 or more |
| 43.4% | MODEXP: refuses, outOfGas | 10.7% | exponent length: 2^32 or more |
| 36.5% | gas: plenty | 9.3% | a length over 1024 and under 2^32, at least 3% |
| 34.6% | an exponent whose first 32 bytes are zero, at least 3% | 9.3% | base length: 2^32 or more |
| 30.5% | the gas of EIP-198 | 9.0% | gas: one more than the price |
| 26.1% | gas: the price | 8.6% | gas: none |
| 23.3% | MODEXP: answers | 7.4% | the header is cut short |
| 19.8% | gas: one less than the price | 5.0% | MODEXP: refuses, lengthTooLarge |
| 16.5% | modulus length: 0 | 4.5% | a body longer than the lengths say, at least 3% |
| 15.8% | an exponent over 32 bytes, at least 5% | 3.4% | modulus length: 1025 to 2^32 |
| 15.8% | exponent length: 33 to 1024 | 3.1% | exponent length: 1025 to 2^32 |
| 15.5% | the gas of EIP-7883, with the limit of EIP-7823 | 2.8% **<3%** | base length: 1025 to 2^32 |
| 14.3% | MODEXP: answers zero | 2.4% **<3%** | before Byzantium |
| 13.5% | base length: 33 to 1024 | 2.4% **<3%** | MODEXP: no precompile at the fork |

#### BLAKE2F answers any bytes as the reference (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 54.1% | 1 to 10 rounds | 13.1% | BLAKE2F: refuses, invalidFlag |
| 52.5% | BLAKE2F: answers | 10.4% | gas: one more than the price |
| 35.1% | gas: plenty | 9.6% | gas: none |
| 27.2% | gas: the price | 8.5% | not 213 bytes |
| 23.5% | BLAKE2F: refuses, outOfGas | 8.1% | BLAKE2F: refuses, invalidInputLength |
| 17.7% | gas: one less than the price | 7.1% | over 24 rounds |
| 16.3% | 11 to 24 rounds | 2.8% **<3%** | BLAKE2F: no precompile at the fork |
| 14.0% | no round |  |  |

#### SHA-256, RIPEMD-160 and IDENTITY answer any bytes as the reference (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 75.0% | it answers, at least 10% | 11.7% | call data of whole words |
| 46.7% | call data of words and a part | 11.6% | call data of words and one byte |
| 39.9% | gas: plenty | 10.1% | SHA256: refuses, outOfGas |
| 26.5% | gas: the price | 8.7% | gas: none |
| 25.1% | RIPEMD160: answers | 8.6% | gas: one more than the price |
| 23.0% | SHA256: answers | 8.3% | RIPEMD160: refuses, outOfGas |
| 22.9% | call data of under a word | 6.6% | IDENTITY: refuses, outOfGas |
| 19.5% | IDENTITY: answers | 6.4% | IDENTITY: answers zero |
| 16.3% | gas: one less than the price | 4.1% | call data of a word |
| 15.8% | call data that ends at a word, at least 3% | 3.0% | call data of no byte |
| 15.6% | call data that ends one byte past a word, at least 3% | 1.0% **<3%** | IDENTITY: answers nothing |

#### any address answers any bytes as the reference (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 34.3% | gas: plenty | 1.5% **<3%** | P256VERIFY: refuses, outOfGas |
| 27.1% | gas: the price | 1.5% **<3%** | BN_MUL: refuses, invalidFieldElement |
| 19.7% | gas: one less than the price | 1.1% **<3%** | RIPEMD160: refuses, outOfGas |
| 9.7% | it answers | 1.0% **<3%** | a body shorter than the lengths say |
| 9.7% | gas: one more than the price | 1.0% **<3%** | base length: 0 |
| 9.2% | gas: none | 0.9% **<3%** | IDENTITY: refuses, outOfGas |
| 6.2% | call data of words and a part | 0.9% **<3%** | IDENTITY: answers zero |
| 5.5% | G2ADD: refuses, invalidInputLength | 0.8% **<3%** | ECRECOVER: refuses, outOfGas |
| 5.1% | G2MSM: refuses, invalidInputLength | 0.8% **<3%** | MODEXP: answers nothing |
| 5.1% | address 257: no precompile at the fork | 0.8% **<3%** | BN_ADD: answers zero |
| 5.0% | BLS_PAIRING: refuses, invalidInputLength | 0.7% **<3%** | MAP_FP2_TO_G2: no precompile at the fork |
| 4.6% | address 255: no precompile at the fork | 0.6% **<3%** | call data that ends one byte past a word |
| 4.6% | address 18: no precompile at the fork | 0.6% **<3%** | BLS_PAIRING: no precompile at the fork |
| 4.2% | POINT_EVALUATION: refuses, invalidInputLength | 0.6% **<3%** | the gas of EIP-7883, with the limit of EIP-7823 |
| 4.0% | MAP_FP_TO_G1: refuses, invalidInputLength | 0.6% **<3%** | MODEXP: refuses, lengthTooLarge |
| 4.0% | G1ADD: refuses, invalidInputLength | 0.6% **<3%** | BN_PAIRING: refuses, outOfGas |
| 3.8% | not 213 bytes | 0.6% **<3%** | P256VERIFY: no precompile at the fork |
| 3.8% | BLAKE2F: refuses, invalidInputLength | 0.5% **<3%** | G2MSM: no precompile at the fork |
| 3.8% | address 0: no precompile at the fork | 0.5% **<3%** | call data of a word |
| 3.8% | call data of under a word | 0.5% **<3%** | a body longer than the lengths say |
| 3.6% | MAP_FP2_TO_G2: refuses, invalidInputLength | 0.5% **<3%** | call data of words and one byte |
| 3.6% | SHA256: answers | 0.4% **<3%** | BN_MUL: answers zero |
| 3.5% | ECRECOVER: answers nothing | 0.4% **<3%** | G2ADD: no precompile at the fork |
| 3.4% | RIPEMD160: answers | 0.3% **<3%** | call data of no byte |
| 3.2% | P256VERIFY: answers nothing | 0.3% **<3%** | G1MSM: no precompile at the fork |
| 3.1% | base length: 2^32 or more | 0.3% **<3%** | BN_MUL: refuses, notOnCurve |
| 3.1% | G1MSM: refuses, invalidInputLength | 0.3% **<3%** | no round |
| 2.6% **<3%** | the header is cut short | 0.3% **<3%** | BLAKE2F: answers |
| 2.6% **<3%** | MODEXP: refuses, outOfGas | 0.2% **<3%** | MAP_FP_TO_G1: answers |
| 2.6% **<3%** | BN_PAIRING: refuses, invalidInputLength | 0.2% **<3%** | BN_PAIRING: answers |
| 2.5% **<3%** | call data that ends at a word | 0.2% **<3%** | BN_PAIRING: no precompile at the fork |
| 2.4% **<3%** | modulus length: 0 | 0.2% **<3%** | G1MSM: answers zero |
| 2.2% **<3%** | BN_ADD: refuses, invalidFieldElement | 0.2% **<3%** | BN_MUL: no precompile at the fork |
| 2.1% **<3%** | exponent length: 0 | 0.1% **<3%** | a length over 1024 and under 2^32 |
| 2.0% **<3%** | BN_ADD: refuses, outOfGas | 0.1% **<3%** | POINT_EVALUATION: no precompile at the fork |
| 2.0% **<3%** | an exponent whose first 32 bytes are zero | 0.1% **<3%** | MAP_FP_TO_G1: no precompile at the fork |
| 2.0% **<3%** | an exponent over 32 bytes whose first 32 are zero | 0.1% **<3%** | MAP_FP2_TO_G2: refuses, outOfGas |
| 2.0% **<3%** | call data of whole words | 0.1% **<3%** | exponent length: 1025 to 2^32 |
| 1.9% **<3%** | the gas of EIP-2565 | 0.1% **<3%** | before Byzantium |
| 1.9% **<3%** | exponent length: 2^32 or more | 0.1% **<3%** | MODEXP: no precompile at the fork |
| 1.8% **<3%** | BN_MUL: refuses, outOfGas | 0.1% **<3%** | BN_ADD: refuses, notOnCurve |
| 1.8% **<3%** | IDENTITY: answers | 0.1% **<3%** | BLS_PAIRING: answers |
| 1.7% **<3%** | modulus length: 2^32 or more | 0.1% **<3%** | POINT_EVALUATION: refuses, outOfGas |
| 1.6% **<3%** | SHA256: refuses, outOfGas | 0.0% **<3%** | a body as long as the lengths say |
| 1.5% **<3%** | the gas of EIP-198 | 0.0% **<3%** | an exponent over 32 bytes |

A mutation of a near-valid input now has 20 to 45 cases in which the body of the precompile ran, where it had 1 to 4.
ECRECOVER stands for the ten: the others are in the report of a run.

#### ECRECOVER answers a near-valid input as the reference (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 73.9% | the body runs on an input that it accepts, at least 10% | 2.3% **<3%** | mutation 12: answers nothing |
| 60.2% | the body runs on a mutated input, at least 15% | 1.9% **<3%** | mutation 0, cut: answers |
| 45.2% | ECRECOVER: answers nothing | 1.8% **<3%** | mutation 9: answers |
| 36.5% | gas: plenty | 1.6% **<3%** | mutation 9: answers nothing |
| 30.0% | gas: the price | 1.1% **<3%** | mutation 7, cut: answers nothing |
| 28.7% | ECRECOVER: answers | 1.1% **<3%** | mutation 4, cut: answers nothing |
| 26.1% | ECRECOVER: refuses, outOfGas | 1.1% **<3%** | mutation 1, cut: answers nothing |
| 16.7% | gas: one less than the price | 0.9% **<3%** | mutation 11, cut: answers nothing |
| 11.1% | the body runs on a valid input, at least 3% | 0.9% **<3%** | mutation 10, cut: answers |
| 11.1% | mutation 0: answers | 0.9% **<3%** | mutation 13, cut: answers nothing |
| 9.4% | gas: none | 0.8% **<3%** | mutation 3, cut: answers nothing |
| 7.4% | gas: one more than the price | 0.7% **<3%** | mutation 0, cut: answers nothing |
| 4.5% | mutation 11: answers nothing | 0.7% **<3%** | mutation 8, cut: answers |
| 4.2% | mutation 7: answers nothing | 0.7% **<3%** | mutation 9, cut: answers nothing |
| 3.9% | mutation 14: answers | 0.7% **<3%** | mutation 6, cut: answers nothing |
| 3.6% | mutation 8: answers | 0.7% **<3%** | mutation 2, cut: answers nothing |
| 3.6% | mutation 13: answers nothing | 0.6% **<3%** | mutation 9, cut: answers |
| 3.6% | mutation 2: answers nothing | 0.6% **<3%** | mutation 5, cut: answers nothing |
| 3.4% | mutation 10: answers | 0.6% **<3%** | mutation 12, cut: answers nothing |
| 3.4% | mutation 5: answers nothing | 0.5% **<3%** | mutation 14, cut: answers |
| 3.2% | mutation 1: answers nothing | 0.4% **<3%** | mutation 14, cut: answers nothing |
| 3.0% | mutation 4: answers nothing | 0.3% **<3%** | mutation 7, cut: answers |
| 2.8% **<3%** | mutation 3: answers nothing | 0.3% **<3%** | mutation 10, cut: answers nothing |
| 2.3% **<3%** | mutation 6: answers nothing | 0.1% **<3%** | mutation 8, cut: answers nothing |

#### The functions under the instructions

#### arithmetic and bitwise instructions on integers (passed 10000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 63.9% | a shift of 1 to 255 | 31.3% | ADDMOD has a sum of 2^256 or more, and a modulus |
| 57.7% | MUL wraps | 30.7% | SMOD of a negative dividend |
| 52.8% | MULMOD has a product of 2^256 or more, and a modulus | 30.4% | SDIV of signs that differ |
| 52.2% | SIGNEXTEND of byte 31 or more | 16.8% | a shift above 256 |
| 51.6% | BYTE of index 0 to 31 | 14.9% | SIGNEXTEND of byte 0 to 30, sign set |
| 50.1% | SUB borrows | 11.9% | a shift of 0, at least 1% |
| 48.4% | BYTE of index 32 or more | 8.4% | a divisor of 0, at least 2% |
| 34.1% | ADD wraps | 8.4% | CLZ of 0, at least 1% |
| 33.5% | SMOD of a negative divisor | 8.1% | a modulus of 0, at least 2% |
| 33.1% | SAR of a negative word | 7.5% | equal operands, at least 1% |
| 33.1% | CLZ of a word with its top bit | 7.5% | a shift of 256 |
| 32.9% | SIGNEXTEND of byte 0 to 30, sign clear | 6.7% | SDIV of -2^255 by -1, at least 1% |

#### EXP is the power modulo 2^256 (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 39.3% | an odd base | 11.7% | base 1 |
| 34.0% | an exponent of 9 to 31 bytes, at least 10% | 10.8% | an exponent of 2 to 8 bytes, at least 4% |
| 26.0% | an even base | 6.2% | an exponent of 32 bytes, at least 1% |
| 23.0% | base 0 | 2.1% **<3%** | exponent 0, at least 1% |
| 23.0% | the power wraps |  |  |

#### the valid jump destinations (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 83.4% | a PUSH whose data may run past the code | 18.3% | a PUSH32 |
| 75.8% | a JUMPDEST byte in push data | 14.9% | no JUMPDEST byte |
| 59.6% | a valid destination | 7.1% | no code |
| 21.2% | a PUSH0 |  |  |

#### the addresses of CREATE and CREATE2 (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 67.1% | a nonce with a length byte | 5.5% | a nonce of 7 bytes, at least 1% |
| 29.0% | nonce of one byte, itself | 5.1% | a nonce of 5 bytes, at least 1% |
| 18.6% | a nonce of 8 bytes, at least 1% | 4.9% | a nonce of 6 bytes, at least 1% |
| 13.2% | a sender that starts with a zero byte | 4.6% | a nonce of 3 bytes, at least 1% |
| 9.4% | a nonce of 2 bytes, at least 1% | 4.4% | a nonce of 2^64 - 1 |
| 7.5% | no init code | 3.9% | nonce 0 |
| 5.9% | a nonce of 4 bytes, at least 1% | 2.5% **<3%** | init code over 55 bytes |
| 5.7% | a nonce of 0x7f or 0x80, at least 1% |  |  |

#### the growth of memory (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 50.6% | no growth | 19.7% | growth of 2^16 bytes or more |
| 48.5% | two ranges or more, at least 10% | 19.0% | growth of words |
| 48.2% | the quadratic part is above 0 | 18.3% | no growth from a range with bytes, at least 5% |
| 29.1% | a range of size 0 | 15.6% | a size of 2^22 or more |
| 27.9% | a range inside the memory | 12.4% | a range that ends at 2^32 or beyond, at least 1% |
| 27.3% | 1 ranges | 11.8% | a range that ends one byte past the size, at least 2% |
| 25.8% | a range that ends one byte past a word, at least 5% | 11.4% | an empty memory before |
| 24.7% | 2 ranges | 10.7% | growth of one word, at least 3% |
| 24.2% | 0 ranges | 10.7% | growth of a word |
| 23.8% | 3 ranges | 10.2% | a range that ends at 2^64 or beyond, at least 1% |
| 21.8% | a range that ends at a word, at least 5% | 9.4% | a range that ends at the size, at least 2% |
| 20.2% | a later range grows more | 8.6% | a range of no byte at a huge start, at least 1% |

#### the gas of a call, with all but one 64th (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 69.0% | a call with value, which adds the stipend, at least 10% | 20.0% | the frame has exactly the extra price and the memory, at least 3% |
| 41.8% | the gas asked is above the bound, at least 10% | 16.4% | the gas asked is below the bound, at least 10% |
| 27.2% | the gas asked is the bound, at least 3% | 14.6% | the frame cannot pay the extra price and the memory, at least 5% |

#### The fee functions

#### the base fee of EIP-1559 (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 44.0% | the parent is below its target, at least 8% | 10.6% | the parent is full |
| 30.5% | the parent is at its target, at least 8% | 9.8% | the rise is more than 1, at least 3% |
| 25.5% | the parent is above its target, at least 8% | 7.9% | a base fee of 0 |
| 24.8% | the fall is 0 | 3.2% | one below the target, at least 1% |
| 19.2% | the fall is more than 0, at least 5% | 2.3% **<3%** | one above the target, at least 1% |
| 16.6% | the parent is empty | 2.0% **<3%** | the rise is an eighth, the most |
| 15.7% | the rise is the least, 1 |  |  |

#### a gas limit may follow its parent's (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 39.2% | refused: too high, at least 5% | 17.8% | one above the lower bound, at least 1% |
| 35.1% | refused: too low, at least 5% | 15.1% | refused: below 5000 alone, at least 1% |
| 24.0% | a parent below 1024, with no room | 15.1% | refused: below 5000 |
| 21.3% | the limit of the parent | 9.5% | one below the upper bound, at least 1% |
| 20.9% | accepted, at least 8% | 8.7% | at 5000 |
| 20.3% | at the upper bound, refused | 2.0% **<3%** | at 4999 |
| 19.5% | at the lower bound, refused |  |  |

#### fakeExponential is fake_exponential of EIP-4844 (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 72.3% | ratio 1 to 60 | 4.1% | ratio below 1 |
| 68.1% | factor 1 | 2.1% **<3%** | numerator 0 |
| 65.5% | a denominator of a fork | 1.7% **<3%** | factor 0 |
| 30.2% | factor above 1 | 1.7% **<3%** | a denominator of 1 |
| 21.5% | ratio above 60 |  |  |

#### the excess blob gas and the blob gas price (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 65.2% | the rule of EIP-4844, at least 10% | 19.9% | at prague |
| 55.0% | above the target: the rule of EIP-4844 | 19.0% | at bpo2 |
| 53.7% | the blob gas price is 1 | 18.8% | at bpo1 |
| 46.3% | a blob gas price above 1, at least 10% | 13.1% | below the target, at least 5% |
| 23.0% | an excess of 0 in the parent | 13.1% | below the target: the excess is 0 |
| 23.0% | the reserve price meets the blob base fee | 10.2% | at the target: the excess is 0 |
| 21.7% | the reserve price of EIP-7918 rules, at least 5% | 8.7% | the parent used the most blobs |
| 21.2% | at cancun | 5.7% | the parent used no blob |
| 21.1% | at osaka | 0.9% **<3%** | one below the target |

#### The state machines

#### SLOAD and SSTORE follow the model of the EIPs (StateMachine) (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 68.3% | SSTORE leaves the word, at least 3% | 19.0% | SSTORE resets a dirty slot to its word, warm |
| 59.1% | the refund rises | 17.5% | SSTORE writes a slot that was cleared, at least 3% |
| 50.1% | SSTORE changes a clean slot, at least 3% | 16.1% | SSTORE refused at the stipend |
| 49.6% | SSTORE clears a clean slot, at least 3% | 15.8% | SSTORE resets a dirty slot to its zero, at least 3% |
| 49.1% | London and later | 15.6% | SSTORE clears a clean slot, warm |
| 36.9% | SSTORE sets a clean zero slot, at least 3% | 15.6% | SSTORE changes a clean slot, warm |
| 36.0% | SLOAD | 15.5% | SSTORE sets a clean zero slot, cold |
| 32.2% | SSTORE resets a dirty slot to its word, at least 3% | 13.8% | SSTORE changes a dirty slot, at least 3% |
| 31.9% | SLOAD warm | 13.1% | Istanbul and Muir Glacier |
| 29.0% | SSTORE leaves the word, cold | 12.3% | before Tangerine Whistle |
| 28.9% | SLOAD cold | 11.5% | SSTORE clears a dirty slot, warm |
| 27.6% | SSTORE leaves the word, warm | 10.9% | SSTORE sets a clean zero slot, warm |
| 24.5% | SSTORE out of gas | 9.8% | SSTORE writes a slot that was cleared, warm |
| 22.4% | the refund falls | 9.0% | SSTORE resets a dirty slot to its zero, warm |
| 20.5% | Tangerine Whistle to Petersburg | 8.3% | SLOAD out of gas |
| 19.8% | SSTORE clears a clean slot, cold | 7.7% | SSTORE changes a dirty slot, warm |
| 19.2% | SSTORE changes a clean slot, cold | 5.0% | Berlin |
| 19.0% | SSTORE clears a dirty slot, at least 3% |  |  |

#### DUPN, SWAPN and EXCHANGE follow the list of EIP-8024 (StateMachine) (passed 1000 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 53.0% | EXCHANGE runs, at least 10% | 30.1% | SWAPN runs, at least 10% |
| 50.0% | DUPN refused: the stack is too short | 25.4% | DUPN runs, at least 10% |
| 47.8% | SWAPN refused: the stack is too short | 24.3% | EXCHANGE refused: the stack is too short |
| 46.5% | EXCHANGE refused: the immediate encodes nothing | 6.6% | it reaches the deepest item, at least 2% |
| 43.9% | PUSH runs | 5.4% | DUPN refused: the stack is full |
| 35.0% | DUPN refused: the immediate encodes nothing | 5.1% | it reaches one past the deepest item, at least 2% |
| 33.9% | SWAPN refused: the immediate encodes nothing | 3.6% | PUSH refused |

#### The frame scenario

Every fork steps a frame now, 333 sequences of up to 40 commands each; these are London's shares.
Over the 24 forks, DUP met a stack that holds what it reaches in 36% to 49% of the sequences, SWAP in 24% to 34%, and a range ended at the size of the memory in 14% to 22%.

#### a frame steps as the reference at london (Command, madhouse) (passed 333 tests)

| Share | Class | Share | Class |
| ---: | --- | ---: | --- |
| 88.0% | a frame that may write | 14.1% | an instruction at the edge of the memory halts: revert |
| 83.2% | a frame with ample gas | 12.3% | a spoiler halts: invalid opcode |
| 73.0% | an instruction that leaves its result runs | 12.0% | a static frame |
| 70.9% | a snippet runs | 12.0% | a spoiler halts: out of gas |
| 57.1% | an instruction at the edge of the memory runs | 10.8% | POP on the stack it meets, at least 3% |
| 41.7% | DUP on the stack it meets, at least 9% | 10.8% | POP runs |
| 41.7% | DUP runs | 10.5% | a spoiler halts: invalid jump |
| 29.4% | DUP halts: stack underflow | 6.6% | a spoiler halts: return data out of bounds |
| 28.5% | a range that ends inside the memory, at least 3% | 6.3% | a spoiler halts: stack underflow |
| 28.2% | an instruction on the words of the stack, at least 5% | 4.5% | SWAP halts: stack underflow |
| 28.2% | an instruction on the stack runs | 3.6% | an instruction at the edge of the memory halts: static violation |
| 27.9% | SWAP on the stack it meets, at least 9% | 1.5% **<3%** | a spoiler halts: revert |
| 27.9% | SWAP runs | 1.5% **<3%** | a snippet halts: static violation |
| 26.7% | POP halts: stack underflow | 1.2% **<3%** | SWAP9 to SWAP16 on the stack it meets |
| 20.4% | a range that ends at the size of the memory, at least 3% | 0.9% **<3%** | DUP9 to DUP16 on the stack it meets |
| 19.5% | a range that ends one byte past the memory, at least 3% | 0.9% **<3%** | a snippet halts: out of gas |
| 16.8% | a frame with little gas | 0.3% **<3%** | an instruction at the edge of the memory halts: out of gas |
| 16.2% | a spoiler runs | 0.3% **<3%** | a spoiler halts: static violation |
Over the 24 forks the scenario ran 65191 commands.

### Every parameter: the tables walked whole

A table that a fork indexes holds a bug at the fork a sample skips, so these properties walk each table and compare every entry (`Property/Evm/Tables.lean`).
Each is one test case, and all pass.

| Property | Entries | Reference |
| --- | --- | --- |
| The opcodes of every fork | the set of opcode bytes at each of 28 forks: the 24 of the release, BPO3 to BPO5 and Glamsterdam | the table of instructions of EELS, the release and the branch |
| Each of the 256 bytes at a fork | 24 forks by 256 bytes, each run after seventeen pushes: an invalid opcode or not | a frame of EELS that runs the byte |
| The precompiles of every fork | the addresses below 512 at each of 28 forks, and four far addresses | the table of precompiles of EELS |
| Every gas constant, by its name | 3,143 pairs of fork and constant at 28 forks, over `GasCosts`, `gasSchedule`, the prices of SLOAD, BALANCE, EXTCODESIZE, EXTCODEHASH and the calls, the precompiles and the blob schedule | `GasCosts` of each fork of the branch, which names its constants as EthLib does |
| SSTORE at every slot | 24 forks, original, current and new word each 0, 1 or 2, cold and warm, gas ample and 2300 and 2301 at the check of EIP-2200: 3,888 writes | a frame of EELS on such a slot |
| EXP at every exponent length | 24 forks, the least and the greatest exponent of each length from 0 to 32 bytes, five bases: 7,800 steps | a frame of EELS |
| All but one 64th | every gas from 0 to 130, and `2^k - 1`, `2^k` and `2^k + 1` for `k` up to 256 | `max_message_call_gas` |
| The discount of G1MSM and G2MSM | every number of pairs from 0 to 130, and 200, 255, 256 and 257, with EthLib's price and one less | the precompiles of EELS at Osaka |

The first three print what they compared.
The opcodes grow as the EIPs say: DELEGATECALL at Homestead, four at Byzantium, five at Constantinople, CHAINID and SELFBALANCE at Istanbul, BASEFEE at London, PUSH0 at Shapella, five at Dencun, CLZ at Fusaka, four at Glamsterdam, and none at the other forks.
The precompiles are 1 to 4 from Frontier, 5 to 8 from Byzantium, 9 from Istanbul, 10 from Dencun, 11 to 17 from Pectra and 256 from Fusaka.
Two constants of the branch have no entry in EthLib's prices: `AUTH_TUPLE_BYTES` and `BLOCK_ACCESS_LIST_ITEM`.

Generated properties cover the parameters that no walk fits:

- The gas of a call (`messageCallGas`) at every fork from Tangerine Whistle: the gas asked around the bound, the gas left around the extra price and the memory, with and without value.
- The growth of memory: ranges that end at the size, one byte past it, at a word, one byte past a word, around `2^32` and `2^64`, and of no byte at a huge start.
  Round 1 dropped every range past `2^40`; the reference prices them all.
- MODEXP at every class of its three lengths, with a body shorter, equal and longer than they say, an exponent whose first 32 bytes are zero, and the gas of EIP-198, EIP-2565 and EIP-7883.
- The hash precompiles at lengths around a word and around a block of the hash.
- EXP as a function at every length of its exponent, and the address of CREATE at every length of its nonce.

### What is tested now

Cases are those of `lake exe evm-property 1000`: 89 properties and about 42,000 cases, in 17 minutes on a loaded machine, and one more property that must fail.
Every row passes.

| Property | EthLib definitions | Varied | Reference | Cases |
| --- | --- | --- | --- | --- |
| A message leaves what the reference leaves | `processMessage`, `processCreateMessage`, every instruction | the fork (24), a call, a static call or a creation, the program, two callees, the gas around what the run uses, the block, the nonce, four slots | EELS | 1,000 |
| A message of accounts that destroy themselves | `selfdestructStep`, `incorporateChild`, the refund before London, the rule of EIP-6780 | the fork, the beneficiary, calls and creations before the end | EELS | 1,000 |
| A full stack and a full depth of calls | `Stack.push` at 1024, `genericCall` at depth 1024 | the fork, the kind of call, the gas, the word pushed | EELS | 100 |
| MODEXP, BLAKE2F, the three hash precompiles, any address, each on any bytes | `Precompiles.run`, `price`, `isPrecompile` | the fork, the lengths, the body, the gas around the price | EELS | 4 x 1,000 |
| Each of 13 precompiles on a near-valid input | the same, and the curve code under it | the fork, a valid input, 14 mutations, 5 changes of length, the gas | EELS on inputs from `py_ecc`, `eth-keys`, `cryptography` | 5 x 1,000, 5 x 200, 3 x 100 |
| Arithmetic and bitwise instructions | `add` to `signextend`, the shifts, `countLeadingZeros` | three words and a small one, with the words of each rule | `Nat` and `Int` | 10,000 |
| EXP, the jump destinations, the addresses of creations, the growth of memory | `exp`, `validJumpDestinations`, `createAddress`, `create2Address`, `extendMemory` | every length of exponent and of nonce, ranges at each boundary | `Nat`, EELS | 4 x 1,000 |
| The base fee, the gas limit, `fakeExponential`, the excess blob gas | `Fees` | the parent around its target and its bounds, the fork | EELS | 4 x 1,000 |
| The gas of a call | `messageCallGas`, `maxMessageCallGas` | the fork from Tangerine Whistle, the gas asked and left around the bound | EELS | 1,000 |
| Eight tables walked whole | `Op.ofByte`, `isPrecompile`, `GasCosts`, `gasSchedule`, `sstoreCost`, `sstoreRefund`, `expStep`, the discounts of the MSMs | every entry: see above | EELS, the release and the branch | 8 x 1 |
| A call at Glamsterdam | `processMessage` with `StateGasMeter` | the program with SLOTNUM and EIP-8024, the reservoir | the branch of EELS | 1,000 |
| SLOAD and SSTORE (`StateMachine`) | `sloadStep`, `sstoreStep` | the fork, four slots, the gas | a model of the EIPs | 1,000 sequences |
| DUPN, SWAPN and EXCHANGE (`StateMachine`) | `dupnStep`, `swapnStep`, `exchangeStep` | the immediate, the depth | a list model of EIP-8024 | 1,000 sequences |
| A frame steps as the reference (`Command`) | `step` on one frame kept over a sequence | each of 24 forks, six kinds of command, the gas, a static frame | a frame of EELS stepped in the oracle | 24 x 333 sequences of up to 40, and 24 x 1 in order |

### Findings of round 3

No property found a place where EthLib computes another value than its reference, with every opcode of every fork run and every table walked.
The finding of round 1 stands as it was, in the group `evm: findings`, which must fail: `HEDGEHOG_ONLY="record no read" lake exe evm-property`.

Harness mistakes of this round, each fixed:

- A program that calls itself with all its gas spends the whole gas in calls of calls: millions of instructions, which the reference runs in minutes.
  The transition driver draws its contracts from this generator, and its reference gave up on six transactions.
  A call of the running program now asks for at most 30,000 gas, and a call in a called program for a bounded amount.
- A frame of the reference that refused a code kept what the code had done before it failed: a warm slot, a write.
  The oracle now opens a transaction of the state before each code and rolls it back on a failure.
- The spoiler of the frame scenario could be a CALL with one operand too few, which runs on a stack that holds more: a frame that is stepped runs no message.
  The scenario draws no call there.
- A range of memory that starts at `2^256` is no word; the generator drew one.
- The reference refuses a parent gas limit under 5000 before it computes a base fee, so none is drawn: the rule of EthLib for a target of 0 has no reference.

### Not covered, after round 3

The list of round 1 stands, with these changes:

- BPO3, BPO4 and BPO5 are now compared with the branch of the reference for their opcodes, their precompiles and their gas constants.
  No message runs at them: the oracle that runs messages drives the release, which lacks them.
- Which error halts a frame is still not compared; the trace names EthLib's error only to classify a case.
- The frame scenario runs no call and no creation, since a stepped frame runs no message; whole programs do.
- At Glamsterdam the block is always the small one, and no frame is stepped.
- The table of opcodes is of whole programs, where the least share of an opcode at a fork is 3%: one or two programs of about forty.
  The median is 28%.
- In the frame scenario an opcode runs in a median of 19 commands of a fork, and a PUSH, a DUP or a SWAP of a rare size in 1 to 4.
  SWAP13, SWAP14 and LOG4 each ran in no command at one fork, in 333 sequences.
  DUP9 to DUP16 and SWAP9 to SWAP16 meet a stack deep enough in under 2% of the sequences; elsewhere they run over words of their own.
- The pairs of precompile and mutation of the eight slow precompiles have 1 to 10 cases each at 1,000.
- The largest run of whole programs was 5,000 of any snippets and 5,000 that destroy accounts: both passed, with each opcode in 7% or more of the programs of each fork.
  A rule that one program in a hundred thousand reaches was not looked for.

### Notes on lean-hedgehog 0.3.0

What the new pieces were like in this driver:

- The context first in `check`, `apply` and `next`.
  The four frame commands of round 1 each stored a `ctx`; now none does, and a command holds only its bytes.
  The frame is indexed by its fork, `Command (Snippet fork) (FrameState fork) (FrameContext fork) IO`, as USAGE says, and the `Σ fork` of round 1 with its check at each command is gone.
  A state with an index has no default, so the scenario is `scenarioFrom`; that was no cost, since the start is generated anyway (the gas, and whether the frame is static).
- `next` and `buildIn`.
  The state holds EthLib's frame, which is a pure value, so `next` runs the command in it.
  `buildIn` then sees the stack and the memory that the command will meet: DUP and SWAP reach what the stack holds, an instruction takes its operands from the results of the commands before it, a range of memory ends at the size of the memory or one byte past it.
  This is the piece that changed the scenario most: in round 1 SWAP ran in 2.5% of the sequences of a fork and DUP in 8.9%, now in 24% to 34% and 36% to 49% over the forks, each on a stack that holds what it reaches.
  It works only because the system under test is pure; a system behind a handle has no `next` that is true, and USAGE could say so.
- `setup` and the range of a scenario.
  `setup` starts the frame of the reference from the generated state, which the first command did in round 1.
  The range `.linear 1 40` gives sequences that carry memory and warm slots far enough.
  A hook after the last command is missing: the opcodes that a whole sequence ran, or the number of commands that ran, can only be labelled from inside a command, so they are counted in an `IO.Ref` beside the report.
- `StateMachine.applySut` with the state before.
  The label of an SSTORE needs the slot before the write and whether the model refused it: both are there now, with no flag threaded for it.
- Coverage.
  `label` and `classify` were the audit: every table above is their output.
  `cover` with a minimum of a third of the share seen at 1,000 cases held on every rerun; a minimum is asked only from 500 cases, by a flag of the driver, since the shares fall on short runs.
  A report lists the labels in the order they were first met, with the percentage first, so a property with a hundred labels is read through `sort`.
  A minimum is a whole percentage: a class at 0.5% can be named and not required.
  The table of opcodes by fork has 3,300 cells, which labels do not fit: a `tabulate` in two keys, as QuickCheck has, would.
  A share in a state machine or a scenario is of sequences, as USAGE says; a share of transitions would say more about a model of nine kinds of SSTORE.
- `Selection.fromEnv`.
  `HEDGEHOG_ONLY` with several parts ran the slow groups in separate processes, and replaced the word filter that this driver had.
  A part cannot hold a comma, so a name with one is selected by another of its parts: `at london (Command, madhouse)` selected every fork, by its second half.
- `mustFail`.
  The finding of round 1 is in such a group, and the exit code now says when it is gone.
- A walk of a whole table is a property of one test with loops in its test.
  That works, and a failure names the entry by `annotate`; nothing says how far a walk of ten thousand entries is, and a time limit for a property is missing.
- `Gen.sequence (atLeast := n)` keeps the operands of an instruction whole under shrinking.
  Without it a shrink dropped an operand and turned a counterexample into a stack underflow.
- Shrinking.
  The one failure of the new frame scenario shrank from about twenty commands to two in 13 steps, `ADD [0, 0]` and a CALL with six of its seven operands, which named the harness mistake at once.

Bugs of the library: none met.

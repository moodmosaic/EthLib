# The EVM: what the property tests found

The driver is `Property/Evm.lean` with its modules under `Property/Evm/`.
It covers `EthLib/Execution/Evm/`, `Evm/Precompiles/` and `Execution/Fees/`.

```bash
cd tests/property
.venv/bin/pip install --no-deps ethereum-execution==2.20.0   # See oracle/requirements-evm.txt.
lake build evm-property
lake exe evm-property 1000              # Every property, then the findings.
lake exe evm-property 5000 message      # Only the properties whose name holds a word.
lake exe evm-property stats 3000        # How the generated programs end, to judge the generator.
```

## The references

- `oracle/evm.py` drives the Python execution-specs (EELS), `ethereum-execution` 2.20.0.
  It has every fork from Frontier to BPO2, and was written apart from EthLib.
  A fork that changes only the consensus layer (Phase 0, Altair, Bellatrix) runs against the
  execution fork before it, and Petersburg against Constantinople, which is EELS's Petersburg.
- `oracle/evm_amsterdam.py` drives the branch `forks/amsterdam` of EELS at commit `16898000`.
  No release has Glamsterdam, and the fork is not final.
  EthLib's state tracker has the names of that branch, so the two are not fully independent.
- `oracle/evm_inputs.py` builds call data for the precompiles from a recipe, with `py_ecc`,
  `eth-keys` and `cryptography`: a valid input from three numbers, then one rule broken.
- Three models are written from the source text, with no reference process: the arithmetic of the
  Yellow Paper on `Nat` and `Int`, the gas and refund of SLOAD and SSTORE, and the list of EIP-8024.

## What was tested

Cases are those of `lake exe evm-property 1000`; the last column gives the largest run made.
Every row passes.

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
`stats` says how runs end: about half succeed, one in twelve creates an account, one in seven
writes a log.

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
- Command: `lake exe evm-property 1 findings`.

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

## Notes on lean-hedgehog

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

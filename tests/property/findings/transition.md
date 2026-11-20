# The transaction and the block transition: what the property tests found

The driver is `Property/Transition.lean`, with its modules under `Property/Transition/`.
The oracles are `oracle/transition.py` and `oracle/transition_amsterdam.py`, which share `oracle/transition_txs.py`.
`oracle/requirements-transition.txt` lists what they need, which the EVM driver installed already.

    cd tests/property
    lake build transition-property
    lake exe transition-property 1000
    HEDGEHOG_ONLY="block at Glamsterdam" lake exe transition-property 3000

The scope is the transaction and the block of the execution layer, as wholes.
It is `Transactions/Process.lean`, `Settlement.lean`, `Inclusion.lean` and `Validity.lean` as they meet a state, and `Blocks/Transition.lean` and `Blocks/Validate.lean`.
The earlier rounds compared one message call and the pieces around a transaction.
This round runs whole transactions and whole blocks.

No property found a place where EthLib computes another value than its source.
One difference from the reference of Glamsterdam was found, and EthLib documents it as a choice.
So a bug that remains is not in what these properties reach, and the last sections say what they do not reach.

## The references

- `oracle/transition.py` drives the Python execution-specs (EELS), `ethereum-execution` 2.20.0, at each of its 20 forks, Frontier to BPO2.
  It calls `process_transaction`, `apply_body` and `state_transition` of the fork, and `validate_ommers` and `apply_fork` where the fork has them.
  The seal of a header is patched out, and `checkSeal` is off in EthLib.
- A fork of EthLib with no module there runs beside the fork whose rules it keeps: Petersburg beside Constantinople, Phase 0 beside Muir Glacier, Altair beside London, Bellatrix beside Gray Glacier.
  BPO3, BPO4 and BPO5 run beside BPO1, BPO2 or Osaka on a chain that sets the blob schedule of that fork (EIP-7892), since from Fusaka the forks differ only in their blob schedule.
- `oracle/transition_amsterdam.py` drives the branch `forks/amsterdam` of EELS for Glamsterdam, at the revision that `oracle/requirements-evm.txt` names.
  No release has that fork, and it is not final.
- `oracle/transition_txs.py` builds each transaction from its fields with the classes of EELS, and signs it with coincurve.
  Both sides then run the same bytes, so the decoder and the sender recovery of EthLib take part in every case.
- The oracle adds one rule that EELS leaves out: a typed transaction must name the chain, as EIP-2930 asks (round 2 found this).
- One model has no reference process: a ledger of nonces and balances as plain numbers, written from the Yellow Paper (6.2) and EIP-1559, 2028, 2930, 7623 and 7825.

## What was tested

The numbers are those of `lake exe transition-property 3000`: 27 properties, exit code 0.
A scenario runs a tenth of the cases at each of its 19 forks, so 300 sequences of up to 50 commands each.
A run of 5,000 (500 sequences per fork) passed too, on generators that did not yet have the precompile callees, the odd delegations and the child that is created again.
The coverage minimums were lowered after the run of 3,000, so that a run of 100 or of 30 cases passes; runs of 30, 100, 300 and 1,000 then passed.
Every row passes, but the last, which fails by design.

| Property | EthLib definitions | What varies | Reference | Cases | Shares of the labels |
| --- | --- | --- | --- | --- | --- |
| a transaction leaves what the reference leaves | `decodeTransaction`, `checkInclusion`, `checkBlockGas`, `checkSender`, `processTransaction`, `prepareFirstFrame`, `applyAuthorizations`, `startSubstate`, `buyGas`, `settleGas`, `payBeneficiary`, `gasUsed`, `gasRefund`, `deleteAccounts`, `applyTransaction`, `makeReceipt`, `stateRoot` (before Byzantium, in the receipt) | 27 forks of EthLib beside 20 modules, the type (0 to 4), 18 actions, 29 faults, 6 beneficiaries, the base fee, the excess blob gas, the blob schedule, the gas and blob gas used before | EELS `process_transaction` | 3,000 | valid 67.5%, invalid 32.5%; ok 33.1%, out of gas 18.1%, other halt 9.5%, revert 6.8%; each of 17 reasons of refusal 0.5% to 6.7%; types 0 to 4 valid 32.1%, 15.2%, 11.8%, 6.0%, 2.4%; by fork family below |
| both sides refuse a transaction for the same reason | `InclusionError`, `TransactionError`, the order of the checks of `checkInclusion` and `validateTransaction` | the same cases | the name of the exception of EELS | 3,000 | 17 reasons, 0.7% to 6.0% each, 32% refused |
| a block is valid as in the reference, and leaves the same state | `stateTransition`, `checkBlock`, `runBody`, `applyBody`, `startSystemCalls`, `applyTransactions`, `withdrawalState`, `blockRequests`, `depositRequests`, `readRequests`, `payRewards`, `daoTransfer`, `daoExtraDataValid`, `validateOmmers`, `outputRoots`, `outputChecks`, `recentHashes`, `blockEnvironment`, `chainBlobSchedule`, `Block.decode`, `decodeBodyTransaction` | the fork, 0 to 6 transactions of 4 senders, withdrawals, 0 to 3 ommers of ages 1 to 7, the gas used and blob gas of the parent, a chain of 1 to 8 or 254 to 300 blocks, the DAO Fork block and its extra data, a missing system contract, one header field changed, the blob schedule of the chain | EELS `state_transition` on a block that EELS built | 3,000 | valid 60.4%; refused at a transaction 5.9%, the ommers 12.7%, the header 2.1%, a system call 1.2%, a deposit 0.4%, and at each of 8 changed fields 0.7% to 3.3%; valid with ommers 13.9%, withdrawals 9.0%, three transactions or more 20.0%, a reverted transaction 5.9%, one out of gas 14.2%, logs 3.7%, requests 0.8%, the child created again 12.3%, its own blob schedule 3.1%, at the DAO Fork block 0.9%; each fork family valid 4.6% to 9.5% |
| state machine: the transfers of a block leave the ledger of a model (`StateMachine`) | `applyTransaction` with a given sender, `checkInclusion`, `intrinsicGas`, `calldataFloor`, `effectiveGasPrice`, `settlement`, `BlockGas` | 27 forks (every one before Glamsterdam), legacy, access list and fee market transfers, the nonce, the balance, the gas limit and the fees at their edges, a block that a few transfers fill | a ledger of plain numbers, from the Yellow Paper and the EIPs | 3,000 sequences of up to 40 | a transfer entered 80.4%, three or more 33.3%; refused by balance 69.2%, intrinsic gas 51.3%, nonce 45.3%, block gas 40.6%, gas cap 14.1%, fee order 11.1%, base fee 10.7% (share of sequences) |
| a block passes the size rule exactly up to 8 MiB, from Fusaka | `validateBlockSize`, `MAX_RLP_BLOCK_SIZE` | 9 forks, a size from 1,000 bytes under the limit to 1,000 over | the number of EIP-7934 | 200 | over the limit from Fusaka 20.5%, over it before Fusaka 23.5%, at or under it 56.0% |
| scenario: a chain under commands, at each of 19 forks (`Command`, madhouse) | the same as the first and the third row, with `BlockChain.addBlock` and the fees of the next block from the last | the start nonces, the beneficiary, the base fee; commands: send a transfer, a call, a creation, a self-destruct, a blob transaction, a set code transaction, any, one of the three that destroy, create and call the child; a transaction that must be refused; a withdrawal; seal | EELS, one `process_transaction` per command and one `state_transition` per sealed block | 19 x 300 sequences of up to 50 | over the forks: a generated transaction entered its block 92.3% to 97.3%; a block was sealed 65.7% to 79.3%, one with three transactions or more 43.3% to 53.7%, a second block 41.0% to 62.0%; a transaction was refused 44.0% to 66.3%; each kind entered in 45% to 84% of the sequences; the child destroyed, created again and called up to 11.7%; no transaction that the model expected to enter was refused |
| a transaction at Glamsterdam leaves what the reference leaves | the first row with `StateGasMeter`: `allocateGas`, `transactionBlockGas`, `baseCost`, the state gas of the first frame, `clearAccountPreservingBalance` | the cases of the first row at one fork | EELS branch `forks/amsterdam`, `process_transaction` | 3,000 | valid 68.6%: ok 40.4%, out of gas 13.8%, revert 10.0%, other halt 4.5%; invalid 31.4%, each of 15 reasons 1.2% to 3.7%; types 0 to 4 valid 12.7% to 15.8% each |
| a block at Glamsterdam is valid as in the reference, and leaves the same state | the third row with `accessListHashOf`, `AccessListBuilder`, `BlockAccessList.hash`, the builder request contracts, `BlockGas.gasUsed` | the cases of the third row at one fork, and the hash of the block access list changed | EELS branch, `execute_block` | 3,000 | valid 57.1%, all with requests; refused at a transaction 12.4%, a system call 5.7%, a deposit 1.6%, the block access list hash 4.7%, each of 8 other fields 2.0% to 2.8% |
| DOC: a creation over storage alone at Glamsterdam ends as in the branch (`mustFail`) | `accountDeployable` | the gas limit and the value | EELS branch | 100 | fails at the first case, by design |

The first property, by fork family and by outcome, in percent of its 3,000 cases:

| Fork family | ok | revert | out of gas | other halt | invalid |
| --- | --- | --- | --- | --- | --- |
| Frontier to Tangerine Whistle | 3.3 | none exists | 2.4 | 2.2 | 3.9 |
| Spurious Dragon to Muir Glacier | 4.1 | 1.0 | 3.0 | 1.6 | 3.1 |
| Berlin | 2.8 | 0.5 | 1.5 | 0.6 | 1.6 |
| London to Gray Glacier | 4.4 | 0.8 | 2.5 | 1.4 | 2.8 |
| Paris | 2.8 | 0.6 | 1.6 | 0.9 | 2.6 |
| Shanghai | 2.8 | 1.0 | 1.4 | 0.6 | 2.7 |
| Cancun | 3.1 | 0.7 | 1.7 | 0.8 | 4.6 |
| Prague | 4.8 | 1.2 | 1.9 | 0.6 | 3.2 |
| Osaka to BPO5 | 5.0 | 1.0 | 2.0 | 0.8 | 7.9 |

The smallest cell is 15 cases.
REVERT exists from Byzantium, so in the second family it is the share of Byzantium to Muir Glacier.

Each fault is refused in 0.5% to 2.1% of the cases, but the five that sit exactly at an edge (the balance exact, the gas at the least, at what the block has left and at `2^24`, the fee at the base fee, the blob fee at the price), which are never refused, as they should not be.
The first runs showed that most blob faults were no fault at their fork; the shares above are after the fix.

## How the cases are made

- A world is about 30 accounts.
  The sender holds the cost of its transaction, one wei less, one wei more, or a fortune.
  Ten contracts are written by hand.
  They store two words, destroy themselves to an address, call an address with a value, create from their call data, log, revert, loop until the gas is gone and store a block hash.
  One emits a deposit event at the deposit contract of mainnet.
  One is a factory that creates the same child with CREATE2; the child counts its calls and destroys itself when asked, so that it can be created again.
  One account holds a generated program of the EVM driver with two callees.
  Four accounts hold a delegation indicator of EIP-7702: to a contract, to a precompile, to a delegated account and to itself.
  From Dencun the world holds the system contracts of EIP-4788, 2935, 7002 and 7251 with the code that their EIPs give.
  An account that exists and is empty is there in a third of the worlds, at every fork.
- The beneficiary is absent, empty, funded, the sender, a contract or a precompile.
- A transaction does one of 18 things, and has at most one of 29 faults.
  A fault puts one field at the edge of a rule:
  - the nonce one too low and one too high;
  - the balance one wei short, and exact;
  - the gas limit one under the least, and at it;
  - the gas limit one over what the block has left, and at it;
  - the gas limit one over `2^24`, and at it;
  - the maximum fee one under the base fee, and at it;
  - the priority fee over the maximum fee;
  - the blob fee one under the price, and at it;
  - a blob hash of another version, no blob, more blobs than the block has left, seven blobs;
  - a sender with code, and a sender with a delegation indicator;
  - another chain, a chain named before Spurious Dragon, a high `s`, an `r` of 0;
  - a blob or set code transaction that creates, no authorization, a type of a later fork;
  - init code one byte over the limit, and at it.

  Four cases in five are drawn at a fork where the fault can bite.
- An authorization of EIP-7702 names another chain, a wrong nonce, a bad signature, the zero address, a precompile or the sender itself now and then.
  Its authority has no account, a plain one, a delegated one or a contract.
- A creation by a transaction meets an account at its address four times in nine.
  That account has a nonce, code, storage alone or a balance alone.
- A block has up to six transactions of four senders, withdrawals, ommers of each age from one to seven, a parent whose gas used and blob gas move the fees, and a chain from its first block or of 254 to 300 blocks.
  One block in ten has a transaction that may not enter it, and three in ten have one field of their header changed after the reference built it.

## Findings

No BUG and no OPEN finding.

### DOC: a creation over storage alone, at Glamsterdam

- Classification: DOC, a choice that the maintainers wrote down, and no deviation from the source that the module cites.
- Definition: `accountDeployable`, `EthLib/Execution/State/Tracker.lean:263`, read by `prepareFirstFrame` (`Transactions/Process.lean:290`) and by CREATE.
- Counterexample, shrunk in 23 steps: at Glamsterdam, a legacy transaction with no recipient and no init code, gas limit 324000, gas price 7, from a sender with nonce 0.
  The address that it creates holds an account with nonce 0, no code, balance 0 and one word of storage.
- EthLib: the message halts with an address collision, and the block counts `324000/0` gas (execution and state).
- The reference: the creation succeeds, and the block counts `24000/183600`.
  Its `account_deployable` (`forks/amsterdam/state_tracker.py`) reads the nonce and the code hash only.
- EIP-7610, fetched on 2026-11-20 and in Last Call, refuses a creation when "the destination address already has either a nonzero nonce, a nonzero code length, or non-empty storage".
  It says "then the creation MUST throw as if the first byte in the init code were an invalid opcode".
- EIP-8037, fetched the same day and in Last Call, says in "Gas accounting for new accounts": "A nonzero balance or non-empty storage alone does not cause a collision."
  It does not name EIP-7610.
- `EthLib/Execution/Evm/Call/Create.lean` says: "EIP-8037 says that storage alone causes no collision; EthLib follows EIP-7610 there."
  The CHANGELOG has the entry of that choice ("A contract creation now fails at an address with non-empty storage, at every fork").
- So the two EIPs disagree at Glamsterdam and EthLib chose one in writing.
  The generators leave the case out at Glamsterdam, and one property keeps it failing in a group of its own, so that a change on either side shows.
- A standalone reproduction of the rule:

      import EthLib.Execution.State
      open EthLib.Base EthLib.Execution.State

      def address : Address := Vector.replicate 20 0xaa

      -- An account with nonce 0, no code, and one word of storage.
      def state : State :=
        ⟨(∅ : Std.ExtTreeMap Address Account).insert address EMPTY_ACCOUNT,
         (∅ : Std.ExtTreeMap Address _).insert address
           ((∅ : Std.ExtTreeMap Bytes32 U256).insert (Vector.replicate 32 0) 1), ∅⟩

      #eval (TransactionState.ofBlock ⟨state, ∅, ∅, ∅, ∅⟩).accountDeployable address  -- false

- Command: `HEDGEHOG_ONLY=DOC lake exe transition-property 100`.

### Harness mistakes, each fixed

- The blob gas used before a transaction was set at forks before Dencun, where the reference has no such count.
- The oracle copied a state with `copy.deepcopy`, which the frozen dataclasses of EELS refuse; it now copies the tries.
- A typed transaction with an empty recipient made EELS raise a `DecodingError` of its RLP library, which is not one of its own exceptions: counted as a refusal.
- A chain of one or two recent blocks at block 9 made the reference raise `IndexError` in BLOCKHASH.
  EELS takes a chain that holds every block from its first one, so a generated chain now does, or holds 254 blocks and more.
- A command that sends a transaction with a nonce too low had no `check`: once an earlier command was shrunk away, its nonce was the right one.
  It now holds the nonce it was made for.
- The reasons of a refusal first lacked `BlobCountExceededError` of Osaka.
- The oracle ran the body before it checked the header, so a block with a wrong DAO extra data and a bad transaction was refused at another place than in EthLib.
- Ages of ommers were drawn up to the length of the chain, so on a long chain nearly every ommer was too old.

## Not covered

- Hegotá, which EthLib does not specify.
- At Glamsterdam: no scenario of commands and no chain of several blocks, only one transaction and one block.
  The builder request contracts hold code made up here (one returns five bytes, one nothing), since no EIP gives their code.
  The blob schedule is the one of BPO2 only.
  The reasons of a refusal are not compared there.
- The seal of a header (Ethash), with `checkSeal` off on both sides.
- A parent at an earlier fork than its block, but for the first block of the DAO Fork after Homestead.
  So the first London block (the initial base fee and the doubled gas limit) and the first block of each later fork are not run as wholes.
- `daoTransfer` on a chain where a later fork activates at the block of the DAO Fork: EthLib then moves the ether at that later fork, and EELS has no such chain.
- The fork of a block against the chain (`wrongFork`): the reference has no such check.
- A block near 8 MiB through `stateTransition`: only `validateBlockSize` is tested at the limit, on a block with one padded item.
- Balances near `2^256` and nonces near `2^64`: `creditEther` and `incrementNonce` at their overflow are not reached.
- What a simulation changes: `LiftedRules`, the precompile overrides and `blobGasPrice`.
  The ledger machine gives the sender through `BodyOverrides.senders`, and no other override is used.
- Which error halts a message: only ok, revert and halt are compared, with out of gas as a halt.
- Blob schedules that a chain sets other than those of Osaka, BPO1 and BPO2, and a schedule that activates after the first block.
- Ommers of recent blocks (`ommerAlreadyIncluded`), since no recent block of a generated chain has ommers.
- More than three withdrawals, authorizations or access list entries, and more than six transactions in the block property (a scenario reaches dozens).
- Creations at the code size limit and init code at its limit inside a block: they are in the property of one transaction only.
- Precompiles with real inputs inside a transaction: a call reaches each precompile address with no input, which shows the warm set and nothing of the precompile.
- The receipts and the logs of a block are compared through the receipts root and the logs Bloom only, and those of one transaction byte by byte.
- `tests/property/README.md` has no row for this driver: it is not a file of this layer.

## Notes on lean-hedgehog 0.3.0

The driver uses a property with coverage, a `StateMachine` whose model is plain numbers, and a scenario of `Command`s at 19 forks.

What helped:

- The context first in `check`, `apply` and `next`.
  The commands of the scenario hold a transaction and nothing else; the oracle, the keys and the fork are in the context.
  The earlier drivers copied the context into each command, and here no command does.
- A state indexed by a value: `instance {fork : Fork} {kind : String} : Command (Send fork kind) (ChainState fork) (ChainContext fork) IO` is written once, and the body of a block keeps its type `BodyOutput fork` with no `Σ`.
- `buildIn` and `next`: the state holds the nonce of each sender as a number, `next` moves it, and `buildIn` draws the next transaction at that nonce.
  In 500 sequences of up to 50 commands at each of 19 forks, no transaction that the model expected to enter was refused.
  Without `next` nearly all after the first of a sender would be.
  The same two functions keep the count of blobs of the open block, so a blob transaction is drawn only while the block has room.
- `scenarioFrom` with a `setup`: the start state (four nonces, a beneficiary, a chain) is generated and shrunk, and the setup opens the chain in the oracle and decodes its headers.
  The range of lengths (`.linear 1 50`) reaches a second and a third sealed block, which 15 commands rarely did.
- `applySut` with the state before: the transfer of the ledger machine is built from the ledger before it (its nonce is the nonce of the sender plus a skew, its gas limit the least gas plus a spare), and compared with the ledger after it.
  The model needs no copy of its last state.
- Coverage found four weak generators that passing properties hid.
  Blob faults were drawn at every fork, so four in five were no fault at all: the shares "fault: blobFeeBelow, refused" said 0.3%.
  Ommers on a chain of 256 blocks were nearly always too old ("invalid ommers" 15% beside "valid with ommers" 12%).
  A revert was 1.8% of the cases, and under 0.2% in most fork families.
  "valid with requests" was 0.3%.
  Each was fixed from its share, and `cover` now guards the main ones.
- `label` with a computed name gives a two-way table for free: `label s!"{family fork}: {outcome}"` is how "each outcome at each fork" was checked.
- `Selection.fromEnv`: `HEDGEHOG_ONLY` with a part of a name was used in nearly every run, to rerun one property of 27 after a change.
- `mustFail`: the group of the documented difference prints its counterexample at each run and does not change the exit code.
- Shrinking: the first harness failure shrank in 15 steps to a plain transfer, the BLOCKHASH failure to one transaction with a distance of 3 on a chain of one block, and the finding of Glamsterdam in 23 steps to a creation with no init code and no value.
  Each shrunk case named its cause at a glance.

What was awkward:

- The report lists the labels in the order they first occurred.
  With a hundred labels of the form `family: outcome` the table is unreadable until it is piped through `sort`.
  Sorting by name, or a `tabulate "table" "row"` as QuickCheck has, would do.
- `classify name false` adds a row of 0.0% for the name.
  With a computed name this prints rows that describe nothing ("expected to enter, refused: ok 0.0%"), and each call had to move under an `if`.
- A command that `buildIn` makes for a state holds an assumption about that state, and nothing says so until a shrink or an earlier refusal breaks it.
  `REFUSE (nonce too low)` was made for nonce 1; once the command before it was gone its nonce was the right one, and the shrunk report showed a single valid transaction under the name of a refusal.
  USAGE says that `check` skips such commands, but the author must think of storing the nonce in the command and comparing it in `check`.
  A sentence in USAGE with this very example would have saved the detour.
- Madhouse draws the commands uniformly, and the only weight is to list a command twice (`Seal` is listed twice here).
  A weight per entry, as `Gen.frequency` has, is missing.
- A scenario cannot draw the value that indexes its state: the context is one value for the whole property.
  So there is one property per fork, 19 of them, each with a tenth of the cases, where one scenario over a drawn fork would spread the cases itself.
- The size grows with the number of the test, so a property that is run 30 times sees sequences of at most 15 commands of the 50 its range allows.
  A slow scenario wants few, long sequences: a way to start at a larger size is missing (a range of `.constant` lengths is the workaround).
- `HEDGEHOG_ONLY=block` also selects "the transfers of a block": the parts match anywhere in a name, and there is no way to ask for one exact name.
- The start state of `scenarioFrom` is not in the report, as USAGE says.
  Annotating it in the setup works, and prints 30 accounts for each failure.
- The list of commands of a scenario needed its type written out once the `Send` commands came from a `List.map` over the kinds: `List (ChainContext fork → ChainState fork → Gen (CommandWrapper (ChainState fork) IO))`.

Little used:

- `HEDGEHOG_RECHECK` was run once, on the case of the documented difference, and replayed it.
  It was not needed otherwise: each failure came back on the next run within a few hundred cases.

No bug of the library was met.

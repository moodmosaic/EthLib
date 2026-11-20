import Property.Transition.World

/-!
# The transfers of one block against a ledger of plain numbers

A state machine runs a sequence of transfers of ether in one block of EthLib.

Its model is a ledger: a nonce and a balance for each party, and the gas that the block used.

The model is written from the Yellow Paper (6.2) and from EIP-1559, 2028, 2930, 7623 and 7825.

No reference process takes part, so it runs at every fork of EthLib before Glamsterdam.

Those are also the forks that the Python execution-specs have no module for.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution
open EthLib.Execution.Transactions EthLib.Execution.Blocks EthLib.Execution.Evm
open EvmProperty (PreAccount addressOf word32 preState)

namespace TransitionProperty

/-- Every fork before Glamsterdam, whose transfers follow the rules above. -/
def ledgerForks : List Fork := [.frontier, .homestead, .daoFork, .tangerineWhistle,
  .spuriousDragon, .byzantium, .constantinople, .petersburg, .istanbul, .muirGlacier, .phase0,
  .berlin, .london, .altair, .arrowGlacier, .grayGlacier, .bellatrix, .paris, .shapella, .dencun,
  .pectra, .fusaka, .bpo1, .bpo2, .bpo3, .bpo4, .bpo5]

/-- The ledger of a block: the model. -/
structure Ledger where
  fork : Fork
  baseFee : Nat
  gasLimit : Nat
  /-- The gas that the transfers so far used. -/
  gasUsed : Nat
  /-- The nonce of each of the four parties. -/
  nonces : List Nat
  /-- The balance of each of the four parties, then of the beneficiary. -/
  balances : List Nat
  /-- The party that is the beneficiary of the block, or 4 for an account of its own. -/
  beneficiary : Nat
  /-- The wei that the base fee burned. -/
  burned : Nat
  /-- The number of transfers that entered the block. -/
  included : Nat
  /-- Why the last transfer was refused, if it was. -/
  refused : Option String

instance : Repr Ledger where
  reprPrec s _ := s!"{s.fork.name} baseFee={s.baseFee} gasLimit={s.gasLimit} \
    gasUsed={s.gasUsed} nonces={s.nonces} balances={s.balances} beneficiary={s.beneficiary} \
    burned={s.burned} refused={s.refused}"

/-- A transfer of ether between two parties, with the fields at the edges of the rules. -/
structure Payment where
  sender : Nat
  recipient : Nat
  value : Nat
  /-- Whether the transfer has a maximum fee and a priority fee, as EIP-1559 adds. -/
  feeMarket : Bool
  /-- The price above the base fee, or the priority fee. -/
  tip : Nat
  /-- The maximum fee minus the base fee. -/
  room : Int
  /-- The zero bytes and the other bytes of the data. -/
  zeros : Nat
  others : Nat
  /-- The addresses and the storage keys of the access list. -/
  addresses : Nat
  keys : Nat
  /-- The gas limit minus the least gas limit. -/
  spare : Int
  /-- The nonce minus the nonce of the sender. -/
  skew : Int
  deriving Repr, BEq

/-- The address of a party, or of the beneficiary that is no party. -/
def partyAddress (index : Nat) : Address :=
  if index < 4 then addressOf (0xa0 + UInt8.ofNat index) 0x77 else addressOf 0xba 0x5e

/-- The base fee that a ledger charges: none before London. -/
def Ledger.base (s : Ledger) : Nat := if s.fork ≥ .london then s.baseFee else 0

/-- The intrinsic gas of a transfer: 21000, the data and the access list.

A zero byte costs 4 gas, and another byte 68, or 16 from Istanbul (EIP-2028).

An address of the access list costs 2400 gas and a storage key 1900 (EIP-2930). -/
def Ledger.intrinsic (s : Ledger) (p : Payment) : Nat :=
  21000 + 4 * p.zeros + (if s.fork ≥ .istanbul then 16 else 68) * p.others +
    2400 * p.addresses + 1900 * p.keys

/-- The least gas limit of a transfer, which is also the gas that it uses.

From Pectra it is at least the floor of EIP-7623: 21000 and 10 gas per token of data. -/
def Ledger.least (s : Ledger) (p : Payment) : Nat :=
  if s.fork ≥ .pectra then max (s.intrinsic p) (21000 + 10 * (p.zeros + 4 * p.others))
  else s.intrinsic p

/-- The gas limit of a transfer. -/
def Ledger.gasOf (s : Ledger) (p : Payment) : Nat := ((s.least p : Int) + p.spare).toNat

/-- The most that a transfer pays per gas. -/
def Ledger.maxFee (s : Ledger) (p : Payment) : Nat :=
  if p.feeMarket then ((s.base : Int) + p.room).toNat else s.base + p.tip

/-- The nonce of a transfer. -/
def Ledger.nonceOf (s : Ledger) (p : Payment) : Nat :=
  ((s.nonces.getD p.sender 0 : Int) + p.skew).toNat

/-- Why a ledger refuses a transfer, or none. -/
def Ledger.refusal (s : Ledger) (p : Payment) : Option String :=
  let gas := s.gasOf p
  if gas < s.least p then some "intrinsic gas"
  else if s.fork ≥ .fusaka ∧ gas > 2 ^ 24 then some "gas cap"
  else if p.feeMarket ∧ p.tip > s.maxFee p then some "fee order"
  else if gas > s.gasLimit - s.gasUsed then some "block gas"
  else if s.maxFee p < s.base then some "base fee"
  else if s.nonceOf p ≠ s.nonces.getD p.sender 0 then some "nonce"
  else if s.balances.getD p.sender 0 < gas * s.maxFee p + p.value then some "balance"
  else none

/-- The ledger after a transfer.

The sender pays the gas used at the price per gas, and the value.

The beneficiary gets the price above the base fee, and the base fee is burned. -/
def Ledger.apply (s : Ledger) (p : Payment) : Ledger :=
  match s.refusal p with
  | some reason => { s with refused := some reason }
  | none =>
    let used := s.least p
    let price := if p.feeMarket then min p.tip (s.maxFee p - s.base) + s.base else s.base + p.tip
    let add (index amount : Nat) (balances : List Nat) : List Nat :=
      balances.set index (balances.getD index 0 + amount)
    let balances := s.balances.set p.sender (s.balances.getD p.sender 0 - used * price - p.value)
    let balances := add p.recipient p.value balances
    let balances := add s.beneficiary (used * (price - s.base)) balances
    { s with
      gasUsed := s.gasUsed + used
      nonces := s.nonces.set p.sender (s.nonces.getD p.sender 0 + 1)
      balances
      burned := s.burned + used * s.base
      included := s.included + 1
      refused := none }

/-- The transaction of EthLib for a transfer on a ledger. -/
def Ledger.transaction (s : Ledger) (p : Payment) : Transaction :=
  let u (n : Nat) : U256 := BitVec.ofNat 256 n
  let data : ByteArray := bytesOf (List.replicate p.zeros 0 ++ List.replicate p.others 0x5a)
  let accessList : List Access := (List.range p.addresses).map fun i =>
    ⟨numberAddress (0x7000 + i), if i = 0 then (List.range p.keys).map word32 else []⟩
  let to := some (partyAddress p.recipient)
  if p.feeMarket then
    .feeMarket {
      chainId := 1, nonce := u (s.nonceOf p), maxPriorityFeePerGas := u p.tip,
      maxFeePerGas := u (s.maxFee p), gas := u (s.gasOf p), to, value := u p.value, data,
      accessList, yParity := 0, r := 0, s := 0 }
  else if p.addresses > 0 then
    .accessList {
      chainId := 1, nonce := u (s.nonceOf p), gasPrice := u (s.maxFee p), gas := u (s.gasOf p),
      to, value := u p.value, data, accessList, yParity := 0, r := 0, s := 0 }
  else
    .legacy {
      nonce := u (s.nonceOf p), gasPrice := u (s.maxFee p), gas := u (s.gasOf p), to,
      value := u p.value, data, v := 0, r := 0, s := 0 }

/-- A ledger at its start: any fork, a block that a few transfers fill, and four parties.

One party is rich, one holds about the cost of a transfer, and one holds nothing. -/
def genLedger : Gen Ledger := do
  let fork ← Gen.element ledgerForks
  let baseFee ← Gen.element [7, 0, 1000]
  let gasLimit ← Gen.frequency [(1, pure 30000000), (1, Gen.nat (.linear 21000 150000))]
  let modest ← Gen.nat (.linear 0 60000)
  let beneficiary ← Gen.element [4, 4, 0, 3]
  let held ← Gen.element [0, 5]
  let nonces ← Gen.list (.singleton 4) (Gen.element [0, 1, 9])
  pure ⟨fork, baseFee, gasLimit, 0, nonces, [10 ^ 18, modest * (baseFee + 3), 0, 0, held],
    beneficiary, 0, 0, none⟩

/-- A transfer for a ledger: its type is one that the fork has, and its fields sit at the edges.

The value is now and then all that the sender holds past the gas, or one wei more. -/
def genPayment (s : Ledger) : Gen Payment := do
  let sender ← Gen.frequency [(3, pure 0), (3, pure 1), (1, pure 2)]
  let recipient ← Gen.nat (.constant 0 4)
  let feeMarket ← if s.fork ≥ .london then Gen.bool else pure false
  let tip ← Gen.element [0, 1, 3]
  let room ← if feeMarket then Gen.frequency [(6, Gen.element [0, 1, 3, 5]), (1, pure (-1))]
    else pure 0
  let zeros ← Gen.nat (.linear 0 40)
  let others ← Gen.nat (.linear 0 40)
  let addresses ← if s.fork ≥ .berlin then Gen.nat (.constant 0 2) else pure 0
  let keys ← if addresses > 0 then Gen.nat (.constant 0 3) else pure 0
  let spare ← Gen.frequency [(4, pure 0), (4, Gen.int (.linear 0 30000)), (1, pure (-1)),
    (1, pure (2 ^ 24 - 21000 : Int)), (1, pure (2 ^ 24 - 20999 : Int))]
  let skew ← Gen.frequency [(10, pure 0), (1, pure 1), (1, pure (-1))]
  let draft : Payment :=
    ⟨sender, recipient, 0, feeMarket, tip, room, zeros, others, addresses, keys, spare, skew⟩
  let rest := s.balances.getD sender 0 - s.gasOf draft * s.maxFee draft
  let value ← Gen.frequency [(4, Gen.nat (.linear 0 1000)), (2, pure rest), (1, pure (rest + 1))]
  pure { draft with value }

/-- The model of a block of transfers. -/
def ledgerModel : Model Ledger Payment where
  initState := genLedger
  transitions := genPayment
  apply := Ledger.apply
  -- A shrunk sequence keeps only the transfers of a type that the fork has.
  preconditions s p := (!p.feeMarket || s.fork ≥ .london) && (p.addresses = 0 || s.fork ≥ .berlin)

/-- The block of EthLib that a ledger describes, before its first transfer. -/
def ledgerBody (s : Ledger) : BodyOutput s.fork :=
  let accounts : List PreAccount := (List.range 5).filterMap fun i =>
    let balance := s.balances.getD i 0
    let nonce := s.nonces.getD i 0
    if balance = 0 ∧ nonce = 0 then none else some ⟨partyAddress i, nonce, balance, .empty, []⟩
  bodyStart s.fork (preState accounts) ⟨0, 0, 0⟩

/-- The block environment of a ledger. -/
def ledgerEnv (s : Ledger) (fork : Fork) : BlockEnvironment fork :=
  let env : EnvSpec :=
    ⟨1000, 1700000000, s.gasLimit, s.baseFee, partyAddress s.beneficiary, 0x20000, 0x11, 0, 0, 0,
      none⟩
  env.toEnv fork

/-- A sequence of transfers in one block leaves the nonces, balances and gas of a ledger.

The ledger says which transfers the block refuses, and EthLib must refuse exactly those.

A refused transfer leaves the block as it was.

After each transfer the gas used, each nonce and each balance are those of the ledger.

The transfer is built from the ledger before it: its nonce, its gas limit and its fees.

A long run asks for a share of sequences that fill a block with three transfers. -/
def ledgerMachine (long : Bool) :
    StateMachine Ledger Payment ((fork : Fork) × BodyOutput fork) IO where
  toModel := ledgerModel
  initSut s := pure ⟨s.fork, ledgerBody s⟩
  applySut sut before after p := do
    let ⟨fork, body⟩ := sut
    let tx := before.transaction p
    let overrides : BodyOverrides := { senders := fun _ => some (partyAddress p.sender) }
    match applyTransaction (ledgerEnv before fork) before.included body tx overrides with
    | .ok next =>
      annotate s!"EthLib includes the transfer; the ledger says {after.refused}"
      ensure after.refused.isNone "EthLib includes a transfer that the ledger refuses"
      pure ⟨fork, next⟩
    | .error (.invalidTransaction _ e) =>
      annotate s!"EthLib refuses with {reprStr e}; the ledger says {after.refused}"
      after.refused === some (reasonOf e)
      pure sut
    | .error e => failWith s!"the block fails with {reprStr e}"
  invariants sut s := do
    let ⟨_, body⟩ := sut
    let state := body.block.applyChanges
    let account (i : Nat) := state.accounts[partyAddress i]?
    body.gas.execution === s.gasUsed
    body.cumulativeGasUsed === s.gasUsed
    body.receipts.length === s.included
    (List.range 4).map (fun i => ((account i).map (·.nonce)).getD 0) === s.nonces
    (List.range 5).map (fun i => ((account i).map (·.balance.toNat)).getD 0) === s.balances
    -- A short run stays at small sizes, where a sequence is a few transfers.
    cover (if long then 25 else 0) "a transfer entered the block" (s.included > 0)
    cover (if long then 10 else 0) "three transfers or more entered the block" (s.included ≥ 3)
    match s.refused with
    | some reason => classify s!"refused: {reason}" true
    | none => pure ()
    classify s!"fork: {family s.fork}" true

end TransitionProperty

import Property.Protocols.World
import EthLib.Consensus.InclusionList
import EthLib.Cryptography.Hash.Sha256

/-!
# The store of inclusion lists of Heze, as a scenario of commands

A member of the inclusion list committee sends a signed list of transactions for a slot.

The store keeps the first list of each member, and marks a member that sends two different ones.

The commands are a list from a member, the same list once more, and another list of that member.

They are drawn in any order in madhouse mode, over long sequences.

The oracle keeps the store of consensus-specs and runs `process_inclusion_list` on it.

After every command both sides must hold the same members, equivocators and transactions.

They must also agree on the bits of a committee, and on whether given bits include them.

The size of the committee is a value of the preset, so the scenario draws the preset too.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ListsProperty

/-- The oracle and the preset of a scenario. -/
structure Node where
  /-- The oracle. -/
  oracle : Oracle
  /-- The preset, as the oracle takes it. -/
  presetKey : String
  /-- The preset. -/
  preset : Preset
  /-- Whether the run is long enough to ask for the minimums of coverage. -/
  long : Bool

/-- What a list is made of: its slot, the number of its root, its member and its transactions. -/
structure Sent where
  /-- The slot. -/
  slot : Nat
  /-- The number of the dependent root. -/
  root : Nat
  /-- The member. -/
  member : Nat
  /-- The transactions, as numbers of a small pool. -/
  transactions : List Nat
  deriving Repr, BEq

/-- The state of a scenario: the lists sent so far, and EthLib's store. -/
structure Frame where
  /-- The lists sent so far, the latest first. -/
  sent : List Sent := []
  /-- The store. -/
  store : InclusionListStore := .empty
  deriving Inhabited

/-- The dependent root of a number, as the oracle makes it. -/
def rootOf (number : Nat) : Root :=
  let hash := Cryptography.Hash.sha256 ("dependent".toUTF8 ++ ⟨#[UInt8.ofNat number]⟩)
  Vector.ofFn fun i : Fin 32 => hash[i.val]!

/-- The first four bytes of a root in hexadecimal. -/
def short (root : Root) : String := String.ofList ((hex ⟨root.toArray⟩).toList.take 8)

/-- The transactions that count at a key, sorted, as the oracle writes them. -/
def transactionsText (store : InclusionListStore) (slot : Consensus.Slot) (root : Root)
    (onlyTimely : Bool) : String :=
  let shown := (store.transactions slot root onlyTimely).map fun t => hex ⟨t.data⟩
  ",".intercalate (shown.toArray.qsort (· < ·)).toList

/-- What the oracle writes of its own store, for the keys that got a list. -/
def view (frame : Frame) : String :=
  let keys := (frame.sent.map fun sent => (sent.slot, sent.root)).eraseDups
  let ordered := keys.toArray.qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && hex ⟨(rootOf a.2).toArray⟩ < hex ⟨(rootOf b.2).toArray⟩)
  let parts := ordered.toList.map fun (slot, number) =>
    let root := rootOf number
    let members := (frame.store.inclusionLists slot.toUInt64 root).map fun (m, _) => toString m
    let equivocators := ((frame.store.equivocators slot.toUInt64 root).map (·.toNat)).toArray.qsort
      (· < ·)
    ":".intercalate [toString slot, short root, ",".intercalate members,
      ",".intercalate (equivocators.toList.map toString),
      transactionsText frame.store slot.toUInt64 root true,
      transactionsText frame.store slot.toUInt64 root false]
  if parts.isEmpty then "-" else " ".intercalate parts

/-- Send a list to both stores, and compare them after. -/
def send (node : Node) (frame : Frame) (sent : Sent) (timely : Bool) : TestT IO Frame := do
  let numbers := if sent.transactions.isEmpty then "-"
    else ",".intercalate (sent.transactions.map toString)
  let answer ← node.oracle.ask ["pi_receive", toString sent.slot, toString sent.root,
    toString sent.member, numbers, if timely then "1" else "0"]
  let [listHex, expected] := answer.splitOn "\t" | failWith "pi_receive: a malformed answer"
  let some bytes := unhex? listHex | failWith "the oracle sent no hexadecimal list"
  match SszType.deserialize SignedInclusionList bytes with
  | .error e => failWith s!"EthLib does not read the list of the reference: {repr e}"
  | .ok signed =>
    let slot := sent.slot.toUInt64
    let root := rootOf sent.root
    let before := (frame.store.equivocators slot root).length
    let store := frame.store.process signed timely
    cover (if node.long then 10 else 0) "a list was equivocated"
      ((store.equivocators slot root).length > before)
    classify "a first list of a member"
      ((store.inclusionLists slot root).length > (frame.store.inclusionLists slot root).length)
    let frame := { sent := sent :: frame.sent, store }
    view frame === expected
    pure frame

/-- A list from a member, mostly a new one. -/
structure Receive where
  /-- What the list holds. -/
  sent : Sent
  /-- Whether it came before the deadline. -/
  timely : Bool
  deriving Repr

/-- The transactions of a list: a few of a pool of eight, so that lists share some. -/
def genTransactions : Gen (List Nat) := Gen.list (.linear 0 5) (Gen.nat (.constant 0 7))

instance : Command Receive Frame Node IO where
  apply node c frame := send node frame c.sent c.timely
  label c := s!"RECEIVE({repr c.sent}, timely {c.timely})"
  build _ := do
    let slot ← Gen.element [5, 6]
    let root ← Gen.nat (.constant 0 1)
    let member ← Gen.nat (.linear 0 9)
    Receive.mk ⟨slot, root, member, ← genTransactions⟩ <$>
      Gen.frequency [(3, pure true), (1, pure false)]

/-- A list that a member already sent, once more or with other transactions. -/
structure Repeat where
  /-- Which of the lists sent so far, counted from the latest. -/
  back : Nat
  /-- The transactions to send in place of the first ones, if any. -/
  other : Option (List Nat)
  /-- Whether it came before the deadline. -/
  timely : Bool
  deriving Repr

instance : Command Repeat Frame Node IO where
  check _ c frame := c.back < frame.sent.length
  apply node c frame :=
    match frame.sent[c.back]? with
    | none => failWith "no such list"
    | some first =>
      send node frame { first with transactions := c.other.getD first.transactions } c.timely
  label c := s!"REPEAT({c.back}, {repr c.other}, timely {c.timely})"
  build _ := pure ⟨0, none, true⟩
  next _ _ frame := { frame with sent := (frame.sent.headD ⟨0, 0, 0, []⟩) :: frame.sent }
  buildIn _ frame := do
    let back ← Gen.nat (.constant 0 (frame.sent.length - 1))
    let other ← Gen.frequency [(1, pure none), (2, some <$> genTransactions)]
    Repeat.mk back other <$> Gen.bool

/-- The bits of a committee, and whether given bits include them. -/
structure Bits where
  /-- The slot. -/
  slot : Nat
  /-- The number of the dependent root. -/
  root : Nat
  /-- The members of the committee, as many as the preset has seats. -/
  committee : List Nat
  /-- The bits to test. -/
  bits : List Bool
  deriving Repr

instance : Command Bits Frame Node IO where
  apply node c frame := do
    let size := node.preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat
    let committee : InclusionListCommittee node.preset :=
      Vector.ofFn fun i => (c.committee.getD (i.val % c.committee.length) 0).toUInt64
    let given : InclusionListBits node.preset :=
      ⟨Vector.ofFn fun i => c.bits.getD (i.val % c.bits.length) false⟩
    let expected ← node.oracle.ask ["pi_bits", toString c.slot, toString c.root,
      ",".intercalate ((List.range size).map fun i =>
        toString (c.committee.getD (i % c.committee.length) 0)),
      ",".intercalate ((List.range size).map fun i =>
        if c.bits.getD (i % c.bits.length) false then "1" else "0")]
    let slot := c.slot.toUInt64
    let root := rootOf c.root
    let shown (onlyTimely : Bool) : List String :=
      let own := frame.store.bits committee slot root onlyTimely
      [String.join (own.bits.toList.map fun b => if b then "1" else "0"),
        if frame.store.isInclusive committee slot root given onlyTimely then "t" else "f"]
    classify "bits: some seat has a list" ((shown false).head!.contains '1')
    classify "bits: the given bits do not include them" ((shown false).getLast! == "f")
    " ".intercalate (shown true ++ shown false) === expected
    pure frame
  label c := s!"BITS({c.slot}, {c.root}, {c.committee}, {c.bits})"
  build _ := do
    let slot ← Gen.element [5, 6]
    let root ← Gen.nat (.constant 0 1)
    let committee ← Gen.list (.linear 1 16) (Gen.nat (.linear 0 9))
    Bits.mk slot root committee <$> Gen.list (.linear 1 16) Gen.bool

/-- The store of inclusion lists of EthLib follows consensus-specs on every sequence. -/
def madhouse (oracle : Oracle) (long : Bool := true) : Property IO := propertyM do
  let presetKey ← forAllWith id (Gen.element ["minimal", ProtocolsProperty.oddTime,
    ProtocolsProperty.tiny, ProtocolsProperty.shortMainnet])
  let node : Node :=
    ⟨oracle, presetKey, (ProtocolsProperty.World.ofKeys presetKey "-").preset, long⟩
  (scenario .madhouse node [Command.gen Receive, Command.gen Receive, Command.gen Repeat,
    Command.gen Repeat, Command.gen Bits] (.linear 1 100) fun frame => do
      let _ ← node.oracle.ask ["pi_init", presetKey]
      pure frame).test

end ListsProperty

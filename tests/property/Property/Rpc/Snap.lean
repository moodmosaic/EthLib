import Property.Rpc.Wire

/-!
# The account ranges of snap

A node that syncs asks for a range of accounts, checks it against its proof, and asks for the next.

The state machine here is that walk: the model holds the accounts and where the next range starts.

The peer is `oracle/rpc_wire.py`, which cuts each range from a trie of py-trie with its proof.

Some answers are changed on the way, and the check must refuse each of them.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Network
open EthLib.Serialization.Rlp

namespace RpcProperty

/-- The root of the empty trie, as the Yellow Paper gives it. -/
def emptyRootHex : String := "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

/-- The hash of the empty code. -/
def emptyCodeHex : String := "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

/-- An account as snap sends it and as the state trie holds it. -/
structure SlimPair where
  slim : ByteArray
  full : ByteArray

/-- An account in both forms: an absent root or code hash is the empty string in the slim one. -/
def genSlimPair : Gen SlimPair := do
  let nonce ← Gen.element [0, 1, 300]
  let balance ← Gen.element [0, 1, 10 ^ 18]
  let root ← Gen.frequency [(1, pure none), (1, some <$> genBytesN 32)]
  let code ← Gen.frequency [(1, pure none), (1, some <$> genBytesN 32)]
  let item (slim : Bool) : Item := .list [numberItem nonce, numberItem balance,
    .bytes (root.getD (if slim then .empty else (unhex? emptyRootHex).getD .empty)),
    .bytes (code.getD (if slim then .empty else (unhex? emptyCodeHex).getD .empty))]
  pure ⟨(encode (item true)).toOption.getD .empty, (encode (item false)).toOption.getD .empty⟩

/-- The walk of a node over the accounts of a trie. -/
structure Walk where
  /-- The accounts by their keys, in order. -/
  entries : List (Nat × SlimPair)
  /-- The key from which the next range starts. -/
  next : Nat
  /-- The accounts received so far. -/
  received : Nat

instance : Repr Walk where
  reprPrec w _ := s!"{w.entries.length} accounts, next {hexVec (word32 w.next)}, \
    received {w.received}"

/-- A step of the walk: a range of some accounts, or one that is changed on the way. -/
inductive Step where
  | ask (count : Nat)
  | changed (count kind : Nat)
  deriving Repr

/-- The accounts that a range of `count` holds from a key on. -/
def Walk.range (w : Walk) (count : Nat) : List (Nat × SlimPair) :=
  (w.entries.filter fun e => e.1 ≥ w.next).take count

/-- The model of the walk: a range moves the start past its last key. -/
def walkModel : Model Walk Step where
  initState := do
    -- Keys that share long prefixes, so that the trie has extensions and branches.
    let key : Gen Nat := Gen.zipWith (fun (high low : Nat) => high * 256 ^ 31 + low)
      (Gen.element [0, 0x10, 0x11, 0xff]) (Gen.frequency [(3, Gen.nat (.constant 0 40)),
        (1, (· * 256 ^ 20) <$> Gen.nat (.constant 1 3))])
    let keys ← Gen.list (.linear 1 14) key
    let sorted := keys.eraseDups.mergeSort (· ≤ ·)
    let pairs ← Gen.list (.singleton sorted.length) genSlimPair
    pure ⟨sorted.zip pairs, 0, 0⟩
  transitions _ := Gen.frequency [(3, Step.ask <$> Gen.nat (.constant 1 5)),
    (1, Gen.zipWith Step.changed (Gen.nat (.constant 1 5)) (Gen.nat (.constant 0 3)))]
  apply w
    | .ask count =>
      match (w.range count).getLast? with
      | some last => { w with next := last.1 + 1, received := w.received + (w.range count).length }
      | none => w
    | .changed .. => w

/-- The accounts of a trie in the text form of the oracle, each with its value in the trie. -/
def Walk.text (w : Walk) : String :=
  joined "," (w.entries.map fun (key, pair) => s!"{hexVec (word32 key)}={hex pair.full}")

/-- The walk on EthLib's check, with the oracle as the peer.

A range is cut by py-trie from where the model says the walk is, before the step.

The check must accept it, and say whether the trie holds more.

A changed range is one account less, or an account with another body or another key.

The check must refuse it. -/
def walkMachine (oracle : Oracle) : StateMachine Walk Step Oracle IO where
  toModel := walkModel
  initSut _ := pure oracle
  applySut oracle before after step := do
    let count := match step with
      | .ask count | .changed count _ => count
    let answer ← oracle.ask ["accounts", hexVec (word32 before.next), toString count, "-",
      before.text]
    let fields := answer.splitOn "|"
    if fields.length ≠ 4 then failWith s!"the oracle answered: {answer}"
    let root ← orFail ((vector? 32 fields[0]!).elim (.error "the root is not 32 bytes") .ok)
    let keys := if fields[1]! = "-" then [] else
      (fields[1]!.splitOn ",").filterMap fun entry => vector? 32 ((entry.splitOn "=").head!)
    let proof := if fields[2]! = "-" then [] else (fields[2]!.splitOn ",").filterMap unhex?
    -- What snap sends for each account is its slim form.
    let entries : List RangeEntry := keys.filterMap fun key =>
      (before.entries.find? fun e => word32 e.1 = key).map fun e => ⟨key, e.2.slim⟩
    let expected := before.range count
    entries.length === expected.length
    match step with
    | .ask _ =>
      match verifyAccountRange root (word32 before.next) entries proof with
      | .ok answer =>
        let more := fields[3]! = "1"
        reprStr answer === reprStr (if more then RangeAnswer.more else RangeAnswer.toEnd)
        classify "a range is accepted" true
        classify "a range of three accounts or more is accepted" (entries.length ≥ 3)
        classify "a range with no account is accepted" entries.isEmpty
        classify "the last range of a trie is accepted" (!more)
        classify "a second range is accepted" (before.received > 0)
        classify "the whole trie is walked"
          (!more ∧ after.received = before.entries.length ∧ before.received > 0)
      | .error e => failWith s!"EthLib refuses a true range: {reprStr e}"
    | .changed _ kind =>
      let other : RangeEntry → RangeEntry := fun e =>
        ⟨e.hash, (encode (.list [numberItem 77, numberItem 1, .bytes .empty, .bytes .empty])
          ).toOption.getD .empty⟩
      let changed : Option (List RangeEntry) := match kind, entries with
        | 0, _ :: rest => some rest
        | 1, a :: _ :: c :: rest => some (a :: c :: rest)
        | 2, a :: rest => some (other a :: rest)
        | 3, a :: rest => some (⟨word32 ((bytesToNat a.hash.toList) + 1), a.data⟩ :: rest)
        | _, _ => none
      match changed with
      | none => pure ()
      | some changed =>
        match verifyAccountRange root (word32 before.next) changed proof with
        | .ok answer =>
          -- No account and no proof is the reply of a peer without the state, and says nothing.
          if changed.isEmpty ∧ proof.isEmpty then reprStr answer === reprStr RangeAnswer.noState
          else failWith s!"EthLib accepts a changed range: {reprStr answer}"
        | .error _ => classify s!"a changed range is refused: kind {kind}" true
    pure oracle

/-- The value of an account in the state trie, from its slim form, is the one of the model.

A body that is not the slim form itself has none: another encoding, or a root written out. -/
def slimAccountValue (oracle : Oracle) : Property IO := propertyM do
  let pair ← forAllWith (fun p => hex p.slim) genSlimPair
  let body ← forAllWith hex (Gen.frequency [(3, pure pair.slim), (1, pure pair.full),
    (1, (fun item => (encode item).toOption.getD .empty) <$> genOffShape
      (.group [.scalar 0, .scalar 256, .bytes, .bytes])),
    (1, (fun item => (encode item).toOption.getD .empty) <$> genShape
      (.group [.scalar 0, .scalar 256, .fixed 32, .fixed 32])),
    (1, genBytes (.linear 0 6))])
  pure do
    let want ← oracle.ask ["slim", hex body]
    annotate s!"the reference: {want}"
    match fullAccount body with
    | some value =>
      hex value === want
      cover 30 "a slim account has a value" true
    | none =>
      want === "error"
      cover 5 "a body that is not slim has none" true

end RpcProperty

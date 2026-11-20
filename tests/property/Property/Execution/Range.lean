import Property.Execution.Trie

/-!
# Range proofs, against the trie that they are about

`verifyRange` checks that some entries are every key of a trie between a start and a last key.

The trie is known here, so what a range claims is true or false, and no second verifier is needed.

- A true claim with the nodes on the paths of its two ends is accepted.
  The answer says whether the trie holds a key after the last entry.
- An accepted claim is true, whatever was done to the entries, the start and the nodes.

py-trie gives the nodes on the path of a key, so the proofs do not come from EthLib.
-/

open Hedgehog Support EthLib EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace ExecutionProperty

/-- A key of a range: 32 bytes. -/
abbrev RangeKey := ByteArray

/-- The number that 32 bytes write, the first byte the most significant. -/
def keyNat (key : RangeKey) : Nat := key.data.foldl (fun n byte => n * 256 + byte.toNat) 0

/-- The 32 bytes of a number below `2 ^ 256`. -/
def natKey (n : Nat) : RangeKey :=
  bytesOf ((List.range 32).map fun i => UInt8.ofNat (n / 256 ^ (31 - i) % 256))

/-- The key as the 32 bytes that `verifyRange` takes. -/
def hashOf (key : RangeKey) : Hash32 := Vector.ofFn fun (i : Fin 32) => key.data.getD i.val 0

/-- How the keys of one trie are drawn. -/
inductive RangeStyle where
  /-- A first byte of five, 30 bytes that every key shares, and a last byte of five.

  The trie has a branch at the root, then extensions, branches and leaves below. -/
  | layered (stem : ByteArray)
  /-- Any 32 bytes: a branch at the root, and leaves below it. -/
  | spread
  /-- 31 bytes that every key shares, and any last byte: an extension at the root.

  A leaf then holds at most one nibble, and its branch holds it inside when its value is short.
  -/
  | clustered (stem : ByteArray)

/-- A style of keys. -/
def genRangeStyle : Gen RangeStyle :=
  Gen.frequency [(3, RangeStyle.layered <$> genBytesN 30), (1, pure .spread),
    (3, RangeStyle.clustered <$> genBytesN 31)]

/-- A key of a style. -/
def genRangeKey : RangeStyle → Gen RangeKey
  | .layered stem => (fun (first last : UInt8) => ⟨#[first]⟩ ++ stem ++ ⟨#[last]⟩) <$>
      Gen.element [0x00, 0x01, 0x10, 0x80, 0xff] <*> Gen.element [0x00, 0x01, 0x10, 0x11, 0xff]
  | .spread => genBytesN 32
  | .clustered stem => (fun (last : UInt8) => stem ++ ⟨#[last]⟩) <$>
      Gen.frequency [(3, Gen.element [0x00, 0x01, 0x02, 0x10, 0x11, 0x12, 0xf0, 0xff]),
        (1, genByte)]

/-- A value: short, so that its leaf may lie inside its parent, or longer than a hash. -/
def genRangeValue : Gen ByteArray :=
  Gen.frequency [(1, genBytes (.constant 1 2)), (1, genBytes (.constant 30 34))]

/-- The entries of a trie: distinct keys in increasing order, each with a value. -/
def sortedEntries (entries : List (RangeKey × ByteArray)) : List (RangeKey × ByteArray) :=
  let distinct := entries.foldl (fun (kept : List (RangeKey × ByteArray)) entry =>
    if kept.any (·.1.data == entry.1.data) then kept else kept ++ [entry]) []
  (distinct.toArray.qsort fun a b => keyNat a.1 < keyNat b.1).toList

/-- What is done to a true claim. -/
inductive ClaimChange where
  /-- Nothing: the claim is true. -/
  | none
  /-- An entry is left out. -/
  | drop (index : Nat)
  /-- A value is changed. -/
  | value (index : Nat)
  /-- An entry that the trie does not hold is added. -/
  | fake (key : RangeKey) (value : ByteArray)
  /-- Every entry is left out. -/
  | clear
  /-- The start is another key. -/
  | start (key : RangeKey)
  /-- Two entries change places. -/
  | swap (index : Nat)
  /-- An entry is written twice. -/
  | twice (index : Nat)
  /-- A value is the empty byte string. -/
  | emptyValue (index : Nat)

/-- A change of a claim as a report shows it. -/
def ClaimChange.text : ClaimChange → String
  | .none => "none"
  | .drop index => s!"drop {index}"
  | .value index => s!"value {index}"
  | .fake key bytes => s!"fake {hex key}={hex bytes}"
  | .clear => "clear"
  | .start key => s!"start {hex key}"
  | .swap index => s!"swap {index}"
  | .twice index => s!"twice {index}"
  | .emptyValue index => s!"emptyValue {index}"

/-- The kind of a change of a claim. -/
def ClaimChange.kind (change : ClaimChange) : String := (change.text.splitOn " ").headD ""

/-- What is done to the nodes of the two paths. -/
inductive NodeChange where
  /-- Nothing. -/
  | none
  /-- No node at all. -/
  | clear
  /-- A node is left out. -/
  | drop (index : Nat)
  /-- The nodes are in the other order. -/
  | reverse
  /-- A node is listed twice. -/
  | twice (index : Nat)
  /-- A byte string that is no node of the trie is added. -/
  | junk
  /-- Only the nodes on the path of the start. -/
  | startOnly
  /-- Only the nodes on the path of the last key. -/
  | lastOnly
  deriving Repr, BEq

/-- A range of a trie, and what is done to it. -/
structure RangeCase where
  /-- The entries of the trie, in increasing order of their keys. -/
  trie : List (RangeKey × ByteArray)
  /-- The start of the range. -/
  start : RangeKey
  /-- How many of the keys from the start on the true claim holds. -/
  count : Nat
  /-- What is done to the claim. -/
  claim : ClaimChange
  /-- What is done to the nodes. -/
  proof : NodeChange

instance : Repr RangeCase where
  reprPrec c _ := s!"trie {showWrites c.trie} start {hex c.start} count {c.count} \
    claim {c.claim.text} proof {reprStr c.proof}"

/-- A key beside the keys of a trie: one of them, one next to one of them, or an end. -/
def genStart (style : RangeStyle) (trie : List (RangeKey × ByteArray)) : Gen RangeKey :=
  let ends := Gen.element [natKey 0, natKey (2 ^ 256 - 1)]
  if trie.isEmpty then Gen.frequency [(1, ends), (1, genRangeKey style)]
  else
    let key := Gen.element (trie.map Prod.fst)
    Gen.frequency [(3, key), (2, (fun k => natKey (keyNat k + 1)) <$> key),
      (2, (fun k => natKey (keyNat k - 1)) <$> key), (2, ends), (1, genRangeKey style)]

/-- A range of a trie of a style, mostly a true one with the nodes of its two ends. -/
def genRangeCase : Gen RangeCase := do
  let style ← genRangeStyle
  let entries ← Gen.frequency [(1, pure []), (2, Gen.list (.constant 1 2)
      (Gen.zip (genRangeKey style) genRangeValue)),
    (8, Gen.list (.linear 2 20) (Gen.zip (genRangeKey style) genRangeValue))]
  let trie := sortedEntries entries
  let start ← genStart style trie
  let after := (trie.filter fun (key, _) => keyNat start ≤ keyNat key).length
  let count ← Gen.frequency [(2, pure after), (2, Gen.nat (.constant 1 (max 1 after))),
    (1, pure 1)]
  let index := Gen.nat (.constant 0 (max 1 count - 1))
  let claim ← Gen.frequency [(6, pure ClaimChange.none), (1, ClaimChange.drop <$> index),
    (1, ClaimChange.value <$> index),
    (1, ClaimChange.fake <$> genStart style trie <*> genRangeValue),
    (1, pure .clear), (1, ClaimChange.start <$> genStart style trie),
    (1, ClaimChange.swap <$> index), (1, ClaimChange.twice <$> index),
    (1, ClaimChange.emptyValue <$> index)]
  let proof ← Gen.frequency [(9, pure NodeChange.none), (1, pure .clear),
    (1, NodeChange.drop <$> Gen.nat (.constant 0 9)), (1, pure .reverse),
    (1, NodeChange.twice <$> Gen.nat (.constant 0 9)), (1, pure .junk),
    (2, Gen.element [.startOnly, .lastOnly])]
  -- One case in ten is the whole trie with no node, which the root alone decides.
  Gen.frequency [(9, pure ⟨trie, start, count, claim, proof⟩),
    (1, pure ⟨trie, natKey 0, trie.length, claim, .clear⟩)]

/-- The true claim of a case: the first `count` keys of the trie from the start on. -/
def RangeCase.honest (c : RangeCase) : List (RangeKey × ByteArray) :=
  (c.trie.filter fun (key, _) => keyNat c.start ≤ keyNat key).take c.count

/-- The start and the entries that a case claims. -/
def RangeCase.claimed (c : RangeCase) : RangeKey × List (RangeKey × ByteArray) :=
  let entries := c.honest
  let at_ (index : Nat) : Nat := index % max 1 entries.length
  match c.claim with
  | .none => (c.start, entries)
  | .drop index => (c.start, entries.eraseIdx (at_ index))
  | .value index => (c.start, entries.modify (at_ index) fun (key, value) =>
      (key, value ++ ⟨#[1]⟩))
  | .fake key bytes =>
    (c.start, sortedEntries (entries ++ [(key, bytes)]))
  | .clear => (c.start, [])
  | .start key => (key, entries)
  | .swap index =>
    let i := at_ index
    match entries[i]?, entries[i + 1]? with
    | some a, some b => (c.start, (entries.set i b).set (i + 1) a)
    | _, _ => (c.start, entries.reverse)
  | .twice index =>
    let i := at_ index
    (c.start, entries.take (i + 1) ++ entries.drop i)
  | .emptyValue index => (c.start, entries.modify (at_ index) fun (key, _) => (key, .empty))

/-- What a claim is worth against the trie: whether a key follows it, or none for a false claim.

A claim is true when it holds every key of the trie from its start to its last key, and no other.

With no entry, it is true when the trie holds no key from the start on. -/
def claimTruth (trie : List (RangeKey × ByteArray)) (start : RangeKey)
    (entries : List (RangeKey × ByteArray)) : Option Bool :=
  let keys := entries.map fun (key, _) => keyNat key
  let last := keys.getLast?
  let within := trie.filter fun (key, _) =>
    keyNat start ≤ keyNat key && last.all (keyNat key ≤ ·)
  let same := entries.length = within.length &&
    (entries.zip within).all fun (a, b) => a.1.data == b.1.data && a.2.data == b.2.data
  if same then some (last.any fun l => trie.any fun (key, _) => l < keyNat key) else none

/-- The nodes of an answer of the oracle to `trieproof`, without its root. -/
def nodesOf (answer : String) : List ByteArray :=
  ((answer.splitOn " ").drop 1).filterMap unhex?

/-- A range of a trie is accepted when it is true, and only then.

The trie holds keys of 32 bytes: spread, layered, or clustered under one extension.

The start is a key, a key beside one, or an end of the key space.

A true claim holds the first keys from the start on, with the nodes of py-trie for its two ends.

- EthLib accepts it, and says whether a key follows the last entry.
- With no node, EthLib accepts the claim that is the whole trie, and no other.

The claim is then changed: an entry left out, changed or added, another start, no entry.

The nodes are changed too: one left out or twice, another order, a stranger, one path only.

Whatever was done, a claim that EthLib accepts is true, and its answer is the truth. -/
def rangeProof (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genRangeCase
  pure do
    let trie : Trie := ⟨false, c.trie⟩
    let .ok rootHash := root keccak256 trie | failWith "no root"
    let (start, entries) := c.claimed
    let words := c.trie.map pairWord
    let startAnswer ← oracle.ask (["trieproof", hex start] ++ words)
    (startAnswer.splitOn " ").headD "" === hexV rootHash
    let lastNodes ← match entries.getLast? with
      | some (key, _) => nodesOf <$> oracle.ask (["trieproof", hex key] ++ words)
      | none => pure []
    let full := nodesOf startAnswer ++ lastNodes
    let at_ (index : Nat) : Nat := index % max 1 full.length
    let nodes := match c.proof with
      | .none => full
      | .clear => []
      | .drop index => full.eraseIdx (at_ index)
      | .reverse => full.reverse
      | .twice index => full ++ (full.drop (at_ index)).take 1
      | .junk => ⟨#[0xc2, 0x20, 0x07]⟩ :: full
      | .startOnly => nodesOf startAnswer
      | .lastOnly => lastNodes
    annotate s!"claim: start {hex start} entries {showWrites entries}"
    annotate s!"nodes: {" ".intercalate (nodes.map hex)}"
    let truth := claimTruth c.trie start entries
    let wellFormed := (entries.zip entries.tail).all (fun (a, b) => keyNat a.1 < keyNat b.1) &&
      entries.all fun (key, value) => keyNat start ≤ keyNat key && !value.isEmpty
    let truth := if wellFormed then truth else none
    let result := verifyRange keccak256 rootHash (hashOf start)
      (entries.map fun (key, value) => (hashOf key, value)) nodes
    annotate s!"EthLib: {repr result}"
    annotate s!"the truth: {repr truth}"
    -- Every node on the two paths is there: the proof is whole.
    let whole := full.all fun node => nodes.any (·.data == node.data)
    let count := c.trie.length
    label (if count = 0 then "trie: 0 keys" else if count = 1 then "trie: 1 key"
      else if count ≤ 4 then "trie: 2 to 4 keys" else "trie: 5 keys or more")
    label (if entries.isEmpty then "claim: no entry" else if entries.length = 1 then
      "claim: 1 entry" else "claim: 2 entries or more")
    coverMin 2 "claim: the whole trie, with nodes" (truth.isSome && !nodes.isEmpty && count ≥ 1 &&
      entries.length = count)
    coverMin 1 "claim: the whole trie, with no node" (truth.isSome && nodes.isEmpty && count ≥ 1 &&
      entries.length = count)
    coverMin 13 "claim: true, and a part of the trie" (truth.isSome && entries.length < count)
    coverMin 4 "claim: true, with no entry in a trie with keys" (truth.isSome && entries.isEmpty &&
      count ≥ 1)
    coverMin 9 "start: a key of the trie" (c.trie.any (·.1.data == start.data))
    coverMin 7 "start: below every key" (count ≥ 1 && c.trie.all (keyNat start < keyNat ·.1))
    coverMin 5 "start: above every key" (count ≥ 1 && c.trie.all (keyNat ·.1 < keyNat start))
    coverMin 6 "start: between two keys" (c.trie.any (keyNat ·.1 < keyNat start) &&
      c.trie.any (keyNat start < keyNat ·.1) && !c.trie.any (·.1.data == start.data))
    let census := censusOf trie
    coverMin 8 "trie: an extension" (0 < census.extensions)
    coverMin 11 "trie: a node held inside its parent" (0 < census.inside)
    coverMin 12 "trie: a root that is an extension"
      (match nodeAt (pathsOf trie) 0 with
        | some (.extension _ _) => true
        | _ => false)
    label s!"claim change: {c.claim.kind}"
    label s!"node change: {(((reprStr c.proof).splitOn " ").headD "").splitOn "." |>.getLastD ""}"
    match result with
    | .ok more =>
      label (if more then "EthLib: accepts, a key follows" else "EthLib: accepts, no key follows")
      coverMin 5 "accepted, after a change of the claim" (!(c.claim matches .none))
      coverMin 7 "accepted, after a change of the nodes" (c.proof != .none)
      coverMin 2 "accepted, with a node missing" (!whole)
      truth === some more
    | .error error =>
      label (match error with
        | .proof inner => s!"EthLib: refuses, proof, {errorName inner}"
        | _ => s!"EthLib: refuses, {errorName error}")
      coverMin 12 "refused, a false claim" (truth.isNone)
      coverMin 2 "refused, a true claim with a node missing" (truth.isSome && !whole)
      -- A true claim with every node of its two paths is accepted.
      --
      -- With no node at all, it is accepted when it is the whole trie.
      if truth.isSome ∧ ((whole ∧ !nodes.isEmpty) ∨ (nodes.isEmpty ∧ entries.length = count)) then
        failWith "a true claim with the nodes of its two ends is refused"

end ExecutionProperty

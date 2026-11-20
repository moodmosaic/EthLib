import Property.Rpc.World
import EthLib.Execution.Network

/-!
# The eth and snap messages

A message is generated as an RLP tree of the shape that `caps/eth.md` or `caps/snap.md` gives it.

One case in three then changes the tree at one place: a list for a scalar, a field more or less.

The reference is `oracle/rpc_wire.py`, a reader written from devp2p with the `rlp` package.

Both sides write the message that they read as the same text, and the texts must agree.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Network
open EthLib.Serialization.Rlp

namespace RpcProperty

/-! ## Shapes -/

/-- The shape of a part of a message, as devp2p writes it. -/
inductive Shape where
  /-- `P`: a scalar, below `2 ^ bits` when the bound is not 0. -/
  | scalar (bits : Nat)
  /-- `B_n`: a string of `n` bytes. -/
  | fixed (n : Nat)
  /-- `B`: a string of any length. -/
  | bytes
  /-- An item that the message carries whole, such as a header. -/
  | item
  /-- `{0, 1}`. -/
  | flag
  /-- A list of parts of one shape. -/
  | list (s : Shape)
  /-- A group of parts, each of its own shape. -/
  | group (ss : List Shape)
  /-- `{P, B_32}`: the first block of a request of headers. -/
  | start
  /-- The bitmap of an announcement: 16 bytes or none. -/
  | cells

/-- A number as its digits in base 256, which `Nat.toDigits` does not give above base 36. -/
def natBytes (n : Nat) : List UInt8 :=
  let rec go (fuel n : Nat) (acc : List UInt8) : List UInt8 :=
    match fuel with
    | 0 => acc
    | fuel + 1 => if n = 0 then acc else go fuel (n / 256) (UInt8.ofNat (n % 256) :: acc)
  go 40 n []

/-- The item of a scalar. -/
def numberItem (n : Nat) : Item := .bytes ⟨(natBytes n).toArray⟩

/-- A small tree of any shape, for a part that the message carries whole. -/
def genAnyItem : Nat → Gen Item
  | 0 => Item.bytes <$> genBytes (.linear 0 6)
  | depth + 1 => Gen.frequency [(2, Item.bytes <$> genBytes (.linear 0 6)),
      (1, Item.list <$> Gen.list (.linear 0 3) (genAnyItem depth))]

/-- A tree of a shape. -/
partial def genShape : Shape → Gen Item
  | .scalar bits =>
    let top := if bits = 0 then 2 ^ 80 else 2 ^ bits - 1
    numberItem <$> Gen.frequency [(3, Gen.nat (.linear 0 300)),
      (1, Gen.element [0, 1, 127, 128, top]),
      (1, Gen.nat (.exponential 0 top))]
  | .fixed n => Item.bytes <$> genBytesN n
  | .bytes => Item.bytes <$> genBytes (.linear 0 8)
  | .item => genAnyItem 2
  | .flag => Gen.element [numberItem 0, numberItem 1]
  | .list s => Item.list <$> Gen.list (.linear 0 4) (genShape s)
  | .group ss => Item.list <$> (ss.mapM genShape)
  | .start => Gen.frequency [(1, Item.bytes <$> genBytesN 32),
      (1, numberItem <$> Gen.element [0, 1, 1000, 2 ^ 64 - 1])]
  | .cells => Gen.frequency [(1, pure (.bytes .empty)), (1, Item.bytes <$> genBytesN 16)]

/-- A tree that is of a shape but for one place, where it holds what the shape forbids.

A scalar is above its bound, has a leading zero, or is a list; a string has a byte more or less.

A flag is 2; a list is a string; a group has a field more or less. -/
partial def genOffShape : Shape → Gen Item
  | .scalar bits => Gen.element ([.list [], .bytes (bytesOf [0]), .bytes (bytesOf [0, 5]),
      .list [numberItem 1]] ++ if bits = 0 then [] else
        [numberItem (2 ^ bits), numberItem (2 ^ bits), numberItem (2 ^ bits + 1)])
  | .fixed n => Gen.frequency [(2, Item.bytes <$> genBytesN (n + 1)),
      (2, Item.bytes <$> genBytesN (n - 1)), (1, pure (.list [])), (1, pure (.bytes .empty))]
  | .bytes => Gen.element [.list [], .list [.bytes .empty]]
  | .item => genAnyItem 2
  | .flag => Gen.element [numberItem 2, .bytes (bytesOf [0]), .list [], numberItem 256]
  | .list s => Gen.frequency [(1, pure (.bytes .empty)), (1, pure (.bytes (bytesOf [1]))),
      (4, do
        let before ← Gen.list (.linear 0 2) (genShape s)
        let odd ← genOffShape s
        let after ← Gen.list (.linear 0 2) (genShape s)
        pure (.list (before ++ [odd] ++ after)))]
  | .group ss => do
    let fields ← ss.mapM genShape
    let index ← Gen.nat (.constant 0 (ss.length - 1))
    let odd ← genOffShape (ss.getD index .bytes)
    Gen.frequency [(1, pure (.list (fields.drop 1))), (1, pure (.list fields.dropLast)),
      (1, pure (.list (fields ++ [.bytes .empty]))), (1, pure (.bytes .empty)),
      (8, pure (.list (fields.set index odd)))]
  | .start => Gen.frequency [(1, Item.bytes <$> genBytesN 33), (1, Item.bytes <$> genBytesN 31),
      (2, pure (numberItem (2 ^ 64))), (1, pure (.list [])), (1, pure (.bytes (bytesOf [0, 1])))]
  | .cells => Gen.frequency [(1, Item.bytes <$> genBytesN 15), (1, Item.bytes <$> genBytesN 17),
      (1, pure (.list []))]

/-- A scalar, a request ID and a hash. -/
def P : Shape := .scalar 0

/-- A request ID: a scalar below `2 ^ 64`. -/
def requestIdShape : Shape := .scalar 64

/-- A hash of 32 bytes. -/
def hashShape : Shape := .fixed 32

/-- The shape of the message of eth with an ID on a version, or none when it has none. -/
def ethShape (version id : Nat) : Option Shape :=
  let forkId := Shape.group [.fixed 4, .scalar 64]
  let i := requestIdShape
  let h := hashShape
  match id with
  | 0x00 => some (if version = 68 then .group [P, P, P, h, h, forkId]
      else .group [P, P, h, forkId, P, P, h])
  | 0x01 => some (.list (.group [h, P]))
  | 0x02 => some (.list .item)
  | 0x03 => some (.group [i, .group [.start, P, P, .flag]])
  | 0x04 | 0x06 | 0x0a => some (.group [i, .list .item])
  | 0x05 | 0x09 => some (.group [i, .list h])
  | 0x07 => some (.group [.item, P])
  | 0x08 => some (.group ([.bytes, .list P, .list h] ++ if version ≥ 72 then [.cells] else []))
  | 0x0f => some (if version < 70 then .group [i, .list h] else .group [i, P, .list h])
  | 0x10 => some (if version < 70 then .group [i, .list (.list .item)]
      else .group [i, .flag, .list (.list .item)])
  | 0x11 => if version ≥ 69 then some (.group [P, P, h]) else none
  | 0x12 => if version ≥ 71 then some (.group [i, .list h]) else none
  | 0x13 => if version ≥ 71 then some (.group [i, .list .item]) else none
  | 0x14 => if version ≥ 72 then some (.group [i, .list h, .fixed 16]) else none
  | 0x15 =>
    if version ≥ 72 then some (.group [i, .list h, .list (.list .bytes), .fixed 16]) else none
  | _ => none

/-- The shape of the message of snap with an ID on a version, or none when it has none. -/
def snapShape (version id : Nat) : Option Shape :=
  let i := requestIdShape
  let h := hashShape
  let entry := Shape.group [h, .bytes]
  match id with
  | 0x00 => some (.group [i, h, h, h, P])
  | 0x01 => some (.group [i, .list entry, .list .bytes])
  | 0x02 => some (.group [i, h, .list h, .bytes, .bytes, P])
  | 0x03 => some (.group [i, .list (.list entry), .list .bytes])
  | 0x04 => some (.group [i, .list h, P])
  | 0x05 => some (.group [i, .list .bytes])
  | 0x06 => if version = 1 then some (.group [i, h, .list (.list .bytes), P]) else none
  | 0x07 => if version = 1 then some (.group [i, .list .bytes]) else none
  | 0x08 => if version = 2 then some (.group [i, .list h, P]) else none
  | 0x09 => if version = 2 then some (.group [i, .list .item]) else none
  | _ => none

/-- An announcement of transactions: as many types and sizes as hashes, or one more or less. -/
def genAnnouncement (version : Nat) : Gen Item := do
  let count ← Gen.nat (.linear 0 4)
  let off ← Gen.frequency [(6, pure (0, 0)), (1, Gen.element [(1, 0), (0, 1)])]
  let types ← genBytes (.singleton (count + off.1))
  let sizes ← Gen.list (.singleton (count + off.2)) (genShape P)
  let hashes ← Gen.list (.singleton count) (genShape hashShape)
  let cells ← genShape .cells
  pure (.list ([.bytes types, .list sizes, .list hashes] ++ if version ≥ 72 then [cells] else []))

/-- The same tree with one place changed: another kind of item, or a field more or less. -/
partial def mutate (item : Item) : Gen Item := do
  let here : Gen Item := match item with
    | .bytes b => Gen.element [.list [], .list [.bytes b], .bytes (bytesOf [0] ++ b),
        .bytes (b ++ bytesOf [0]), .bytes (b.extract 0 (b.size - 1)), .bytes (bytesOf [2]),
        .bytes (bytesOf [0]), .bytes (bytesOf [1, 0, 0, 0, 0, 0, 0, 0, 0]), .bytes .empty]
    | .list l => Gen.element [.bytes .empty, .list (l.drop 1), .list (l ++ [.bytes (bytesOf [1])]),
        .list (l ++ l.take 1), .list l.reverse, .bytes (bytesOf [0xc0]), .list l.dropLast]
  match item with
  | .list (first :: rest) =>
    let children := first :: rest
    let index ← Gen.nat (.constant 0 (children.length - 1))
    Gen.frequency [(1, here),
      (2, do
        let child ← mutate (children.getD index first)
        pure (.list (children.set index child)))]
  | _ => here

/-! ## The text of a message -/

/-- A string as `x` and its hexadecimal. -/
def showBytes (b : ByteArray) : String := "x" ++ (if b.isEmpty then "" else hex b)

/-- A fixed string as `x` and its hexadecimal. -/
def showVec {n : Nat} (v : Vector UInt8 n) : String := showBytes ⟨v.toArray⟩

/-- An item that a message carries whole, as `i` and the hexadecimal of its encoding. -/
def showItem (item : Item) : String :=
  match encode item with
  | .ok bytes => "i" ++ (if bytes.isEmpty then "" else hex bytes)
  | .error _ => "i?"

/-- A list in brackets. -/
def showList {α : Type} (f : α → String) (l : List α) : String :=
  "[" ++ ",".intercalate (l.map f) ++ "]"

/-- A group of fields in parentheses. -/
def showGroup (fields : List String) : String := "(" ++ ",".intercalate fields ++ ")"

/-- A flag as `1` or `0`. -/
def showFlag (b : Bool) : String := if b then "1" else "0"

/-- A message of eth as the text of the oracle. -/
def showEth : Message → String
  | .status (.eth68 v n td h g id) =>
    showGroup [toString v, toString n, toString td, showVec h, showVec g,
      showGroup [showVec id.hash, toString id.next.toNat]]
  | .status (.eth69 v n g id r) =>
    showGroup [toString v, toString n, showVec g,
      showGroup [showVec id.hash, toString id.next.toNat], toString r.earliest, toString r.latest,
      showVec r.latestHash]
  | .newBlockHashes blocks =>
    showList (fun (a : BlockAnnouncement) => showGroup [showVec a.hash, toString a.number]) blocks
  | .transactions txs => showList showItem txs
  | .getBlockHeaders i r =>
    let start := match r.start with
      | .number n => toString n.toNat
      | .hash h => showVec h
    showGroup [toString i.toNat,
      showGroup [start, toString r.limit, toString r.skip, showFlag r.reverse]]
  | .blockHeaders i hs => showGroup [toString i.toNat, showList showItem hs]
  | .getBlockBodies i hs => showGroup [toString i.toNat, showList showVec hs]
  | .blockBodies i bs => showGroup [toString i.toNat, showList showItem bs]
  | .newBlock b td => showGroup [showItem b, toString td]
  | .newPooledTransactionHashes (.eth68 t s h) =>
    showGroup [showBytes t, showList toString s, showList showVec h]
  | .newPooledTransactionHashes (.eth72 t s h c) =>
    showGroup [showBytes t, showList toString s, showList showVec h,
      match c with
      | some mask => showVec mask
      | none => "_"]
  | .getPooledTransactions i hs => showGroup [toString i.toNat, showList showVec hs]
  | .pooledTransactions i txs => showGroup [toString i.toNat, showList showItem txs]
  | .getReceipts i k hs =>
    showGroup ([toString i.toNat] ++ (k.map toString).toList ++ [showList showVec hs])
  | .receipts i b ls =>
    showGroup ([toString i.toNat] ++ (b.map showFlag).toList ++ [showList (showList showItem) ls])
  | .blockRangeUpdate r =>
    showGroup [toString r.earliest, toString r.latest, showVec r.latestHash]
  | .getBlockAccessLists i hs => showGroup [toString i.toNat, showList showVec hs]
  | .blockAccessLists i ls => showGroup [toString i.toNat, showList showItem ls]
  | .getCells i hs m => showGroup [toString i.toNat, showList showVec hs, showVec m]
  | .cells i hs gs m =>
    showGroup [toString i.toNat, showList showVec hs, showList (showList showBytes) gs, showVec m]

/-- An entry of a range as the text of the oracle. -/
def showEntry (e : RangeEntry) : String := showGroup [showVec e.hash, showBytes e.data]

/-- A message of snap as the text of the oracle. -/
def showSnap : SnapMessage → String
  | .getAccountRange i r s l b =>
    showGroup [toString i.toNat, showVec r, showVec s, showVec l, toString b]
  | .accountRange i accounts proof =>
    showGroup [toString i.toNat, showList showEntry accounts, showList showBytes proof]
  | .getStorageRanges i r accounts s l b =>
    showGroup [toString i.toNat, showVec r, showList showVec accounts, showBytes s, showBytes l,
      toString b]
  | .storageRanges i slots proof =>
    showGroup [toString i.toNat, showList (showList showEntry) slots, showList showBytes proof]
  | .getByteCodes i hs b => showGroup [toString i.toNat, showList showVec hs, toString b]
  | .byteCodes i codes => showGroup [toString i.toNat, showList showBytes codes]
  | .getTrieNodes i r paths b =>
    showGroup [toString i.toNat, showVec r, showList (showList showBytes) paths, toString b]
  | .trieNodes i nodes => showGroup [toString i.toNat, showList showBytes nodes]
  | .getBlockAccessLists i hs b => showGroup [toString i.toNat, showList showVec hs, toString b]
  | .blockAccessLists i lists => showGroup [toString i.toNat, showList showItem lists]

/-! ## The properties -/

/-- The versions of eth, by their numbers. -/
def ethVersions : List (Nat × EthVersion) :=
  [(68, .eth68), (69, .eth69), (70, .eth70), (71, .eth71), (72, .eth72)]

/-- A tree for a message: of its shape, of its shape with one place changed, or any tree. -/
def genMessageItem (shape : Option Shape) (special : Option (Gen Item)) : Gen (Item × Bool) := do
  let valid ← match special, shape with
    | some gen, _ => gen
    | none, some s => genShape s
    | none, none => genAnyItem 3
  let off ← match shape with
    | some s => genOffShape s
    | none => genAnyItem 3
  Gen.frequency [(4, pure (valid, false)), (1, (·, true) <$> mutate valid), (2, pure (off, true))]

/-- Count a decode under what it did: read as generated, read though changed, or refused. -/
def classifyDecode (accepted changed : Bool) : TestT IO Unit := do
  cover 30 "valid: read as generated" (accepted ∧ !changed)
  cover 3 "changed and still valid" (accepted ∧ changed)
  cover 10 "refused" (!accepted)

/-- A message of eth reads as `caps/eth.md` says, at every version and every message ID.

What EthLib reads is what the reference reads, field by field, and it writes back the same bytes.

Bytes that are not the message of that ID on that version are refused. -/
def ethDecode (oracle : Oracle) : Property IO := propertyM do
  let (number, version) ← forAll (Gen.element ethVersions)
  -- Nine IDs in ten have a message on the version.
  let used := (List.range 0x16).filter fun id => (ethShape number id).isSome
  -- The others are mostly an ID that only a later version has.
  let later := (List.range 0x16).filter fun id => (ethShape number id).isNone ∧ id ≥ 0x11
  let id ← forAll (Gen.frequency [(18, Gen.element used), (1, Gen.nat (.constant 0 0x18)),
    (1, Gen.element (later ++ [0x0b]))])
  let special := if id = 0x08 then some (genAnnouncement number) else none
  -- An ID with no message on the version carries the message of a version that has it.
  let shape := (ethShape number id).orElse fun _ => ethShape 72 id
  let (item, changed) ← forAllWith (fun (item, changed) => s!"{showItem item} changed={changed}")
    (genMessageItem shape special)
  pure do
    let data ← orFail ((encode item).mapError reprStr)
    let want ← oracle.ask ["eth", toString number, toString id, hex data]
    annotate s!"the reference: {want}"
    if want.startsWith "crash" then failWith "the reference failed"
    match Message.decode version id data with
    | .ok message =>
      annotate s!"EthLib: {showEth message}"
      showEth message === want
      message.id === id
      (message.encode.toOption.map hex) === some (hex data)
      classifyDecode true changed
      classify s!"read: message {id}" true
    | .error e =>
      annotate s!"EthLib: {reprStr e}"
      ensure (want.startsWith "error") "EthLib refuses a message that the reference reads"
      -- An ID with no message on the version is refused as such.
      if want = "error id" then
        ensure (e matches .unknownId _) "an ID with no message is not refused as an unknown ID"
      classifyDecode false changed
      classify "refused: no message has the ID on the version" (want = "error id")

/-- A message of snap reads as `caps/snap.md` says, at both versions and every message ID. -/
def snapDecode (oracle : Oracle) : Property IO := propertyM do
  let (number, version) ← forAll (Gen.element [(1, SnapVersion.snap1), (2, SnapVersion.snap2)])
  let used := (List.range 0x0a).filter fun id => (snapShape number id).isSome
  let id ← forAll (Gen.frequency [(9, Gen.element used), (1, Gen.nat (.constant 0 0x0b))])
  let (item, changed) ← forAllWith (fun (item, changed) => s!"{showItem item} changed={changed}")
    (genMessageItem (snapShape number id) none)
  pure do
    let data ← orFail ((encode item).mapError reprStr)
    let want ← oracle.ask ["snap", toString number, toString id, hex data]
    annotate s!"the reference: {want}"
    if want.startsWith "crash" then failWith "the reference failed"
    match SnapMessage.decode version id data with
    | .ok message =>
      annotate s!"EthLib: {showSnap message}"
      showSnap message === want
      message.id === id
      (message.encode.toOption.map hex) === some (hex data)
      classifyDecode true changed
      classify s!"read: message {id}" true
    | .error e =>
      annotate s!"EthLib: {reprStr e}"
      ensure (want.startsWith "error") "EthLib refuses a message that the reference reads"
      if want = "error id" then
        ensure (e matches .unknownId _) "an ID with no message is not refused as an unknown ID"
      classifyDecode false changed
      classify "refused: no message has the ID on the version" (want = "error id")

/-! ## Headers that answer a request -/

/-- A header of a test chain: 15 fields, with its parent first and its number ninth. -/
def fakeHeader (parent : Hash32) (number salt : Nat) : Item :=
  .list ([.bytes ⟨parent.toArray⟩] ++ (List.replicate 7 (numberItem salt)) ++ [numberItem number] ++
    List.replicate 6 (numberItem 0))

/-- A chain of headers from a number on, each the child of the one before. -/
def fakeChain (first count salt : Nat) : List Item :=
  let rec go (number left : Nat) (parent : Hash32) (acc : List Item) : List Item :=
    match left with
    | 0 => acc.reverse
    | left + 1 =>
      let header := fakeHeader parent number salt
      go (number + 1) left ((headerHash header).toOption.getD parent) (header :: acc)
  go first count (Vector.replicate 32 0x77) []

/-- The headers that a peer with a chain answers a request with, as the request describes them. -/
def serve (chain : List Item) (first : Nat) (r : HeaderRequest) : List Item :=
  let start : Option Nat := match r.start with
    | .number n => if first ≤ n.toNat ∧ n.toNat < first + chain.length then some n.toNat else none
    | .hash h => (chain.findIdx? fun header => (headerHash header).toOption = some h).map
        (first + ·)
  match start with
  | none => []
  | some start =>
    (List.range r.limit).filterMap fun i =>
      let number : Option Nat :=
        let step := i * (r.skip + 1)
        if r.reverse then (if step ≤ start then some (start - step) else none)
        else some (start + step)
      number.bind fun n => if first ≤ n then chain[n - first]? else none

/-- Some headers answer a request exactly when they are the headers that the request describes.

The reference reads "GetBlockHeaders (0x03)": at most `limit`, from the start block, `skip` apart.

A peer may answer fewer headers, and none.

The true answer of a peer with a chain is changed at one place in half of the cases. -/
def headersAnswer (oracle : Oracle) : Property IO := propertyM do
  let first ← forAll (Gen.element [0, 1, 5, 1000])
  let chain := fakeChain first 12 1
  let other := fakeChain first 12 2
  let byHash ← forAll Gen.bool
  let at_ ← forAll (Gen.nat (.constant 0 13))
  let limit ← forAll (Gen.nat (.constant 0 8))
  let skip ← forAll (Gen.frequency [(3, pure 0), (2, Gen.nat (.constant 1 3))])
  let reverse ← forAll Gen.bool
  let start : BlockId := if byHash then
      .hash (((chain[at_]?).bind fun h => (headerHash h).toOption).getD (Vector.replicate 32 0x99))
    else .number (first + at_).toUInt64
  let request : HeaderRequest := ⟨start, limit, skip, reverse⟩
  let answer := serve chain first request
  let change ← forAll (Gen.frequency [(4, pure 0), (2, Gen.nat (.constant 1 8)), (2, pure 6)])
  let place ← forAll (Gen.nat (.constant 0 7))
  let changed : List Item := match change with
    | 0 => answer
    | 1 => answer.drop 1
    | 2 => answer.take place
    | 3 => answer ++ (chain.getLast?).toList
    | 4 => answer.reverse
    | 5 => answer.eraseIdx place
    -- The header of the same number on another chain, which does not chain with its neighbours.
    | 6 => answer.set place (((answer[place]?).bind fun header =>
        (headerNumber header).toOption.bind fun n => other[n - first]?).getD (.list []))
    | 7 => (answer.take 1) ++ answer
    | _ => (serve other first { request with start := .number (first + at_).toUInt64 })
  pure do
    let texts ← orFail ((changed.mapM fun h => hex <$> encode h).mapError reprStr)
    let startText := match start with
      | .number n => toString n.toNat
      | .hash h => hexVec h
    let want ← oracle.ask ["headers",
      s!"{startText},{limit},{skip},{if reverse then 1 else 0}", joined "," texts]
    annotate s!"the reference: {want}"
    let got := checkHeaders request changed
    annotate s!"EthLib: {reprStr got}"
    (if got.isOk then "ok" else "no") === want
    cover 30 "the headers answer the request" got.isOk
    cover 5 "the headers do not answer the request" (!got.isOk)
    classify "an answer of three headers or more is accepted" (got.isOk ∧ changed.length ≥ 3)
    classify "an empty answer" changed.isEmpty
    classify "a request by hash" byHash
    classify "a falling request" reverse
    classify "a request with a skip" (skip > 0)

/-- Some transactions answer a request of hashes exactly when they are a part of it, in order.

The hash of a transaction on the wire is that of its list, or of its typed bytes.

A blob transaction in its network form hashes without its blobs. -/
def pooledAnswer (oracle : Oracle) : Property IO := propertyM do
  let genTx : Gen Item := Gen.frequency [
    (2, Item.list <$> Gen.list (.constant 1 4) (Item.bytes <$> genBytes (.linear 0 5))),
    (2, (fun b => Item.bytes (bytesOf [2] ++ b)) <$> genBytes (.linear 1 8)),
    -- A blob transaction as a block holds it: its payload starts with the chain, a scalar.
    (1, (fun b => Item.bytes (bytesOf [3] ++ (encode (.list [.bytes b, .bytes b])).toOption.getD b))
      <$> genBytes (.linear 0 4)),
    -- A blob transaction in its network form: its payload starts with the body, a list.
    (2, (fun b => Item.bytes (bytesOf [3] ++
      (encode (.list [.list [.bytes b], .list [.bytes b], .list []])).toOption.getD b))
      <$> genBytes (.linear 0 4)),
    (1, (fun b => Item.bytes (bytesOf [3] ++ b)) <$> genBytes (.linear 0 4)),
    (1, pure (.bytes .empty))]
  let pool ← forAllWith (fun l => showList showItem l) (Gen.list (.linear 1 6) genTx)
  let sent ← forAllWith (fun l => showList showItem l) (Gen.frequency [
    (3, Gen.subsequence pool), (1, Gen.shuffle pool),
    (1, (fun extra => pool ++ [extra]) <$> genTx)])
  pure do
    let hashes ← orFail ((pool.mapM wireHash).mapError reprStr)
    let texts ← orFail ((sent.mapM fun t => hex <$> encode t).mapError reprStr)
    let want ← oracle.ask ["pooled", joined "," (hashes.map hexVec), joined "," texts]
    annotate s!"the reference: {want}"
    let got := checkPooled hashes sent
    annotate s!"EthLib: {reprStr got}"
    (if got.isOk then "ok" else "no") === want
    cover 30 "the transactions answer the request" got.isOk
    cover 5 "the transactions do not answer the request" (!got.isOk)
    classify "two transactions or more are accepted" (got.isOk ∧ sent.length ≥ 2)

end RpcProperty

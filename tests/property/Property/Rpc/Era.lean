import Property.Rpc.Wire
import EthLib.Execution.History

/-!
# Era1 files

A file is written by `oracle/rpc_era.py` from the era1 document, with cramjam and eth-remerkleable.

EthLib must read it back: the first number, each block and the accumulator root.

A file with one fault is not an era1 file, and must be refused.

A fault is in the bytes, as a record out of order, or in the chain, as a header with another parent.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.History
open EthLib.Execution.Network (headerHash)
open EthLib.Serialization.Rlp

namespace RpcProperty

/-- A block of a file: its header, its body and its receipts as RLP, and its total difficulty. -/
structure EraBlock where
  header : Item
  body : Item
  receipts : Item
  total : Nat

/-- A header of a test chain: 15 fields, its parent first, its difficulty eighth, its number ninth.
-/
def eraHeader (parent : Hash32) (difficulty number : Nat) : Item :=
  .list ([.bytes ⟨parent.toArray⟩] ++ List.replicate 6 (numberItem 7) ++
    [numberItem difficulty, numberItem number] ++ List.replicate 6 (numberItem 0))

/-- A chain of blocks from a number on, with a fault at one block if one is asked.

Each header names the one before as its parent, and each total difficulty adds a difficulty. -/
def eraChain (start before : Nat) (parts : List (Nat × Item × Item)) (fault : String)
    (place : Nat) : List EraBlock :=
  let rec go (i total : Nat) (parent : Hash32) : List (Nat × Item × Item) → List EraBlock
    | [] => []
    | (difficulty, body, receipts) :: rest =>
      let here := fault ≠ "" ∧ i = place
      let number := start + i + (if here ∧ fault = "number" then 1 else 0)
      let named := if here ∧ fault = "parent" then Vector.replicate 32 0x66 else parent
      let header := eraHeader named difficulty number
      let total := total + difficulty
      let written := total + (if here ∧ fault = "total" then 1 else 0)
      ⟨header, body, receipts, written⟩ ::
        go (i + 1) total ((headerHash header).toOption.getD parent) rest
  go 0 (if start = 0 then 0 else before) (Vector.replicate 32 0x77) parts

/-- The blocks in the text form of the oracle. -/
def showEraBlocks (blocks : List EraBlock) : Except String String := do
  let texts ← blocks.mapM fun b => do
    let part (item : Item) : Except String String := (hex <$> encode item).mapError reprStr
    pure s!"{← part b.header}.{← part b.body}.{← part b.receipts}.{b.total}"
  pure (joined "," texts)

/-- The faults of the bytes of a file, each with the fewest blocks at which it changes the file. -/
def fileFaults : List (String × Nat) := [("truncate", 0), ("noversion", 0), ("version", 0),
  ("accumulator", 0), ("count", 0), ("noindex", 0), ("swap", 1), ("offset", 1), ("size", 1),
  ("frame", 1), ("reserved", 1), ("between", 2)]

/-- An era1 file reads back, and a file with one fault is refused.

The writer follows the era1 document: the records in order, Snappy frames, the SSZ root, the index.

A record of another type before the accumulator is allowed, and the file still reads.

A second Version record is refused, as EthLib reads the grammar.

The chain rules are EthLib's own: numbers in a row, parents, and total difficulties that add up. -/
def era1File (oracle : Oracle) : Property IO := propertyM do
  let start ← forAll (Gen.element [0, 0, 1, 8192, 2 ^ 40])
  let before ← forAll (Gen.element [0, 5, 2 ^ 64, 2 ^ 255])
  let genPart : Gen (Nat × Item × Item) := do
    let difficulty ← Gen.element [0, 1, 131072, 2 ^ 64, 2 ^ 200]
    let body ← genAnyItem 2
    let receipts ← Item.list <$> Gen.list (.linear 0 3) (genAnyItem 1)
    pure (difficulty, body, receipts)
  let parts ← forAllWith (fun l => s!"{l.length} blocks of difficulties {l.map (·.1)}")
    (Gen.list (.constant 0 6) genPart)
  let count := parts.length
  let place ← forAll (Gen.nat (.constant 0 (count - 1)))
  let fault ← forAll (Gen.frequency [(5, pure "-"), (1, pure "other"),
    (2, Gen.element ["number", "parent", "total"]), (4, Gen.element (fileFaults.map (·.1)))])
  let chainFault := if ["number", "parent", "total"].contains fault then fault else ""
  let blocks := eraChain start before parts chainFault place
  -- Whether the fault breaks the file.
  --
  -- The first block of a file that starts after the genesis block has nothing before it.
  --
  -- So its parent and its total difficulty are not checked.
  let breaks : Bool :=
    if fault = "-" ∨ fault = "other" then false
    else if fault = "number" then count > 0
    else if fault = "parent" then count > 0 ∧ place > 0
    else if fault = "total" then count > 0 ∧ (place > 0 ∨ start = 0 ∨ count > 1)
    else ((fileFaults.lookup fault).map fun least => decide (least ≤ count)).getD true
  pure do
    let text ← orFail (showEraBlocks blocks)
    let fileFault := if chainFault = "" then fault else "-"
    let answer ← oracle.ask ["era1", toString start, text, fileFault]
    let (file, root) := match answer.splitOn "|" with
      | [file, root] => (file, root)
      | _ => ("", "")
    if root = "" then failWith s!"the oracle answered: {answer.take 300}"
    let bytes ← orFail ((unhex? file).elim (.error "the file is not hexadecimal") .ok)
    let got := decodeEra1 bytes
    cover 25 "a file reads" got.isOk
    cover 25 "a file with a fault is refused" (!got.isOk)
    classify "a file of three blocks or more reads" (got.isOk ∧ count ≥ 3)
    classify "a file with no block reads" (got.isOk ∧ count = 0)
    classify "a file with other records reads" (got.isOk ∧ fault = "other")
    classify "a file that starts at the genesis block reads" (got.isOk ∧ start = 0)
    classify "a total difficulty of 2^64 or more reads"
      (got.isOk ∧ blocks.any (·.total ≥ 2 ^ 64))
    match got with
    | .error e =>
      annotate s!"EthLib: {reprStr e}"
      classify s!"refused: {fault}" true
      ensure breaks "EthLib refuses an era1 file"
    | .ok era =>
      ensure (!breaks) s!"EthLib reads a file with the fault {fault}"
      era.startingNumber === start
      era.blocks.length === count
      hexVec era.accumulator === root
      era.others.length === (if fault = "other" then 2 else 0)
      for (mine, theirs) in era.blocks.zip blocks do
        (some mine.header.data.toList) === (encode theirs.header).toOption.map (·.data.toList)
        (some mine.body.data.toList) === (encode theirs.body).toOption.map (·.data.toList)
        (some mine.receipts.data.toList) === (encode theirs.receipts).toOption.map (·.data.toList)
        mine.totalDifficulty.toNat === theirs.total

/-- A file holds at most 8192 blocks: one of 8192 reads, and one of 8193 is refused. -/
def era1Limit (oracle : Oracle) : Property IO := propertyM do
  let count ← forAll (Gen.element [8192, 8193])
  pure do
    let blocks := eraChain 0 0 (List.replicate count (1, .list [], .list [])) "" 0
    let text ← orFail (showEraBlocks blocks)
    let answer ← oracle.ask ["era1", "0", text, "-"]
    let (file, root) := match answer.splitOn "|" with
      | [file, root] => (file, root)
      | _ => ("", "")
    let bytes ← orFail ((unhex? file).elim (.error "the file is not hexadecimal") .ok)
    match decodeEra1 bytes with
    | .ok era =>
      count === 8192
      era.blocks.length === 8192
      hexVec era.accumulator === root
      classify "8192 blocks read" true
    | .error e =>
      annotate s!"EthLib: {reprStr e}"
      count === 8193
      ensure (e matches .tooManyBlocks _) "8193 blocks are not refused for their number"
      classify "8193 blocks are refused" true

/-! ## The form of an error -/

/-- An error shows its constructor in full and each value under its name, a hash in hex.

A string of bytes shows as `0x` and two digits a byte, and a word as its number.

An absent value shows as `none`.

An application in an argument position is in parentheses. -/
def errorFormat : Property IO := pureIO do
  let bytes ← forAllWith hex (genBytes (.linear 0 40))
  let hash ← forAllWith hexVec (Vector.ofFn (n := 32) <$> (fun (l : List UInt8) i => l.getD i.val 0)
    <$> Gen.list (.singleton 32) genByte)
  let n ← forAll (genNatBits 256)
  let i ← forAll (Gen.nat (.linear 0 1000))
  let hexOf (b : ByteArray) : String := "0x" ++ (if b.isEmpty then "" else hex b)
  (namedArg "data" bytes).pretty === s!"(data := {hexOf bytes})"
  (namedArg "hash" hash).pretty === s!"(hash := 0x{hexVec hash})"
  (namedArg "word" (BitVec.ofNat 256 n)).pretty === s!"(word := {n})"
  (namedArg "index" i).pretty === s!"(index := {i})"
  (namedArg "maybe" (none : Option Hash32)).pretty === "(maybe := none)"
  (namedArg "maybe" (some hash)).pretty === s!"(maybe := some 0x{hexVec hash})"
  (constructorFormat "A.b" [namedArg "i" i] 0).pretty 200 === s!"A.b (i := {i})"
  (constructorFormat "A.b" [namedArg "i" i] 1024).pretty 200 === s!"(A.b (i := {i}))"
  (constructorFormat "A.b" [] 0).pretty === "A.b"
  -- An error of this layer shows that way.
  --
  -- A long error breaks its line before each value, which is a space here.
  (reprStr (Era1Error.parentHash i hash hash)).replace "\n " "" ===
    s!"EthLib.Execution.History.Era1Error.parentHash (i := {i}) (expected := 0x{hexVec hash}) \
      (actual := 0x{hexVec hash})"
  reprStr (Era1Error.wrongSize 0x0600 i) ===
    s!"EthLib.Execution.History.Era1Error.wrongSize (type := 1536) (size := {i})"

end RpcProperty

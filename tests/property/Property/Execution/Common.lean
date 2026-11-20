import Hedgehog
import Support
import EthLib.Execution.Transactions
import EthLib.Execution.Blocks
import EthLib.Execution.Trie
import EthLib.Execution.State

/-!
# What the modules of the execution driver share

The forks that the reference knows, and RLP items with a bias to the edges of each field.

Also a mutation of an item that keeps it almost valid.
-/

open Hedgehog Support EthLib EthLib.Base
open EthLib.Serialization.Rlp

namespace ExecutionProperty

/-- The forks that execution-specs 2.20.0 has, with the name of each there. -/
def eelsForks : List (Fork × String) := [
  (.frontier, "frontier"), (.homestead, "homestead"), (.daoFork, "dao_fork"),
  (.tangerineWhistle, "tangerine_whistle"), (.spuriousDragon, "spurious_dragon"),
  (.byzantium, "byzantium"), (.petersburg, "constantinople"), (.istanbul, "istanbul"),
  (.muirGlacier, "muir_glacier"), (.berlin, "berlin"), (.london, "london"),
  (.arrowGlacier, "arrow_glacier"), (.grayGlacier, "gray_glacier"), (.paris, "paris"),
  (.shapella, "shanghai"), (.dencun, "cancun"), (.pectra, "prague"), (.fusaka, "osaka"),
  (.bpo1, "bpo1"), (.bpo2, "bpo2")]

/-- The forks of EthLib that the reference has no module for, each beside a fork of its rules.

Constantinople has the rules of Petersburg in EthLib, as the reference names them.

The three forks of the consensus layer change no rule of the execution layer. -/
def sameRuleForks : List (Fork × String) := [
  (.constantinople, "constantinople"), (.phase0, "muir_glacier"), (.altair, "london"),
  (.bellatrix, "gray_glacier")]

/-- The forks that the released reference answers for: its own 20, and the four beside them. -/
def releaseForks : List (Fork × String) := eelsForks ++ sameRuleForks

/-- The forks that only the branch `forks/amsterdam` of execution-specs has.

Hegotá has no rule of its own yet, so it stands beside Amsterdam. -/
def lateForks : List (Fork × String) := [
  (.bpo3, "bpo3"), (.bpo4, "bpo4"), (.bpo5, "bpo5"), (.glamsterdam, "amsterdam"),
  (.hegota, "amsterdam")]

/-- The reference processes: the release, and the later branch where it is installed. -/
structure Oracles where
  /-- execution-specs as released, with every fork from Frontier to BPO2. -/
  main : Oracle
  /-- The branch `forks/amsterdam`, or none where it is not installed. -/
  late : Option Oracle

/-- The forks that the references answer for: every fork of EthLib where both are there. -/
def Oracles.forks (oracles : Oracles) : List (Fork × String) :=
  releaseForks ++ (if oracles.late.isSome then lateForks else [])

/-- The reference that answers for a fork. -/
def Oracles.at (oracles : Oracles) (fork : Fork × String) : Oracle :=
  if lateForks.any fun late => late.1 == fork.1 then oracles.late.getD oracles.main
  else oracles.main

/-- The family of a fork: the forks between two changes of the formats that this driver reads. -/
def forkFamily (fork : Fork) : String :=
  if fork < .homestead then "Frontier"
  else if fork < .spuriousDragon then "Homestead to Tangerine Whistle"
  else if fork < .byzantium then "Spurious Dragon"
  else if fork < .berlin then "Byzantium to Muir Glacier"
  else if fork < .london then "Berlin"
  else if fork < .paris then "London to Gray Glacier"
  else if fork < .shapella then "Paris"
  else if fork < .dencun then "Shapella"
  else if fork < .pectra then "Dencun"
  else if fork < .fusaka then "Pectra"
  else if fork < .glamsterdam then "Fusaka to BPO5"
  else "Glamsterdam on"

/-- A fork of a list: a family first, each as often as another, then a fork of the family.

So Pectra, which is one fork, is drawn as often as the seven forks from Byzantium to Phase 0. -/
def genForkOf (forks : List (Fork × String)) : Gen (Fork × String) :=
  let families := (forks.map fun fork => forkFamily fork.1).eraseDups
  Gen.choice (families.map fun family =>
    Gen.element (forks.filter fun fork => forkFamily fork.1 == family))

/-- A fork that the released reference answers for. -/
def genFork : Gen (Fork × String) := genForkOf releaseForks

/-- A fork before Paris, which has a difficulty. -/
def genWorkFork : Gen (Fork × String) :=
  genForkOf (releaseForks.filter fun fork => fork.1 < .paris)

/-- The order of the group of secp256k1. -/
def curveOrder : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- A number of at most `bits` bits, often at an edge, or one of the values given. -/
def genNatNear (bits : Nat) (edges : List Nat := []) : Gen Nat :=
  Gen.frequency [(4, Gen.nat (.exponential 0 (2 ^ bits - 1))), (2, genNatBits bits),
    (if edges.isEmpty then 0 else 3, Gen.element edges)]

/-- The bytes of a list. -/
def bytesOf (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-- The bytes that the oracle answered, or none for an answer that is not hexadecimal. -/
def vectorOf? (n : Nat) (text : String) : Option (Vector UInt8 n) :=
  (unhex? text).bind (exactBytes? n)

/-- A vector of `n` bytes. -/
def genVector (n : Nat) : Gen (Vector UInt8 n) :=
  (fun bytes => (Vector.ofFn fun (i : Fin n) => bytes.getD i.val 0)) <$>
    Gen.list (.singleton n) genByte

/-- An address: one of four, so that they meet, or any. -/
def genAddress : Gen Address :=
  Gen.frequency [(3, (fun (b : UInt8) => Vector.replicate 20 b) <$> Gen.element [0, 1, 2, 0xff]),
    (1, genVector 20)]

/-- A 32-byte word: one of a few, or any. -/
def genWord : Gen Bytes32 :=
  Gen.frequency [(3, (fun (b : UInt8) => Vector.replicate 32 b) <$> Gen.element [0, 1, 2]),
    (1, genVector 32)]

/-- The hexadecimal of a vector of bytes. -/
def hexV {n : Nat} (v : Vector UInt8 n) : String := hex ⟨v.toArray⟩

/-- Where a mutation lands in an item, and what it does there. -/
structure Mutation where
  /-- The path to the item: the index of the child to enter at each list, modulo its length. -/
  path : List Nat
  /-- What happens to the item at the end of the path. -/
  kind : Nat
  deriving Repr

/-- One change of an item, by its kind: the changes that a careless decoder forgives. -/
def mutateHere (kind : Nat) : Item → Item
  | .bytes b =>
    match kind % 7 with
    | 0 => .bytes (⟨#[0]⟩ ++ b)
    | 1 => .bytes (b.extract 1 b.size)
    | 2 => .bytes (b ++ ⟨#[1]⟩)
    | 3 => .list []
    | 4 => .bytes .empty
    | 5 => .list [.bytes b]
    | _ => .bytes (b.extract 0 (b.size - 1))
  | .list items =>
    match kind % 6 with
    | 0 => .list (items.dropLast)
    | 1 => .list (items ++ [.bytes .empty])
    | 2 => .list (items ++ items.take 1)
    | 3 => .bytes .empty
    | 4 => .list (items.drop 1)
    | _ => .list [.list items]

/-- The item with one change at the end of a path. -/
def mutate : List Nat → Nat → Item → Item
  | index :: rest, kind, .list items =>
    if items.isEmpty then mutateHere kind (.list items)
    else .list (items.mapIdx fun i item =>
      if i = index % items.length then mutate rest kind item else item)
  | _, kind, item => mutateHere kind item

/-- A mutation that reaches into the lists of a transaction, a receipt or a header. -/
def genMutation : Gen Mutation :=
  Gen.zipWith Mutation.mk (Gen.list (.linear 1 4) (Gen.nat (.constant 0 15)))
    (Gen.nat (.constant 0 41))

/-- The item, changed by each mutation in turn. -/
def mutateAll (mutations : List Mutation) (item : Item) : Item :=
  mutations.foldl (fun item m => mutate m.path m.kind item) item

/-- The encoding of an item, which fails for no item that a generator here makes. -/
def enc (item : Item) : ByteArray := (encode item).toOption.getD .empty

/-- The text of an answer of EthLib: the value, or `error`. -/
def orError {ε : Type} (result : Except ε String) : String :=
  match result with
  | .ok text => text
  | .error _ => "error"

/-- The name of the constructor of an error: the last word of its head, as `Repr` writes it. -/
def errorName {ε : Type} [Repr ε] (error : ε) : String :=
  let text := (reprStr error).toList.dropWhile (· == '(')
  let head := String.ofList (text.takeWhile fun c => c.isAlphanum || c == '.' || c == '_')
  (head.splitOn ".").getLastD head

/-- Whether a run is long enough for the minimums of `coverMin`, which `main` sets.

A share depends on the number of cases, and a run of 100 cases has only small ones. -/
initialize longRun : IO.Ref Bool ← IO.mkRef false

/-- Count the case under the name when covered, and in a long run require a share of the cases.

The minimums are about a third of the shares of a run of 1,000 cases. -/
def coverMin (minimum : Nat) (name : String) (covered : Bool) : TestT IO Unit := do
  if ← longRun.get then cover minimum name covered else classify name covered

/-- Count the case under one name, and require a share of the cases for each name of a list.

A name outside the list is counted with no minimum. -/
def coverOne (minimum : Nat) (names : List String) (name : String) :
    TestT IO Unit := do
  for other in names do
    coverMin minimum other (other == name)
  unless names.contains name do
    label name

/-- Count the case under the name of its fork family. -/
def labelFork (fork : Fork) : TestT IO Unit :=
  label s!"fork: {forkFamily fork}"

end ExecutionProperty

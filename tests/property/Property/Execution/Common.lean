import Hedgehog
import Support
import EthLib.Execution.Transactions
import EthLib.Execution.Blocks
import EthLib.Execution.Trie
import EthLib.Execution.State

/-!
# What the modules of the execution driver share

The forks that the reference knows, RLP items with a bias to the edges of each field, and a
mutation of an item that keeps it almost valid.
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

/-- A fork of the reference, the later ones as often as the earlier. -/
def genFork : Gen (Fork × String) := Gen.element eelsForks

/-- The forks of the reference before Paris, which have a difficulty. -/
def genWorkFork : Gen (Fork × String) := Gen.element (eelsForks.take 13)

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

end ExecutionProperty

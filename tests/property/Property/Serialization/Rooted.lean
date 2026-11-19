import Hedgehog
import Support
import Property.Serialization.Common

/-!
# Typed SSZ values that keep their tree, as state machines

A rooted list or vector rehashes one path on a write.
The model is the plain list of elements, and the root of the model is the reference's.

- `StateMachine`: a fork-chosen list, before and after the switch to a progressive list.
- `Command`: a vector of basic elements and one of composite ones, in madhouse mode.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Serialization EthLib.Serialization.Ssz

namespace SerializationProperty

/-- A pair of integers, a container of two fields. -/
structure Pair where
  first : UInt64
  second : UInt16
  deriving Repr, DecidableEq

instance : SszType Pair :=
  SszType.container ["f0", "f1"] (fun p => (p.first, p.second)) (fun (a, b) => ⟨a, b⟩)

/-- An element type of the rooted sequences, made from a number. -/
class Element (α : Type) extends SszType α where
  /-- The element of a number. -/
  make : Nat → α

instance : Element UInt64 := { make := UInt64.ofNat }
instance : Element UInt16 := { make := UInt16.ofNat }
instance : Element Bool := { make := fun n => n % 2 == 1 }
instance : Element U256 := { make := fun n => BitVec.ofNat 256 (n * 2 ^ 190 + n) }
instance : Element (Vector UInt8 32) :=
  { make := fun n => Vector.ofFn fun i => UInt8.ofNat (n + i.val) }
instance : Element Pair := { make := fun n => ⟨UInt64.ofNat (n * 2 ^ 40), UInt16.ofNat n⟩ }

/-- The elements of the numbers, as the oracle reads them. -/
def elementsText (α : Type) [Element α] (numbers : List Nat) : String :=
  valueText (.seq (numbers.map fun n => SszType.toValue (Element.make n : α)))

/-- The bytes and the root of a typed value, as the oracle writes them. -/
def typedEncoded {α : Type} [SszType α] (a : α) : String :=
  match SszType.encode a, SszType.root a with
  | .ok bytes, .ok root => s!"{hex bytes} {hex ⟨root⟩}"
  | .error e, _ => s!"error encode {repr e}"
  | _, .error e => s!"error root {repr e}"

/-! ## A fork-chosen list: `StateMachine` -/

/-- A write to a list. -/
inductive ListStep where
  | push (number : Nat)
  | pushMany (numbers : List Nat)
  | set (index number : Nat)
  deriving Repr, BEq

/-- The model of a list: its elements, as numbers. -/
structure ListModel where
  numbers : List Nat
  deriving Repr

/-- The model: a list of at most `limit` numbers before the switch, of any count after. -/
def listModel (bounded : Bool) (limit : Nat) : Model ListModel ListStep where
  initState := ListModel.mk <$> Gen.list (.linear 0 3) (Gen.nat (.linear 0 255))
  transitions s :=
    let number := Gen.frequency [(3, Gen.nat (.linear 0 255)), (1,
        Gen.nat (.exponential 0 (2 ^ 64)))]
    Gen.frequency [
      (4, .push <$> number),
      (1, .pushMany <$> Gen.list (.linear 1 40) number),
      (3, Gen.zipWith .set (Gen.frequency [(2, Gen.nat (.constant 0 (s.numbers.length - 1))),
        (1, pure (s.numbers.length - 1))]) number)]
  apply s
    | .push number => ⟨s.numbers ++ [number]⟩
    | .pushMany numbers => ⟨s.numbers ++ numbers⟩
    | .set index number => ⟨s.numbers.set index number⟩
  preconditions s
    | .push _ => !bounded || s.numbers.length < limit
    | .pushMany numbers => !bounded || s.numbers.length + numbers.length ≤ limit
    | .set index _ => index < s.numbers.length

/-- The list with the elements pushed one by one, or none where the limit refuses one. -/
def pushAll {switch fork : Fork} {α : Type} [Element α] {limit : Nat}
    (list : RootedForkList switch fork α limit) :
    List Nat → Option (RootedForkList switch fork α limit)
  | [] => some list
  | number :: rest =>
    if room : fork < switch → list.data.size < limit then
      pushAll (list.push (Element.make number) room) rest
    else none

/-- The rooted fork-chosen list against the list of its elements.

After each write, the bytes and the root are those the reference gives the model.
The list is also read back from its bytes, which builds its tree afresh: the roots agree. -/
def listMachine (oracle : Oracle) (switch fork : Fork) (α : Type) [Element α] (limit : Nat)
    (typeOf : String) :
    StateMachine ListModel ListStep (RootedForkList switch fork α limit) IO where
  toModel := listModel (fork < switch) limit
  initSut s :=
    match pushAll (RootedForkList.ofData #[] (fun _ => Nat.zero_le _)) s.numbers with
    | some list => pure list
    | none => throw (IO.userError "the first elements do not fit")
  applySut list _ step :=
    match step with
    | .push number =>
      match pushAll list [number] with
      | some next => pure next
      | none => failWith "the push was refused"
    | .pushMany numbers =>
      match pushAll list numbers with
      | some next => pure next
      | none => failWith "the pushes were refused"
    | .set index number =>
      if inside : index < list.data.size then pure (list.set index (Element.make number) inside)
      else failWith "the index is outside the list"
  invariants list s := do
    let expected ← oracle.ask ["sszenc", typeOf, elementsText α s.numbers]
    typedEncoded list === expected
    -- The same elements read from their bytes have a tree built from the leaves up.
    match SszType.encode list >>= SszType.decode (α := RootedForkList switch fork α limit) with
    | .ok fresh => typedEncoded fresh === expected
    | .error e => failWith s!"the bytes of the list do not read back: {repr e}"

/-- The property of a list machine, with sequences up to a length. -/
def listProperty (oracle : Oracle) (bounded : Bool) (α : Type) [Element α] (limit : Nat)
    (elementType : String) (length : Nat) : Property IO :=
  if bounded then
    (listMachine oracle .glamsterdam .fusaka α limit s!"[\"list\",{elementType},{limit}]").property
      (.linear 1 length)
  else
    (listMachine oracle .glamsterdam .glamsterdam α limit s!"[\"plist\",{elementType}]").property
      (.linear 1 length)

/-! ## Rooted vectors: `Command`, in madhouse mode -/

/-- The length of the vector of integers: ten nodes, so a tree with zero nodes beside them. -/
abbrev wordCount : Nat := 37

/-- The length of the vector of containers. -/
abbrev pairCount : Nat := 5

/-- The two vectors under test, and the numbers of their elements. -/
structure VectorState where
  words : RootedVector UInt64 wordCount
  wordModel : List Nat
  pairs : RootedVector Pair pairCount
  pairModel : List Nat
  /-- The writes so far, which the report of a failure shows. -/
  writes : Nat

instance : Inhabited VectorState :=
  ⟨⟨.ofVector (Vector.replicate _ 0), List.replicate wordCount 0,
    .ofVector (Vector.replicate _ (Element.make 0)), List.replicate pairCount 0, 0⟩⟩

/-- Both vectors have the bytes and the root that the reference gives the model. -/
def checkVectors (oracle : Oracle) (s : VectorState) : TestT IO Unit := do
  typedEncoded s.words === (← oracle.ask ["sszenc", s!"[\"vec\",[\"uint\",8],{wordCount}]",
    elementsText UInt64 s.wordModel])
  typedEncoded s.pairs === (← oracle.ask ["sszenc",
    s!"[\"vec\",[\"cont\",[\"f0\",\"f1\"],[[\"uint\",8],[\"uint\",2]]],{pairCount}]",
    elementsText Pair s.pairModel])

/-- Write one integer. -/
structure SetWord where
  index : Nat
  number : Nat

instance : Command SetWord VectorState Oracle IO where
  check c _ := c.index < wordCount
  apply c s := do
    if inside : c.index < wordCount then
      pure { s with words := s.words.set c.index (UInt64.ofNat c.number) inside,
                    wordModel := s.wordModel.set c.index c.number, writes := s.writes + 1 }
    else failWith "the index is outside the vector"
  label c := s!"SET_WORD({c.index}, {c.number})"
  build _ := Gen.zipWith SetWord.mk
    (Gen.frequency [(3, Gen.nat (.constant 0 (wordCount - 1))), (1, Gen.element [0, 3, 4, 31, 32,
        35, 36])])
    (Gen.nat (.exponential 0 (2 ^ 64 - 1)))

/-- Write one container. -/
structure SetPair where
  index : Nat
  number : Nat

instance : Command SetPair VectorState Oracle IO where
  check c _ := c.index < pairCount
  apply c s := do
    if inside : c.index < pairCount then
      pure { s with pairs := s.pairs.set c.index (Element.make c.number) inside,
                    pairModel := s.pairModel.set c.index c.number, writes := s.writes + 1 }
    else failWith "the index is outside the vector"
  label c := s!"SET_PAIR({c.index}, {c.number})"
  build _ :=
    Gen.zipWith SetPair.mk (Gen.nat (.constant 0 (pairCount - 1))) (Gen.nat (.linear 0 9999))

/-- Drop the first integers and append fresh ones. -/
structure ShiftWords where
  fresh : List Nat

instance : Command ShiftWords VectorState Oracle IO where
  check c _ := c.fresh.length ≤ wordCount
  apply c s := do
    let fresh : Vector UInt64 c.fresh.length :=
      Vector.ofFn fun i => UInt64.ofNat (c.fresh.getD i.val 0)
    if le : c.fresh.length ≤ wordCount then
      pure { s with words := s.words.shift fresh le,
                    wordModel := s.wordModel.drop c.fresh.length ++
                        c.fresh, writes := s.writes + 1 }
    else failWith "more fresh elements than the vector holds"
  label c := s!"SHIFT_WORDS({c.fresh})"
  build _ := ShiftWords.mk <$> Gen.frequency [
    (3, Gen.list (.linear 0 6) (Gen.nat (.linear 0 255))),
    (1, Gen.list (.constant (wordCount - 1) wordCount) (Gen.nat (.linear 0 255)))]

/-- Drop the first containers and append fresh ones. -/
structure ShiftPairs where
  fresh : List Nat

instance : Command ShiftPairs VectorState Oracle IO where
  check c _ := c.fresh.length ≤ pairCount
  apply c s := do
    let fresh : Vector Pair c.fresh.length :=
      Vector.ofFn fun i => Element.make (c.fresh.getD i.val 0)
    if le : c.fresh.length ≤ pairCount then
      pure { s with pairs := s.pairs.shift fresh le,
                    pairModel := s.pairModel.drop c.fresh.length ++
                        c.fresh, writes := s.writes + 1 }
    else failWith "more fresh elements than the vector holds"
  label c := s!"SHIFT_PAIRS({c.fresh})"
  build _ := ShiftPairs.mk <$> Gen.list (.linear 0 pairCount) (Gen.nat (.linear 0 9999))

/-- Read both vectors back from their bytes, which drops the trees they kept. -/
structure Reload where

instance : Command Reload VectorState Oracle IO where
  apply _ s := do
    match SszType.encode s.words >>= SszType.decode (α := RootedVector UInt64 wordCount),
      SszType.encode s.pairs >>= SszType.decode (α := RootedVector Pair pairCount) with
    | .ok words, .ok pairs => pure { s with words, pairs }
    | _, _ => failWith "a vector does not read back from its bytes"
  label _ := "RELOAD"
  build _ := pure {}

/-- Compare both vectors with the reference. -/
structure CheckRoots where
  oracle : Oracle

instance : Command CheckRoots VectorState Oracle IO where
  apply c s := do
    checkVectors c.oracle s
    pure s
  label _ := "CHECK"
  build oracle := pure ⟨oracle⟩

/-- A write outside a vector is no command: its check refuses it, and the state stays. -/
structure SetOutside where
  index : Nat

instance : Command SetOutside VectorState Oracle IO where
  check c _ := c.index < wordCount
  apply _ _ := failWith "a write outside the vector ran"
  label c := s!"SET_OUTSIDE({c.index})"
  build _ := SetOutside.mk <$> Gen.nat (.constant wordCount (wordCount + 5))

/-- Random writes to the two vectors, with the reference asked after every few. -/
def vectorScenario (oracle : Oracle) : Property IO :=
  scenario .madhouse oracle [
    Command.gen SetWord, Command.gen SetWord, Command.gen SetPair, Command.gen ShiftWords,
    Command.gen ShiftPairs, Command.gen Reload, Command.gen CheckRoots, Command.gen CheckRoots,
    Command.gen SetOutside]

end SerializationProperty

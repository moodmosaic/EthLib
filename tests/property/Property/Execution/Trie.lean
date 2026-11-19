import Property.Execution.Common

/-!
# The Merkle Patricia Trie, against execution-specs and py-trie

The keys are short and over few bytes, so that they share prefixes and one is a prefix of another.

The values lie on both sides of the 32 bytes at which a parent holds a child by its hash.
-/

open Hedgehog Support EthLib EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace ExecutionProperty

/-- A key: a few bytes from a small alphabet, or 32 bytes that differ only at the end. -/
def genKeyBytes : Gen ByteArray :=
  let short := bytesOf <$> Gen.list (.linear 0 4) (Gen.element [0x00, 0x01, 0x10, 0x11, 0xff])
  let long := (fun (tail : List UInt8) => bytesOf (List.replicate 30 0x11 ++ tail)) <$>
    Gen.list (.singleton 2) (Gen.element [0x00, 0x01, 0x10, 0xf0])
  Gen.frequency [(4, short), (1, long)]

/-- A value that is not empty, of a length around the 32 bytes of a hash. -/
def genValue : Gen ByteArray := do
  let length ← Gen.frequency [(3, Gen.nat (.constant 1 4)), (3, Gen.nat (.constant 25 34)),
    (1, Gen.nat (.linear 1 80))]
  genBytesN length

/-- A value, or now and then the empty one, which deletes its key. -/
def genValueOrNone : Gen ByteArray := Gen.frequency [(4, genValue), (1, pure .empty)]

/-- Writes to a trie, in order. -/
def genWrites : Gen (List (ByteArray × ByteArray)) :=
  Gen.list (.linear 0 24) (Gen.zip genKeyBytes genValueOrNone)

/-- A write as a word of a command of the oracle. -/
def pairWord (entry : ByteArray × ByteArray) : String := s!"{hex entry.1}={hex entry.2}"

/-- The trie after the writes. -/
def trieOf (secured : Bool) (writes : List (ByteArray × ByteArray)) : Trie :=
  writes.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured, []⟩

/-- The value of a key after the writes: the last one written, by a plain search. -/
def lastWrite (writes : List (ByteArray × ByteArray)) (key : ByteArray) : ByteArray :=
  ((writes.reverse.find? fun (k, _) => k.data == key.data).map Prod.snd).getD .empty

/-- How the writes show in a report. -/
def showWrites (writes : List (ByteArray × ByteArray)) : String :=
  " ".intercalate (writes.map pairWord)

/-- The root of a trie is the root of execution-specs, plain or secured. -/
def trieRoot (oracle : Oracle) : Property IO := propertyM do
  let secured ← forAll Gen.bool
  let writes ← forAllWith showWrites genWrites
  pure do
    let expected ← oracle.ask (["trieroot", if secured then "1" else "0"] ++ writes.map pairWord)
    orError (hexV <$> root keccak256 (trieOf secured writes)) === expected

/-- The value that a proof gives, in the words of the oracle. -/
def proofAnswer (result : Except ProofError (Option ByteArray)) : String :=
  match result with
  | .ok (some value) => hex value
  | .ok none => "absent"
  | .error _ => "error"

/-- The proof of a key is the proof of py-trie, and it shows the value of the key or its absence.

py-trie lists every node on the path, and EthLib the ones that their parent holds by hash.

So the oracle keeps those of py-trie. -/
def trieProof (oracle : Oracle) : Property IO := propertyM do
  let writes ← forAllWith showWrites genWrites
  let key ← forAllWith hex (Gen.choice [genKeyBytes,
    if writes.isEmpty then genKeyBytes else Gen.element (writes.map Prod.fst)])
  pure do
    let trie := trieOf false writes
    let answer ← oracle.ask (["trieproof", hex key] ++ writes.map pairWord)
    let proof := (getProof keccak256 trie key).toOption.getD []
    let rootHash := orError (hexV <$> root keccak256 trie)
    " ".intercalate (rootHash :: proof.map hex) === answer
    let truth := lastWrite writes key
    match root keccak256 trie with
    | .ok r => proofAnswer (verifyProof keccak256 r false key proof) ===
        (if truth.isEmpty then "absent" else hex truth)
    | .error _ => failWith "no root"

/-- A change of a proof. -/
inductive ProofChange where
  /-- A node removed. -/
  | drop (index : Nat)
  /-- A node written twice. -/
  | repeated (index : Nat)
  /-- A node changed as an item and encoded again. -/
  | node (index : Nat) (mutation : Mutation)
  /-- A byte of a node changed. -/
  | byte (index position : Nat) (value : UInt8)
  /-- The nodes of the proof of another key, in place of the tail. -/
  | graft (keep : Nat)
  deriving Repr

/-- A change of a proof, at an index that is reduced modulo the length. -/
def genProofChange : Gen ProofChange :=
  let index := Gen.nat (.constant 0 5)
  Gen.choice [ProofChange.drop <$> index, ProofChange.repeated <$> index,
    ProofChange.node <$> index <*> genMutation,
    ProofChange.byte <$> index <*> Gen.nat (.constant 0 600) <*> genByte,
    ProofChange.graft <$> index]

/-- The proof after a change; `other` is the proof of another key. -/
def ProofChange.apply (proof other : List ByteArray) : ProofChange → List ByteArray
  | .drop i => proof.eraseIdx (i % (proof.length + 1))
  | .repeated i =>
    let i := i % (proof.length + 1)
    proof.take (i + 1) ++ proof.drop i
  | .node i mutation => proof.mapIdx fun j encoded =>
    if j = i % proof.length then
      match decode encoded with
      | .ok item => enc (mutate mutation.path mutation.kind item)
      | .error _ => encoded
    else encoded
  | .byte i position value => proof.mapIdx fun j encoded =>
    if j = i % proof.length ∧ 0 < encoded.size then encoded.set! (position % encoded.size) value
    else encoded
  | .graft keep => proof.take (keep % (proof.length + 1)) ++ other.drop (keep % (other.length + 1))

/-- A proof that EthLib accepts gives the value of the key in the trie, whatever was done to it.

The proofs are those of a key, changed:

- A node dropped, repeated or rewritten.
- A byte changed.
- The tail of the proof of another key.

A proof that still reads the trie's nodes may be accepted, and then it must not lie.

py-trie reads the same proof, and where both accept, they give the same value. -/
def trieProofSound (oracle : Oracle) : Property IO := propertyM do
  let writes ← forAllWith showWrites genWrites
  let keys := if writes.isEmpty then genKeyBytes else
    Gen.choice [genKeyBytes, Gen.element (writes.map Prod.fst)]
  let key ← forAllWith hex keys
  let otherKey ← forAllWith hex keys
  let asked ← forAllWith hex (Gen.frequency [(3, pure key), (1, pure otherKey), (1, genKeyBytes)])
  let changes ← forAll (Gen.list (.constant 0 2) genProofChange)
  pure do
    let trie := trieOf false writes
    let proof := (getProof keccak256 trie key).toOption.getD []
    let other := (getProof keccak256 trie otherKey).toOption.getD []
    let changed := changes.foldl (fun proof change => change.apply proof other) proof
    annotate s!"proof {" ".intercalate (changed.map hex)}"
    let .ok r := root keccak256 trie | failWith "no root"
    let truth := lastWrite writes asked
    let got := proofAnswer (verifyProof keccak256 r false asked changed)
    if got ≠ "error" then
      got === (if truth.isEmpty then "absent" else hex truth)
      -- py-trie 4.0.0 raises on a key that ends inside an extension, so its refusal says nothing.
      let reference ← oracle.ask (["trieverify", hexV r, hex asked] ++ changed.map hex)
      if reference ≠ "error" then got === reference

/-! ## The trie as a state machine -/

/-- A write to the trie: an empty value deletes the key. -/
structure TrieWrite where
  /-- The key. -/
  key : ByteArray
  /-- The value, or the empty byte string to delete the key. -/
  value : ByteArray

instance : Repr TrieWrite where
  reprPrec w _ := s!"{hex w.key}={hex w.value}"

/-- The model of a trie: the keys that are set, each with its value, in no order. -/
structure TrieModel where
  /-- The entries. -/
  entries : List (ByteArray × ByteArray)

instance : Repr TrieModel where
  reprPrec m _ := showWrites m.entries

/-- The model: a list of entries, where a write replaces its key and an empty value removes it.

A write is to a key that is set, three times in five, so that updates and deletions are common. -/
def trieModel : Model TrieModel TrieWrite where
  initState := pure ⟨[]⟩
  transitions s :=
    let key := if s.entries.isEmpty then genKeyBytes else
      Gen.frequency [(3, Gen.element (s.entries.map Prod.fst)), (2, genKeyBytes)]
    Gen.zipWith TrieWrite.mk key (Gen.frequency [(3, genValue), (2, pure .empty)])
  apply s w :=
    let rest := s.entries.filter fun (k, _) => k.data != w.key.data
    ⟨if w.value.isEmpty then rest else (w.key, w.value) :: rest⟩

/-- EthLib's trie under writes, beside py-trie under the same writes.

py-trie changes its nodes in place at each write, and EthLib builds the root from the entries.

After each write the two roots are equal, and EthLib holds the entries of the model.

EthLib's root does not depend on the order in which the entries were set. -/
def trieMachine (oracle : Oracle) : StateMachine TrieModel TrieWrite Trie IO where
  toModel := trieModel
  initSut _ := do
    oracle.stdin.putStrLn "sm_trie\tnew"
    oracle.stdin.flush
    let _ ← oracle.stdout.getLine
    pure ⟨false, []⟩
  applySut trie _ _ w := do
    let trie := trieSet trie w.key w.value
    let expected ← oracle.ask ["sm_trie", "set", hex w.key, hex w.value]
    orError (hexV <$> root keccak256 trie) === expected
    pure trie
  invariants trie s := do
    trie.data.length === s.entries.length
    for (key, value) in s.entries do
      hex (trieGet trie key) === hex value
    -- The root is a function of the entries, not of their order.
    orError (hexV <$> root keccak256 ⟨false, s.entries⟩) ===
      orError (hexV <$> root keccak256 trie)

end ExecutionProperty

namespace ExecutionProperty

/-- The empty proof shows that a key is absent from the empty trie, as it does for py-trie.

The empty trie has no node, so a proof by "the nodes on the path" (EIP-1186) lists none.

py-trie builds the empty proof, and reads it as the absence of the key.

EthLib builds the proof `[0x80]` and refuses the empty one, so this property fails.

See the findings. -/
def emptyTrieProof (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith hex genKeyBytes
  let secured ← forAll Gen.bool
  pure do
    let .ok emptyRoot := root keccak256 ⟨secured, []⟩ | failWith "no root"
    let reference ← oracle.ask ["trieverify", hexV emptyRoot, hex key]
    reference === "absent"
    annotate s!"EthLib: {repr (verifyProof keccak256 emptyRoot secured key [])}"
    proofAnswer (verifyProof keccak256 emptyRoot secured key []) === reference

end ExecutionProperty

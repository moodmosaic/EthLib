import Hedgehog
import Support
import EthLib.Consensus.SlashingProtection

/-!
# Slashing protection as a state machine, against EIP-3076 read literally

The system is `Interchange`: the record of a signer, with `checkBlock`, `checkAttestation`,
`recordBlock`, `recordAttestation` and `importFile`.

The model is a `Book`, written from the text of EIP-3076 and not from EthLib:

- `held` is the data that the five conditions of the EIP range over, as plain lists.
  A signature appends a record, and an import keeps the maxima, as the section Advice for Minimal
  Databases says.
- `history` is every message ever signed or imported, with nothing dropped.

Two claims are checked after every request:

- EthLib refuses exactly when one of the five conditions, applied to `held`, says refuse.
- Safety, which no strategy may break: an accepted message is not slashable with any message of
  `history`, by the definitions of a double block, a double vote and a surround vote.

The same steps run under both state machine styles of lean-hedgehog: a `StateMachine` whose
generator reads the model to aim at the records that exist, and a `Command` scenario in madhouse
mode whose commands are generated blind.
-/

open Hedgehog Support EthLib EthLib.Consensus Lean

namespace SlashingProperty

/-! ## The model -/

/-- A block record: the key, the slot, and the variant of the block when its root is known. -/
structure BlockRec where
  key : Nat
  slot : Nat
  variant : Option Nat
  deriving Repr, BEq, DecidableEq

/-- A vote record: the key, the epochs, and the variant of the vote when its root is known. -/
structure VoteRec where
  key : Nat
  source : Nat
  target : Nat
  variant : Option Nat
  deriving Repr, BEq, DecidableEq

/-- What the conditions range over, and everything that was ever signed or imported. -/
structure Book where
  heldBlocks : List BlockRec := []
  heldVotes : List VoteRec := []
  historyBlocks : List BlockRec := []
  historyVotes : List VoteRec := []
  deriving Repr, Inhabited

/-- The least of some numbers, none of none. -/
def least : List Nat → Option Nat
  | [] => none
  | x :: xs => some (xs.foldl min x)

/-- The greatest of some numbers, none of none. -/
def greatest : List Nat → Option Nat
  | [] => none
  | x :: xs => some (xs.foldl max x)

/-- A double block: the same key and slot, and not known to be the same block. -/
def BlockRec.slashableWith (old new : BlockRec) : Bool :=
  old.key == new.key && old.slot == new.slot && old.variant != new.variant

/-- Whether a record is the same vote as a new one: the same data, so the same signing root. -/
def VoteRec.same (old new : VoteRec) : Bool :=
  old.key == new.key && old.source == new.source && old.target == new.target &&
    old.variant == new.variant

/-- A double vote or a surround vote, either way, as `is_slashable_attestation_data` has them. -/
def VoteRec.slashableWith (old new : VoteRec) : Bool :=
  old.key == new.key &&
    ((old.target == new.target && !old.same new) ||
      (old.source < new.source && new.target < old.target) ||
      (new.source < old.source && old.target < new.target))

/-- Conditions 1 and 2 of the EIP on a new block. -/
def Book.refusesBlock (book : Book) (new : BlockRec) : Bool :=
  let mine := book.heldBlocks.filter (·.key == new.key)
  let repeated := mine.any (· == new)
  mine.any (·.slashableWith new) ||
    match least (mine.map (·.slot)) with
    | some low => new.slot ≤ low && !repeated
    | none => false

/-- Conditions 3, 4 and 5 of the EIP on a new vote. -/
def Book.refusesVote (book : Book) (new : VoteRec) : Bool :=
  let mine := book.heldVotes.filter (·.key == new.key)
  let repeated := mine.any (·.same new)
  mine.any (·.slashableWith new) ||
    (match least (mine.map (·.source)) with
      | some low => new.source < low
      | none => false) ||
    match least (mine.map (·.target)) with
    | some low => new.target ≤ low && !repeated
    | none => false

/-- The book after a signature. -/
def Book.signBlock (book : Book) (new : BlockRec) : Book :=
  { book with heldBlocks := book.heldBlocks ++ [new], historyBlocks := new :: book.historyBlocks }

/-- The book after a signature. -/
def Book.signVote (book : Book) (new : VoteRec) : Book :=
  { book with heldVotes := book.heldVotes ++ [new], historyVotes := new :: book.historyVotes }

/-- The keys of some records, each once. -/
def keysOf (keys : List Nat) : List Nat := keys.eraseDups

/-- The book after an import by the minimal strategy: per key, the maxima and no root. -/
def Book.importFile (book : Book) (blocks : List BlockRec) (votes : List VoteRec) : Book :=
  let allBlocks := book.heldBlocks ++ blocks
  let allVotes := book.heldVotes ++ votes
  { heldBlocks := (keysOf (allBlocks.map (·.key))).filterMap fun key =>
      (greatest ((allBlocks.filter (·.key == key)).map (·.slot))).map (⟨key, ·, none⟩)
    heldVotes := (keysOf (allVotes.map (·.key))).filterMap fun key => do
      let mine := allVotes.filter (·.key == key)
      pure ⟨key, ← greatest (mine.map (·.source)), ← greatest (mine.map (·.target)), none⟩
    historyBlocks := blocks ++ book.historyBlocks
    historyVotes := votes ++ book.historyVotes }

/-! ## The translation to EthLib -/

/-- The public key of a signer of the model. -/
def pubkey (key : Nat) : Cryptography.Bls.BLSPubkey := Vector.replicate 48 (UInt8.ofNat (key + 1))

/-- A signing root: it commits to the fields of the message, so other fields give another root. -/
def rootOf (kind first second variant : Nat) : Root :=
  (Vector.replicate 32 (0 : UInt8)) |>.set! 0 (UInt8.ofNat kind) |>.set! 1 (UInt8.ofNat first)
    |>.set! 2 (UInt8.ofNat (first / 256)) |>.set! 3 (UInt8.ofNat second)
    |>.set! 4 (UInt8.ofNat (second / 256)) |>.set! 5 (UInt8.ofNat variant)

/-- The signing root of a block of the model. -/
def BlockRec.root (block : BlockRec) : Option Root := block.variant.map (rootOf 1 block.slot 0)

/-- The signing root of a vote of the model. -/
def VoteRec.root (vote : VoteRec) : Option Root :=
  vote.variant.map (rootOf 2 vote.source vote.target)

/-- A file with one entry per record, in the order given: a key may then appear many times. -/
def fileOf (blocks : List BlockRec) (votes : List VoteRec) : Interchange where
  genesisValidatorsRoot := Vector.replicate 32 7
  data := blocks.map (fun b => ⟨pubkey b.key, [⟨UInt64.ofNat b.slot, b.root⟩], []⟩) ++
    votes.map fun v =>
      ⟨pubkey v.key, [], [⟨UInt64.ofNat v.source, UInt64.ofNat v.target, v.root⟩]⟩

/-- The same file with the records of each key in one entry. -/
def groupedFileOf (blocks : List BlockRec) (votes : List VoteRec) : Interchange where
  genesisValidatorsRoot := Vector.replicate 32 7
  data := (keysOf (blocks.map (·.key) ++ votes.map (·.key))).map fun key =>
    ⟨pubkey key,
      (blocks.filter (·.key == key)).map (fun b => ⟨UInt64.ofNat b.slot, b.root⟩),
      (votes.filter (·.key == key)).map
        (fun v => ⟨UInt64.ofNat v.source, UInt64.ofNat v.target, v.root⟩)⟩

/-- The system and the model, side by side. -/
structure World where
  held : Interchange := ⟨Vector.replicate 32 7, []⟩
  book : Book := {}
  deriving Inhabited

instance : Repr World where
  reprPrec world _ := repr world.book

/-- A request to a signer. -/
inductive Op where
  /-- Sign a block. -/
  | block (new : BlockRec)
  /-- Sign a vote. -/
  | vote (new : VoteRec)
  /-- Import a file, with the records of a key in one entry or in one entry each. -/
  | importFile (blocks : List BlockRec) (votes : List VoteRec) (grouped : Bool)
  /-- Write the record as JSON text and read it back. -/
  | export
  deriving Repr

/-- The block records that EthLib holds of a key, as the model writes them. -/
def heldBlocksOf (held : Interchange) (key : Nat) : List (Nat × Option Root) :=
  (held.blocksOf (pubkey key)).map fun b => (b.slot.toNat, b.signingRoot)

/-- The vote records that EthLib holds of a key, as the model writes them. -/
def heldVotesOf (held : Interchange) (key : Nat) : List (Nat × Nat × Option Root) :=
  (held.attestationsOf (pubkey key)).map fun v =>
    (v.sourceEpoch.toNat, v.targetEpoch.toNat, v.signingRoot)

/-- EthLib holds the records of the model, key by key and in order. -/
def agree {m : Type → Type} [Monad m] (world : World) : TestT m Unit := do
  for key in [0, 1, 2, 3] do
    heldBlocksOf world.held key ===
      (world.book.heldBlocks.filter (·.key == key)).map fun b => (b.slot, b.root)
    heldVotesOf world.held key ===
      (world.book.heldVotes.filter (·.key == key)).map fun v => (v.source, v.target, v.root)

/-- Run a request on EthLib and on the model, and check both claims. -/
def step {m : Type → Type} [Monad m] (world : World) : Op → TestT m World
  | .block new => do
    let some root := new.root | failWith "a request has a signing root"
    let accepted := (world.held.checkBlock (pubkey new.key) (UInt64.ofNat new.slot) root).isOk
    annotate s!"EthLib: {reprStr (world.held.checkBlock (pubkey new.key) (.ofNat new.slot) root)}"
    accepted === !world.book.refusesBlock new
    if accepted then
      ensure (!world.book.historyBlocks.any (·.slashableWith new))
        "an accepted block is slashable with an earlier one"
      let next : World := ⟨world.held.recordBlock (pubkey new.key) (UInt64.ofNat new.slot) root,
        world.book.signBlock new⟩
      -- What was signed may be signed again.
      ensure (next.held.checkBlock (pubkey new.key) (UInt64.ofNat new.slot) root).isOk
        "a block just signed is refused as a repeat"
      agree next
      pure next
    else pure world
  | .vote new => do
    let some root := new.root | failWith "a request has a signing root"
    let check := world.held.checkAttestation (pubkey new.key) (UInt64.ofNat new.source)
      (UInt64.ofNat new.target) root
    annotate s!"EthLib: {reprStr check}"
    check.isOk === !world.book.refusesVote new
    if check.isOk then
      ensure (!world.book.historyVotes.any (·.slashableWith new))
        "an accepted vote is slashable with an earlier one"
      let next : World := ⟨world.held.recordAttestation (pubkey new.key) (UInt64.ofNat new.source)
        (UInt64.ofNat new.target) root, world.book.signVote new⟩
      ensure (next.held.checkAttestation (pubkey new.key) (UInt64.ofNat new.source)
        (UInt64.ofNat new.target) root).isOk "a vote just signed is refused as a repeat"
      agree next
      pure next
    else pure world
  | .importFile blocks votes grouped => do
    let file := if grouped then groupedFileOf blocks votes else fileOf blocks votes
    let next : World := ⟨world.held.importFile file, world.book.importFile blocks votes⟩
    agree next
    -- An import is idempotent, and one entry per key is left, in the order of the keys.
    ensure (next.held.importFile ⟨file.genesisValidatorsRoot, []⟩ == next.held)
      "an import of nothing changes a minimal record"
    let keys := next.held.data.map (·.pubkey)
    ensure (keys.eraseDups.length == keys.length) "a key has two entries after an import"
    pure next
  | .export => do
    let document := world.held.toJson
    ensure ((Interchange.ofJson document).toOption == some world.held)
      "the document does not read back"
    match Json.parse document.compress with
    | .ok parsed =>
      ensure ((Interchange.ofJson parsed).toOption == some world.held)
        "the text does not read back"
    | .error e => failWith s!"the text is not JSON: {e}"
    pure world

/-! ## Generators -/

/-- A key: few of them, so that requests meet. -/
def genKey : Gen Nat := Gen.frequency [(4, pure 0), (2, pure 1), (1, Gen.element [2, 3])]

/-- A variant of a message: few of them, so that repeats and double signings happen. -/
def genVariant : Gen Nat := Gen.frequency [(3, pure 0), (1, Gen.element [1, 2])]

/-- A number near some of the numbers that exist, or any small one. -/
def genNear (known : List Nat) (top : Nat) : Gen Nat :=
  if known.isEmpty then Gen.nat (.linear 0 top)
  else Gen.frequency [
    (3, do
      let base ← Gen.element known
      (fun delta : Int => (base + delta).toNat) <$> Gen.int (.linearFrom 0 (-2) 2)),
    (1, Gen.nat (.linear 0 top)),
    (1, (· + (greatest known).getD 0) <$> Gen.nat (.linear 0 3))]

/-- A block request, near the slots of the given records. -/
def genBlock (known : List BlockRec) : Gen BlockRec := do
  let key ← genKey
  let slot ← genNear ((known.filter (·.key == key)).map (·.slot)) 12
  pure ⟨key, slot, some (← genVariant)⟩

/-- A vote request, with a source and a target near those of the given records. -/
def genVote (known : List VoteRec) : Gen VoteRec := do
  let key ← genKey
  let mine := known.filter (·.key == key)
  let (source, target) ← Gen.zip (genNear (mine.map (·.source)) 10)
    (genNear (mine.map (·.target)) 12)
  -- A vote has its source at most at its target, most of the time.
  let ordered ← Gen.frequency [(9, pure true), (1, pure false)]
  let (source, target) := if ordered && target < source then (target, source) else (source, target)
  pure ⟨key, source, target, some (← genVariant)⟩

/-- A record of a file: as a request, but its signing root may be absent. -/
def genFile (blocks : List BlockRec) (votes : List VoteRec) :
    Gen (List BlockRec × List VoteRec) := do
  let dropRoot : Gen Bool := Gen.frequency [(2, pure false), (1, pure true)]
  let fileBlocks ← Gen.list (.linear 0 4) do
    let block ← genBlock blocks
    pure (if ← dropRoot then { block with variant := none } else block)
  let fileVotes ← Gen.list (.linear 0 4) do
    let vote ← genVote votes
    pure (if ← dropRoot then { vote with variant := none } else vote)
  pure (fileBlocks, fileVotes)

/-- A request, aimed at the records that the model holds. -/
def genOp (book : Book) : Gen Op :=
  Gen.frequency [
    (5, Op.block <$> genBlock (book.heldBlocks ++ book.historyBlocks)),
    (7, Op.vote <$> genVote (book.heldVotes ++ book.historyVotes)),
    (2, do
      let (blocks, votes) ← genFile book.historyBlocks book.historyVotes
      Op.importFile blocks votes <$> Gen.bool),
    (1, pure Op.export)]

/-! ## The `StateMachine`: transitions as one type -/

/-- The book after a request, as the model alone computes it. -/
def Book.apply (book : Book) : Op → Book
  | .block new => if book.refusesBlock new then book else book.signBlock new
  | .vote new => if book.refusesVote new then book else book.signVote new
  | .importFile blocks votes _ => book.importFile blocks votes
  | .export => book

/-- EthLib's signer follows the five conditions of EIP-3076 and never signs a slashable pair. -/
def machine : StateMachine Book Op World IO where
  initState := pure {}
  transitions := genOp
  apply := Book.apply
  initSut _ := pure {}
  applySut world after op := do
    let next ← step world op
    -- The model that the driver ran is the model that the step ran.
    ensure (reprStr next.book == reprStr after) "the two runs of the model differ"
    pure next

/-! ## The `Command` scenario: commands as types -/

/-- Sign a block. -/
structure SignBlock where
  new : BlockRec

instance : Command SignBlock World Unit IO where
  apply command world := step world (.block command.new)
  label command := s!"SIGN_BLOCK(key {command.new.key}, slot {command.new.slot}, " ++
    s!"variant {command.new.variant.getD 0})"
  build _ := SignBlock.mk <$> genBlock []

/-- Sign a vote. -/
structure SignVote where
  new : VoteRec

instance : Command SignVote World Unit IO where
  apply command world := step world (.vote command.new)
  label command := s!"SIGN_VOTE(key {command.new.key}, {command.new.source} -> " ++
    s!"{command.new.target}, variant {command.new.variant.getD 0})"
  build _ := SignVote.mk <$> genVote []

/-- Import a file. -/
structure ImportFile where
  blocks : List BlockRec
  votes : List VoteRec
  grouped : Bool

instance : Command ImportFile World Unit IO where
  apply command world := step world (.importFile command.blocks command.votes command.grouped)
  label command := s!"IMPORT({reprStr command.blocks}, {reprStr command.votes}, " ++
    s!"grouped {command.grouped})"
  build _ := do
    let (blocks, votes) ← genFile [] []
    ImportFile.mk blocks votes <$> Gen.bool

/-- Write the record and read it back: it runs only once something is recorded. -/
structure Export where

instance : Command Export World Unit IO where
  check _ world := !world.held.data.isEmpty
  apply _ world := step world .export
  label _ := "EXPORT"
  build _ := pure {}

/-- The same claims, on sequences of commands that no model steers. -/
def madhouse : Property IO :=
  scenario .madhouse () [Command.gen SignBlock, Command.gen SignVote, Command.gen SignVote,
    Command.gen ImportFile, Command.gen Export]

/-! ## The file -/

/-- An integer of the file is decimal digits in a string, below `2 ^ 64`, and nothing else. -/
def numbers : Property IO := pureIO do
  let n ← forAll (Gen.choice [genNatBits 64, (2 ^ 64 + ·) <$> Gen.nat (.linear 0 5)])
  let text ← forAll (Gen.frequency [
    (4, pure (toString n)),
    (1, pure s!"0{n}"), (1, pure s!"+{n}"), (1, pure s!" {n}"), (1, pure s!"{n} "),
    (1, pure s!"-{n}"), (1, pure s!"{n}.0"), (1, pure s!"0x{n}"), (1, pure ""),
    (1, pure s!"{n}e0"), (1, pure "١٢")])
  let expected := if text == toString n && n < 2 ^ 64 then some (UInt64.ofNat n) else none
  (Interchange.readUInt64 "x" (.str text)).toOption === expected
  -- A JSON number is not a string, whatever its value.
  (Interchange.readUInt64 "x" (.num n)).toOption === none

end SlashingProperty

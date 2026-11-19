import Property.Curves.BlsSig
import Property.Curves.Kzg
import EthLib.Cryptography.Secp256k1

/-!
# State machines of the public-key layer

Two machines with transitions as one type (`StateMachine`):

- A point of `G1` as an accumulator, against a scalar mod `r`.
- The nonce generator of RFC 6979, against a replay of its operations by the oracle.

Two scenarios with commands as types (`Command`), run in madhouse mode:

- A set of BLS signers: keys, signatures, aggregates, and changes that must be refused.
- A store of blobs: commitments, proofs, cells, loss and recovery.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.Machines

/-! ## An accumulator in `G1` -/

/-- An operation on the accumulator. -/
inductive Step where
  /-- Add `k G`, as an affine point. -/
  | add (k : Nat)
  /-- Add `k G`, as a Jacobian form with `Z != 1`. -/
  | addJacobian (k : Nat)
  /-- Subtract `k G`. -/
  | sub (k : Nat)
  | double
  | neg
  /-- Multiply by a scalar. -/
  | mul (k : Nat)
  /-- Add the accumulator to itself: the doubling branch of the sum. -/
  | addSelf
  /-- Add the negative of the accumulator: the sum is the point at infinity. -/
  | cancel
  /-- Compress and decompress: the form goes back to `Z = 1`. -/
  | reencode
  deriving Repr, BEq

open Bls12 in
/-- The accumulator is `scalar * G`: the model is arithmetic mod `r`. -/
def accumulator (oracle : Oracle) : StateMachine Nat Step Bls.G1 IO where
  initState := Gen.frequency [(1, pure 0), (1, pure 1), (2, genNear r |>.map (· % r))]
  transitions s :=
    let k := Gen.frequency [(1, pure s), (1, pure ((r - s) % r)), (1, Gen.nat (.linear 0 3)),
      (3, (· % r) <$> genNear r)]
    Gen.frequency [(3, .add <$> k), (3, .addJacobian <$> k), (2, .sub <$> k), (2, pure .double),
      (1, pure .neg), (2, .mul <$> k), (1, pure .addSelf), (1, pure .cancel), (1, pure .reencode)]
  apply s
    | .add k | .addJacobian k => (s + k) % r
    | .sub k => (s + r - k % r) % r
    | .double | .addSelf => 2 * s % r
    | .neg => (r - s) % r
    | .mul k => s * k % r
    | .cancel => 0
    | .reencode => s
  initSut s := pure (Bls.G1.mulNat Bls.G1.generator s)
  applySut acc _ _ t := do
    let g := Bls.G1.generator
    let spread (pt : Bls.G1) : Bls.G1 :=
      Bls.G1.add (Bls.G1.double (Bls.G1.double pt)) (Bls.G1.neg (Bls.G1.add (Bls.G1.double pt) pt))
    match t with
    | .add k => pure (Bls.G1.add acc (Bls.G1.mulNat g k))
    | .addJacobian k => pure (Bls.G1.add acc (spread (Bls.G1.mulNat g k)))
    | .sub k => pure (Bls.G1.add acc (Bls.G1.neg (Bls.G1.mulNat g k)))
    | .double => pure (Bls.G1.double acc)
    | .neg => pure (Bls.G1.neg acc)
    | .mul k => pure (Bls.G1.mulNat acc k)
    | .addSelf => pure (Bls.G1.add acc acc)
    | .cancel => pure (Bls.G1.add acc (Bls.G1.neg acc))
    | .reencode =>
      match Bls.G1.uncompress (Bls.G1.compress acc) with
      | .ok pt => pure pt
      | .error _ => failWith "the accumulator does not decompress"
  invariants acc s := do
    render1 acc === (← oracle.ask ["g1mul", toString s, render1 Bls.G1.generator])
    ensure (Bls.G1.inSubgroup acc) "the accumulator left the subgroup"

/-! ## The nonce generator of RFC 6979 -/

/-- The generator's two operations: take a candidate, or reject the last one. -/
inductive NonceStep where
  | next
  | reject
  deriving Repr, BEq

/-- The key, the hash and the operations so far, newest first. -/
structure NonceModel where
  key : Nat
  hash : Nat
  taken : List NonceStep
  deriving Repr

/-- The candidates of EthLib's generator are those of RFC 6979 section 3.2, step h.

The oracle's generator rejects after every candidate.

So the model allows a `next` only right after a `reject` or at the start.

It allows a `reject` only right after a `next`. -/
def nonces (oracle : Oracle) :
    StateMachine NonceModel NonceStep (Rfc6979.NonceState × List Nat) IO where
  initState := do
    let n := Secp256k1.Fn.modulus
    let (key, hash) ← Gen.zip (genScalar n) (genNear n)
    pure ⟨key, hash, []⟩
  transitions s := pure (if s.taken.head? == some .next then .reject else .next)
  preconditions s t := (s.taken.head? == some .next) == (t == .reject)
  apply s t := { s with taken := t :: s.taken }
  initSut s := pure (Rfc6979.nonceSeed Secp256k1.Fn.modulus s.key (vec32 s.hash), [])
  applySut sut _ _ t :=
    match t with
    | .next =>
      let (candidate, state) := Rfc6979.nonceNext sut.1
      pure (state, sut.2 ++ [candidate])
    | .reject => pure (Rfc6979.nonceReject sut.1, sut.2)
  invariants sut s := do
    let ops := String.ofList (s.taken.reverse.map fun
      | .next => 'n'
      | .reject => 'r')
    if !sut.2.isEmpty then
      " ".intercalate (sut.2.map toString) === (← oracle.ask ["nonces", "k1", toString s.key,
        hexVec (vec32 s.hash), ops])

/-! ## A set of BLS signers -/

/-- What the scenario knows: the secret keys registered, and the signatures made. -/
structure Signers where
  keys : Array Nat := #[]
  /-- A signature with the index of its key and its message. -/
  made : Array (Nat × ByteArray × ByteArray) := #[]
  deriving Inhabited

open Bls12 Bls.Signatures

def bit (b : Bool) : String := if b then "1" else "0"

/-- Register a key: its public key is the oracle's, and its proof of possession verifies. -/
structure Register where
  oracle : Oracle
  key : Nat

/-- Register a key and check it against the oracle. -/
def register (oracle : Oracle) (key : Nat) (s : Signers) : TestT IO Signers := do
  let some sk := secret key | failWith "no key"
  let pk := skToPk sk
  hexVec pk === (← oracle.ask ["sktopk", toString key])
  match popProve sk with
  | .ok proof => ensure (popVerify pk proof) "an honest proof of possession is refused"
  | .error _ => failWith "no proof of possession"
  pure { s with keys := s.keys.push key }

instance : Command Register Signers Oracle IO where
  check _ c s := !s.keys.contains c.key && s.keys.size < 5
  apply _ c s := register c.oracle c.key s
  label c := s!"REGISTER({c.key})"
  build oracle := Register.mk oracle <$>
    Gen.frequency [(1, Gen.nat (.constant 1 3)), (2, genScalar r)]

/-- Register the opposite of a registered key, so that the two public keys sum to infinity. -/
structure RegisterOpposite where
  oracle : Oracle
  pick : Nat

instance : Command RegisterOpposite Signers Oracle IO where
  check _ c s := !s.keys.isEmpty && s.keys.size < 5 &&
    !s.keys.contains (r - s.keys[c.pick % s.keys.size]!)
  apply _ c s := register c.oracle (r - s.keys[c.pick % s.keys.size]!) s
  label c := s!"REGISTER_OPPOSITE({c.pick})"
  build oracle := RegisterOpposite.mk oracle <$> Gen.nat (.constant 0 4)

/-- A registered key signs a message: the signature is the oracle's and verifies. -/
structure Sign where
  oracle : Oracle
  pick : Nat
  msg : ByteArray

instance : Command Sign Signers Oracle IO where
  check _ _ s := !s.keys.isEmpty && s.made.size < 6
  apply _ c s := do
    let index := c.pick % s.keys.size
    let key := s.keys[index]!
    let sig := sigOf key c.msg
    hex sig === (← c.oracle.ask ["blssign", toString key, hex c.msg])
    ensure (verify (vec 48 (pkOf key)) c.msg (vec 96 sig)) "an honest signature is refused"
    pure { s with made := s.made.push (index, c.msg, sig) }
  label c := s!"SIGN({c.pick}, {hex c.msg})"
  build oracle := Gen.zipWith (Sign.mk oracle) (Gen.nat (.constant 0 4))
    (Gen.frequency [(1, pure ByteArray.empty), (1, pure (beBytes 1 7)), (2, genBytes
        (.linear 0 12))])

/-- A signature made earlier, with one bit of the key, message or signature changed.

The other choice is the same signature under another registered key.

Either must be refused, as the oracle refuses it, and nothing changes. -/
structure Tamper where
  oracle : Oracle
  pick : Nat
  field : Nat
  place : Nat

instance : Command Tamper Signers Oracle IO where
  check _ _ s := !s.made.isEmpty
  apply _ c s := do
    let (index, msg, sig) := s.made[c.pick % s.made.size]!
    let pk := pkOf s.keys[index]!
    let other := pkOf s.keys[(index + 1) % s.keys.size]!
    let (pk, msg, sig) := match c.field % 4 with
      | 0 => (flipBit pk c.place, msg, sig)
      | 1 => (pk, flipBit (msg ++ beBytes 1 0) c.place, sig)
      | 2 => (pk, msg, flipBit sig c.place)
      | _ => (other, msg, sig)
    let got := verify (vec 48 pk) msg (vec 96 sig)
    bit got === (← c.oracle.ask ["blsverify", hex pk, hex msg, hex sig])
    ensure (!got || (c.field % 4 == 3 && s.keys.size == 1)) "a changed signature is accepted"
    pure s
  label c := s!"TAMPER({c.pick}, {c.field}, {c.place})"
  build oracle := do
    let (pick, field, place) ← Gen.zip (Gen.nat (.constant 0 5))
      (Gen.zip (Gen.nat (.constant 0 3)) (Gen.nat (.constant 0 767)))
    pure ⟨oracle, pick, field, place⟩

/-- Every registered key signs one message.

The aggregate verifies exactly when the oracle says so.

The oracle says so unless the public keys sum to infinity.

The aggregate never verifies without its last signer. -/
structure AggregateSame where
  oracle : Oracle
  msg : ByteArray

instance : Command AggregateSame Signers Oracle IO where
  check _ _ s := !s.keys.isEmpty
  apply _ c s := do
    let keys := s.keys.toList
    let pks := keys.map pkOf
    let sig := aggregateOf keys (keys.map fun _ => c.msg)
    let words := [listWord (pks.map hex), hex c.msg, hex sig]
    let got := fastAggregateVerify (pks.map (vec 48)).toArray c.msg (vec 96 sig)
    bit got === (← c.oracle.ask ("fastaggverify" :: words))
    bit (ethFastAggregateVerify (pks.map (vec 48)).toArray c.msg (vec 96 sig)) ===
      (← c.oracle.ask ("ethfastaggverify" :: words))
    -- The model: the keys are known, so their sum mod `r` says whether the key is infinity.
    got === (keys.foldl (· + ·) 0 % r != 0)
    let fewer := (pks.dropLast.map (vec 48)).toArray
    if !fewer.isEmpty then
      ensure (!fastAggregateVerify fewer c.msg
          (vec 96 sig)) "an aggregate verifies without a signer"
    let sum := match ethAggregatePubkeys (pks.map (vec 48)).toArray with
      | .ok pk => hexVec pk
      | .error _ => "error"
    sum === (← c.oracle.ask ["ethaggpk", listWord (pks.map hex)])
    pure s
  label c := s!"AGGREGATE_SAME({hex c.msg})"
  build oracle := AggregateSame.mk oracle <$> genBytes (.linear 0 8)

/-- The signatures made so far aggregate, and the aggregate verifies on their messages. -/
structure AggregateMade where
  oracle : Oracle

instance : Command AggregateMade Signers Oracle IO where
  check _ _ s := !s.made.isEmpty
  apply _ c s := do
    let made := s.made.toList
    let pks := made.map fun (index, _, _) => pkOf s.keys[index]!
    let msgs := made.map (·.2.1)
    let sig := match aggregate (made.map fun (_, _, sig) => vec 96 sig).toArray with
      | .ok sig => ByteArray.mk sig.toArray
      | .error _ => ByteArray.empty
    hex sig === (← c.oracle.ask ["aggregate", listWord (made.map fun (_, _, sig) => hex sig)])
    let got := aggregateVerify (pks.map (vec 48)).toArray msgs.toArray (vec 96 sig)
    bit got === (← c.oracle.ask ["aggverify", listWord (pks.map hex), listWord (msgs.map hex),
      hex sig])
    ensure got "an honest aggregate is refused"
    pure s
  label _ := "AGGREGATE_MADE"
  build oracle := pure ⟨oracle⟩

/-- No signer at all: Ethereum accepts the signature of infinity, the draft accepts nothing. -/
structure EmptySet where
  msg : ByteArray

instance : Command EmptySet Signers Oracle IO where
  apply _ c s := do
    ensure (ethFastAggregateVerify #[] c.msg G2_POINT_AT_INFINITY) "the empty set is refused"
    ensure (!fastAggregateVerify #[] c.msg G2_POINT_AT_INFINITY) "the draft takes an empty set"
    ensure (!aggregateVerify #[] #[] G2_POINT_AT_INFINITY) "an empty aggregate verifies"
    for (_, _, sig) in s.made do
      ensure (!ethFastAggregateVerify #[] c.msg (vec 96 sig)) "the empty set signs"
    pure s
  label c := s!"EMPTY_SET({hex c.msg})"
  build _ := EmptySet.mk <$> genBytes (.linear 0 4)

/-- The signers, in random order: no command is special, and each must hold in every state. -/
def signers (oracle : Oracle) (mode : Mode) : Property IO :=
  scenario mode oracle [
    Command.gen Register, Command.gen Sign, Command.gen RegisterOpposite, Command.gen Tamper,
    Command.gen AggregateSame, Command.gen AggregateMade, Command.gen EmptySet,
    Command.gen Sign, Command.gen Tamper]

/-! ## A store of blobs -/

open Kzg KzgTest

/-- A blob with what a node keeps of it. -/
structure Stored where
  spec : BlobSpec
  commitment : Vector UInt8 48
  proof : Vector UInt8 48
  cells : Array Cell
  proofs : Array (Vector UInt8 48)
  deriving Inhabited

/-- The blobs stored so far. -/
structure Store where
  blobs : Array Stored := #[]
  deriving Inhabited

/-- What every command of the store reads. -/
structure Env where
  oracle : Oracle
  setup : TrustedSetup

/-- Store a blob: its commitment, proof and cells are c-kzg's. -/
structure AddBlob where
  env : Env
  spec : BlobSpec

instance : Command AddBlob Store Env IO where
  check _ _ s := s.blobs.size < 3
  apply _ c s := do
    let blob := c.spec.blob
    let .ok commitment := blobToKzgCommitment c.env.setup blob | failWith "no commitment"
    let .ok proof := computeBlobKzgProof c.env.setup blob commitment | failWith "no proof"
    let .ok (cells, proofs) := computeCellsAndKzgProofs c.env.setup blob | failWith "no cells"
    hexVec commitment === (← c.env.oracle.ask ["kzgcommit", blobHex c.spec])
    hexVec proof === (← c.env.oracle.ask ["kzgblobproof", blobHex c.spec, hexVec commitment])
    s!"{digest cells} {digest proofs}" === (← c.env.oracle.ask ["kzgcells", blobHex c.spec])
    pure { s with blobs := s.blobs.push ⟨c.spec, commitment, proof, cells, proofs⟩ }
  label c := s!"ADD_BLOB({repr c.spec})"
  build env := AddBlob.mk env <$> genBlob false

/-- Every stored blob verifies in one batch.

With two proofs exchanged the batch verifies exactly when the two are equal. -/
structure VerifyAll where
  env : Env
  swap : Bool

instance : Command VerifyAll Store Env IO where
  apply _ c s := do
    let blobs := s.blobs.map (·.spec.blob)
    let commitments := s.blobs.map (·.commitment)
    let proofs := s.blobs.map (·.proof)
    let proofs := if c.swap && proofs.size ≥ 2 then
      (proofs.set! 0 proofs[1]!).set! 1 proofs[0]! else proofs
    let honest := !(c.swap && proofs.size ≥ 2) || proofs[0]! == proofs[1]!
    let got := verifyBlobKzgProofBatch c.env.setup blobs commitments proofs
    verdict got === (← c.env.oracle.ask ["kzgverifybatch", listWord (blobs.toList.map hexVec),
      listWord (commitments.toList.map hexVec), listWord (proofs.toList.map hexVec)])
    -- Two equal proofs of different blobs can only be those of two constant blobs.
    if honest then verdict got === "1"
    pure s
  label c := s!"VERIFY_ALL({c.swap})"
  build env := VerifyAll.mk env <$> Gen.bool

/-- A sample of cells across the stored blobs verifies.

With one cell index moved the sample verifies only as c-kzg says. -/
structure Sample where
  env : Env
  picks : List (Nat × Nat)
  move : Bool

instance : Command Sample Store Env IO where
  check _ _ s := !s.blobs.isEmpty
  apply _ c s := do
    let rows := c.picks.map fun (b, i) =>
      let stored := s.blobs[b % s.blobs.size]!
      (stored.commitment, i, stored.cells[i]!, stored.proofs[i]!)
    let indices := rows.map (·.2.1)
    let indices := match c.move, indices with
      | true, i :: rest => (i + 1) % 128 :: rest
      | _, is => is
    let got := verifyCellKzgProofBatch c.env.setup (rows.map (·.1)).toArray indices.toArray
      (rows.map (·.2.2.1)).toArray (rows.map (·.2.2.2)).toArray
    verdict got === (← c.env.oracle.ask ["kzgverifycells",
      listWord (rows.map fun row => hexVec row.1), listWord (indices.map toString),
      listWord (rows.map fun row => hexVec row.2.2.1),
      listWord (rows.map fun row => hexVec row.2.2.2)])
    if !c.move || rows.isEmpty then verdict got === "1"
    pure s
  label c := s!"SAMPLE({c.picks}, {c.move})"
  build env := do
    let picks ← Gen.list (.linear 0 6) (Gen.zip (Gen.nat (.constant 0 2)) (Gen.nat
        (.constant 0 127)))
    Sample.mk env picks <$> Gen.bool

/-- Lose up to half of the cells of a blob: recovery gives back the cells and proofs stored.

With one cell more lost, recovery fails. -/
structure LoseAndRecover where
  env : Env
  pick : Nat
  kept : List Nat

instance : Command LoseAndRecover Store Env IO where
  check _ _ s := !s.blobs.isEmpty
  apply _ c s := do
    let stored := s.blobs[c.pick % s.blobs.size]!
    let cells := c.kept.map fun i => stored.cells[i]!
    match recoverCellsAndKzgProofs c.env.setup c.kept.toArray cells.toArray with
    | .ok (all, proofs) =>
      ensure (c.kept.length ≥ 64) "recovery from fewer than half of the cells"
      ensure (all == stored.cells && proofs == stored.proofs) "recovery gives other cells"
    | .error _ => ensure (c.kept.length < 64) "recovery from half of the cells fails"
    pure s
  label c := s!"LOSE_AND_RECOVER({c.pick}, {c.kept})"
  build env := do
    let kept ← Gen.frequency [
      (3, Gen.filter (·.length ≥ 64) (Gen.subsequence (List.range 128))),
      (1, (fun k => (List.range 128).drop k |>.take 64) <$> Gen.nat (.constant 0 64)),
      (1, (fun k => (List.range 128).drop k |>.take 63) <$> Gen.nat (.constant 0 65))]
    (LoseAndRecover.mk env · kept) <$> Gen.nat (.constant 0 2)

/-- Open a stored blob at a point: the proof verifies for its value and for no other. -/
structure OpenPoint where
  env : Env
  pick : Nat
  z : Nat

instance : Command OpenPoint Store Env IO where
  check _ _ s := !s.blobs.isEmpty
  apply _ c s := do
    let stored := s.blobs[c.pick % s.blobs.size]!
    let z := vec32 (c.z % KzgTest.r)
    let .ok (proof, y) := computeKzgProof c.env.setup stored.spec.blob z | failWith "no proof"
    s!"{hexVec proof} {hexVec y}" === (← c.env.oracle.ask ["kzgproof", blobHex stored.spec,
      hexVec z])
    verdict (verifyKzgProof c.env.setup stored.commitment z y proof) === "1"
    let other := vec32 ((beNat ⟨y.toArray⟩ + 1) % KzgTest.r)
    verdict (verifyKzgProof c.env.setup stored.commitment z other proof) === "0"
    pure s
  label c := s!"OPEN_POINT({c.pick}, {c.z})"
  build env := Gen.zipWith (OpenPoint.mk env) (Gen.nat (.constant 0 2)) genZ

/-- The store, in random order. -/
def store (env : Env) (mode : Mode) : Property IO :=
  scenario mode env [
    Command.gen AddBlob, Command.gen VerifyAll, Command.gen Sample, Command.gen LoseAndRecover,
    Command.gen OpenPoint, Command.gen AddBlob]

end CurvesProperty.Machines

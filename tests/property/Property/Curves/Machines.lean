import Property.Curves.BlsSig
import Property.Curves.Kzg
import EthLib.Cryptography.Secp256k1
import EthLib.Cryptography.Secp256r1

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
  applySut acc before _ t := do
    let g := Bls.G1.generator
    classify "a step from the point at infinity" (before == 0)
    let other (k : Nat) (name : String) : TestT IO Unit := do
      classify s!"{name}: the accumulator itself, a doubling" (k % r == before && before != 0)
      classify s!"{name}: its opposite, the point at infinity" ((k + before) % r == 0 &&
        before != 0)
      classify s!"{name}: the point at infinity" (k % r == 0)
      classify s!"{name}: another point" (k % r != before && (k + before) % r != 0 &&
        k % r != 0 && before != 0)
    match t with
    | .add k => other k "add"
    | .addJacobian k => other k "add a Jacobian form"
    | .sub k => other (r - k % r) "subtract"
    | .double => label "double"
    | .neg => label "negate"
    | .mul k =>
      classify "multiply by zero" (k == 0)
      classify "multiply by one" (k == 1)
      classify "multiply by another scalar" (k > 1)
    | .addSelf => label "add to itself"
    | .cancel => label "add its negative"
    | .reencode => label "compress and decompress"
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

/-- The order, the key, the hash and the operations so far, newest first. -/
structure NonceModel where
  order : Nat
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
    -- The generator takes any order of 256 bits: those of the two curves, and any other.
    let n ← Gen.frequency [(2, pure Secp256k1.Fn.modulus), (2, pure Secp256r1.Fn.modulus),
      (1, Gen.element [2 ^ 255, 2 ^ 255 + 1, 2 ^ 256 - 1]),
      (3, Gen.nat (.constant (2 ^ 255) (2 ^ 256 - 1)))]
    let (key, hash) ← Gen.zip (genScalar n) (genNear n)
    pure ⟨n, key, hash, []⟩
  transitions s := pure (if s.taken.head? == some .next then .reject else .next)
  preconditions s t := (s.taken.head? == some .next) == (t == .reject)
  apply s t := { s with taken := t :: s.taken }
  initSut s := pure (Rfc6979.nonceSeed s.order s.key (vec32 s.hash), [])
  applySut sut before _ t := do
    match t with
    | .next =>
      let (candidate, state) := Rfc6979.nonceNext sut.1
      classify "a second candidate or a later one, after a rejection" (!sut.2.isEmpty)
      classify "ten candidates or more" (sut.2.length ≥ 9)
      classify "a candidate of the order or more, which a signer rejects" (candidate ≥ before.order)
      classify "the hash is the order or more, so it is reduced" (before.hash ≥ before.order)
      classify "the order of secp256k1" (before.order == Secp256k1.Fn.modulus)
      classify "the order of P-256" (before.order == Secp256r1.Fn.modulus)
      classify "another order of 256 bits" (before.order != Secp256k1.Fn.modulus &&
        before.order != Secp256r1.Fn.modulus)
      pure (state, sut.2 ++ [candidate])
    | .reject => pure (Rfc6979.nonceReject sut.1, sut.2)
  invariants sut s := do
    let ops := String.ofList (s.taken.reverse.map fun
      | .next => 'n'
      | .reject => 'r')
    if !sut.2.isEmpty then
      " ".intercalate (sut.2.map toString) === (← oracle.ask ["nonces", toString s.order,
        toString s.key,
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
  key : Nat

/-- Register a key and check it against the oracle. -/
def register (oracle : Oracle) (key : Nat) (s : Signers) : TestT IO Signers := do
  let some sk := secret key | failWith "no key"
  let pk := skToPk sk
  hexVec pk === (← oracle.ask ["sktopk", toString key])
  match popProve sk with
  | .ok proof => ensure (popVerify pk proof) "an honest proof of possession is refused"
  | .error _ => failWith "no proof of possession"
  classify "a second key or a later one is registered" (!s.keys.isEmpty)
  pure { s with keys := s.keys.push key }

instance : Command Register Signers Oracle IO where
  check _ c s := !s.keys.contains c.key && s.keys.size < 5
  apply oracle c s := register oracle c.key s
  label c := s!"REGISTER({c.key})"
  build _ := Register.mk <$>
    Gen.frequency [(1, Gen.nat (.constant 1 3)), (2, genScalar r)]
  -- The keys after the command, so that the commands after it are built for them.
  next _ c s := if !s.keys.contains c.key && s.keys.size < 5
    then { s with keys := s.keys.push c.key } else s

/-- Register the opposite of a registered key, so that the two public keys sum to infinity. -/
structure RegisterOpposite where
  pick : Nat

instance : Command RegisterOpposite Signers Oracle IO where
  check _ c s := !s.keys.isEmpty && s.keys.size < 5 &&
    !s.keys.contains (r - s.keys[c.pick % s.keys.size]!)
  apply oracle c s := do
    label "the opposite of a key is registered"
    register oracle (r - s.keys[c.pick % s.keys.size]!) s
  label c := s!"REGISTER_OPPOSITE({c.pick})"
  build _ := RegisterOpposite.mk <$> Gen.nat (.constant 0 4)
  next _ c s :=
    if !s.keys.isEmpty && s.keys.size < 5 && !s.keys.contains (r - s.keys[c.pick % s.keys.size]!)
    then { s with keys := s.keys.push (r - s.keys[c.pick % s.keys.size]!) } else s
  -- One of the keys registered by then.
  buildIn _ s := RegisterOpposite.mk <$> Gen.nat (.constant 0 (s.keys.size - 1))

/-- A registered key signs a message: the signature is the oracle's and verifies. -/
structure Sign where
  pick : Nat
  msg : ByteArray

instance : Command Sign Signers Oracle IO where
  check _ _ s := !s.keys.isEmpty && s.made.size < 6
  apply oracle c s := do
    let index := c.pick % s.keys.size
    let key := s.keys[index]!
    let sig := sigOf key c.msg
    hex sig === (← oracle.ask ["blssign", toString key, hex c.msg])
    ensure (verify (vec 48 (pkOf key)) c.msg (vec 96 sig)) "an honest signature is refused"
    label "a signature is made"
    classify "a message is signed a second time" (s.made.any fun (_, msg, _) => msg == c.msg)
    pure { s with made := s.made.push (index, c.msg, sig) }
  label c := s!"SIGN({c.pick}, {hex c.msg})"
  build _ := Gen.zipWith Sign.mk (Gen.nat (.constant 0 4))
    (Gen.frequency [(1, pure ByteArray.empty), (1, pure (beBytes 1 7)), (2, genBytes
        (.linear 0 12))])
  -- The signature itself is made in `apply`: here only the count and the message matter.
  next _ c s := if !s.keys.isEmpty && s.made.size < 6
    then { s with made := s.made.push (c.pick % s.keys.size, c.msg, ByteArray.empty) } else s
  -- A key registered by then, and often a message that was signed before.
  buildIn _ s := Gen.zipWith Sign.mk (Gen.nat (.constant 0 (s.keys.size - 1)))
    (Gen.frequency ([(1, pure ByteArray.empty), (1, pure (beBytes 1 7)),
      (2, genBytes (.linear 0 12))] ++
      (if s.made.isEmpty then [] else [(2, Gen.element (s.made.toList.map (·.2.1)))])))

/-- A signature made earlier, with one bit of the key, message or signature changed.

The other choice is the same signature under another registered key.

Either must be refused, as the oracle refuses it, and nothing changes. -/
structure Tamper where
  pick : Nat
  field : Nat
  place : Nat

instance : Command Tamper Signers Oracle IO where
  check _ _ s := !s.made.isEmpty
  apply oracle c s := do
    let (index, msg, sig) := s.made[c.pick % s.made.size]!
    let pk := pkOf s.keys[index]!
    let other := pkOf s.keys[(index + 1) % s.keys.size]!
    let (pk, msg, sig) := match c.field % 4 with
      | 0 => (flipBit pk c.place, msg, sig)
      | 1 => (pk, flipBit (msg ++ beBytes 1 0) c.place, sig)
      | 2 => (pk, msg, flipBit sig c.place)
      | _ => (other, msg, sig)
    let got := verify (vec 48 pk) msg (vec 96 sig)
    bit got === (← oracle.ask ["blsverify", hex pk, hex msg, hex sig])
    ensure (!got || (c.field % 4 == 3 && s.keys.size == 1)) "a changed signature is accepted"
    label (match c.field % 4 with
      | 0 => "tampered: a bit of the key"
      | 1 => "tampered: a bit of the message"
      | 2 => "tampered: a bit of the signature"
      | _ => if s.keys.size == 1 then "tampered: the same key, accepted"
        else "tampered: another registered key")
    if !got then label s!"tamper refused: {coreRefusal pk sig}"
    pure s
  label c := s!"TAMPER({c.pick}, {c.field}, {c.place})"
  build _ := do
    let (pick, field, place) ← Gen.zip (Gen.nat (.constant 0 5))
      (Gen.zip (Gen.nat (.constant 0 3)) (Gen.nat (.constant 0 767)))
    pure ⟨pick, field, place⟩
  -- A signature made by then.
  buildIn _ s := do
    let (pick, field, place) ← Gen.zip (Gen.nat (.constant 0 (s.made.size - 1)))
      (Gen.zip (Gen.nat (.constant 0 3)) (Gen.nat (.constant 0 767)))
    pure ⟨pick, field, place⟩

/-- Every registered key signs one message.

The aggregate verifies exactly when the oracle says so.

The oracle says so unless the public keys sum to infinity.

The aggregate never verifies without its last signer. -/
structure AggregateSame where
  msg : ByteArray

instance : Command AggregateSame Signers Oracle IO where
  check _ _ s := !s.keys.isEmpty
  apply oracle c s := do
    let keys := s.keys.toList
    let pks := keys.map pkOf
    let sig := aggregateOf keys (keys.map fun _ => c.msg)
    let words := [listWord (pks.map hex), hex c.msg, hex sig]
    let got := fastAggregateVerify (pks.map (vec 48)).toArray c.msg (vec 96 sig)
    classify "one message: the aggregate of one key verifies" (got && keys.length == 1)
    classify "one message: the aggregate of several keys verifies" (got && keys.length > 1)
    classify "one message: the keys sum to infinity, refused" (!got)
    bit got === (← oracle.ask ("fastaggverify" :: words))
    bit (ethFastAggregateVerify (pks.map (vec 48)).toArray c.msg (vec 96 sig)) ===
      (← oracle.ask ("ethfastaggverify" :: words))
    -- The model: the keys are known, so their sum mod `r` says whether the key is infinity.
    got === (keys.foldl (· + ·) 0 % r != 0)
    let fewer := (pks.dropLast.map (vec 48)).toArray
    if !fewer.isEmpty then
      ensure (!fastAggregateVerify fewer c.msg
          (vec 96 sig)) "an aggregate verifies without a signer"
    let sum := match ethAggregatePubkeys (pks.map (vec 48)).toArray with
      | .ok pk => hexVec pk
      | .error _ => "error"
    sum === (← oracle.ask ["ethaggpk", listWord (pks.map hex)])
    pure s
  label c := s!"AGGREGATE_SAME({hex c.msg})"
  build _ := AggregateSame.mk <$> genBytes (.linear 0 8)

/-- The signatures made so far aggregate, and the aggregate verifies on their messages. -/
structure AggregateMade where

instance : Command AggregateMade Signers Oracle IO where
  check _ _ s := !s.made.isEmpty
  apply oracle _ s := do
    let made := s.made.toList
    let pks := made.map fun (index, _, _) => pkOf s.keys[index]!
    let msgs := made.map (·.2.1)
    let sig := match aggregate (made.map fun (_, _, sig) => vec 96 sig).toArray with
      | .ok sig => ByteArray.mk sig.toArray
      | .error _ => ByteArray.empty
    hex sig === (← oracle.ask ["aggregate", listWord (made.map fun (_, _, sig) => hex sig)])
    let got := aggregateVerify (pks.map (vec 48)).toArray msgs.toArray (vec 96 sig)
    bit got === (← oracle.ask ["aggverify", listWord (pks.map hex), listWord (msgs.map hex),
      hex sig])
    ensure got "an honest aggregate is refused"
    classify "several messages: an aggregate of one signature" (made.length == 1)
    classify "several messages: an aggregate of two or more" (made.length > 1)
    classify "several messages: one message twice" ((msgs.map hex).eraseDups.length <
      msgs.length)
    classify "several messages: one key twice" ((pks.map hex).eraseDups.length < pks.length)
    pure s
  label _ := "AGGREGATE_MADE"
  build _ := pure {}

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
    label "the empty set"
    classify "the empty set against signatures made" (!s.made.isEmpty)
    pure s
  label c := s!"EMPTY_SET({hex c.msg})"
  build _ := EmptySet.mk <$> genBytes (.linear 0 4)

/-- The signers, in random order: no command is special, and each must hold in every state. -/
def signers (oracle : Oracle) (mode : Mode) : Property IO :=
  -- A sequence has 8 to 20 commands at every size.
  --
  -- A short one registers no key, and then every other command is skipped.
  scenario mode oracle [
    Command.gen Register, Command.gen Sign, Command.gen RegisterOpposite, Command.gen Tamper,
    Command.gen AggregateSame, Command.gen AggregateMade, Command.gen EmptySet,
    Command.gen Sign, Command.gen Tamper, Command.gen Register, Command.gen AggregateSame,
    Command.gen AggregateMade] (.constant 8 20)

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
  spec : BlobSpec

instance : Command AddBlob Store Env IO where
  check _ _ s := s.blobs.size < 3
  apply env c s := do
    let blob := c.spec.blob
    let .ok commitment := blobToKzgCommitment env.setup blob | failWith "no commitment"
    let .ok proof := computeBlobKzgProof env.setup blob commitment | failWith "no proof"
    let .ok (cells, proofs) := computeCellsAndKzgProofs env.setup blob | failWith "no cells"
    hexVec commitment === (← env.oracle.ask ["kzgcommit", blobHex c.spec])
    hexVec proof === (← env.oracle.ask ["kzgblobproof", blobHex c.spec, hexVec commitment])
    s!"{digest cells} {digest proofs}" === (← env.oracle.ask ["kzgcells", blobHex c.spec])
    label "a blob is stored"
    classify "a second blob or a third is stored" (!s.blobs.isEmpty)
    classify "a blob is stored twice" (s.blobs.any (·.commitment == commitment))
    classify "a constant blob is stored, whose proof is the point at infinity"
      (proof == Bls.G1.infinityBytes)
    pure { s with blobs := s.blobs.push ⟨c.spec, commitment, proof, cells, proofs⟩ }
  label c := s!"ADD_BLOB({repr c.spec})"
  build _ := AddBlob.mk <$> genBlob false
  -- Only the count matters to the commands built after this one.
  next _ c s := if s.blobs.size < 3
    then { s with blobs := s.blobs.push { (default : Stored) with spec := c.spec } } else s
  -- A blob stored before comes again now and then: one commitment twice in a batch.
  buildIn _ s := AddBlob.mk <$> Gen.frequency ([(5, genBlob false)] ++
    (if s.blobs.isEmpty then [] else [(1, Gen.element (s.blobs.toList.map (·.spec)))]))

/-- Every stored blob verifies in one batch.

With two proofs exchanged the batch verifies exactly when the two are equal. -/
structure VerifyAll where
  swap : Bool

instance : Command VerifyAll Store Env IO where
  apply env c s := do
    let blobs := s.blobs.map (·.spec.blob)
    let commitments := s.blobs.map (·.commitment)
    let proofs := s.blobs.map (·.proof)
    let proofs := if c.swap && proofs.size ≥ 2 then
      (proofs.set! 0 proofs[1]!).set! 1 proofs[0]! else proofs
    let honest := !(c.swap && proofs.size ≥ 2) || proofs[0]! == proofs[1]!
    let got := verifyBlobKzgProofBatch env.setup blobs commitments proofs
    verdict got === (← env.oracle.ask ["kzgverifybatch", listWord (blobs.toList.map hexVec),
      listWord (commitments.toList.map hexVec), listWord (proofs.toList.map hexVec)])
    -- Two equal proofs of different blobs can only be those of two constant blobs.
    if honest then verdict got === "1"
    classify "batch: no blob" blobs.isEmpty
    classify "batch: one blob verifies" (blobs.size == 1)
    classify "batch: two or three blobs verify" (blobs.size ≥ 2 && got.toOption == some true)
    classify "batch: two proofs exchanged, refused" (got.toOption == some false)
    pure s
  label c := s!"VERIFY_ALL({c.swap})"
  build _ := VerifyAll.mk <$> Gen.bool

/-- A sample of cells across the stored blobs verifies.

With one cell index moved the sample verifies only as c-kzg says. -/
structure Sample where
  picks : List (Nat × Nat)
  move : Bool

instance : Command Sample Store Env IO where
  check _ _ s := !s.blobs.isEmpty
  apply env c s := do
    let rows := c.picks.map fun (b, i) =>
      let stored := s.blobs[b % s.blobs.size]!
      (stored.commitment, i, stored.cells[i]!, stored.proofs[i]!)
    let indices := rows.map (·.2.1)
    let indices := match c.move, indices with
      | true, i :: rest => (i + 1) % 128 :: rest
      | _, is => is
    let got := verifyCellKzgProofBatch env.setup (rows.map (·.1)).toArray indices.toArray
      (rows.map (·.2.2.1)).toArray (rows.map (·.2.2.2)).toArray
    classify "sample: no cell" rows.isEmpty
    classify "sample: cells verify" (!rows.isEmpty && got.toOption == some true)
    classify "sample: cells of two or three blobs verify" (got.toOption == some true &&
      (rows.map fun row => hexVec row.1).eraseDups.length > 1)
    classify "sample: a moved index, refused" (got.toOption == some false)
    verdict got === (← env.oracle.ask ["kzgverifycells",
      listWord (rows.map fun row => hexVec row.1), listWord (indices.map toString),
      listWord (rows.map fun row => hexVec row.2.2.1),
      listWord (rows.map fun row => hexVec row.2.2.2)])
    if !c.move || rows.isEmpty then verdict got === "1"
    pure s
  label c := s!"SAMPLE({c.picks}, {c.move})"
  build _ := do
    let picks ← Gen.list (.linear 0 6) (Gen.zip (Gen.nat (.constant 0 2)) (Gen.nat
        (.constant 0 127)))
    Sample.mk picks <$> Gen.bool
  -- Cells of the blobs stored by then, a few of them, at any index and at the two ends.
  buildIn _ s := do
    let cell := Gen.frequency [(1, pure 0), (1, pure 127), (4, Gen.nat (.constant 0 127))]
    let picks ← Gen.frequency [(1, pure []), (6, Gen.list (.constant 1 6)
      (Gen.zip (Gen.nat (.constant 0 (s.blobs.size - 1))) cell))]
    Sample.mk picks <$> Gen.bool

/-- Lose up to half of the cells of a blob: recovery gives back the cells and proofs stored.

With one cell more lost, recovery fails. -/
structure LoseAndRecover where
  pick : Nat
  kept : List Nat

instance : Command LoseAndRecover Store Env IO where
  check _ _ s := !s.blobs.isEmpty
  apply env c s := do
    let stored := s.blobs[c.pick % s.blobs.size]!
    let cells := c.kept.map fun i => stored.cells[i]!
    match recoverCellsAndKzgProofs env.setup c.kept.toArray cells.toArray with
    | .ok (all, proofs) =>
      ensure (c.kept.length ≥ 64) "recovery from fewer than half of the cells"
      ensure (all == stored.cells && proofs == stored.proofs) "recovery gives other cells"
      classify "recovered from exactly 64 cells" (c.kept.length == 64)
      classify "recovered from more than 64 cells" (c.kept.length > 64)
    | .error _ =>
      ensure (c.kept.length < 64) "recovery from half of the cells fails"
      label "recovery refused: 63 cells"
    pure s
  label c := s!"LOSE_AND_RECOVER({c.pick}, {c.kept})"
  build _ := do
    let kept ← Gen.frequency [
      (3, Gen.filter (·.length ≥ 64) (Gen.subsequence (List.range 128))),
      (1, (fun k => (List.range 128).drop k |>.take 64) <$> Gen.nat (.constant 0 64)),
      (1, (fun k => (List.range 128).drop k |>.take 63) <$> Gen.nat (.constant 0 65))]
    (LoseAndRecover.mk · kept) <$> Gen.nat (.constant 0 2)

/-- Open a stored blob at a point: the proof verifies for its value and for no other. -/
structure OpenPoint where
  pick : Nat
  z : Nat

instance : Command OpenPoint Store Env IO where
  check _ _ s := !s.blobs.isEmpty
  apply env c s := do
    let stored := s.blobs[c.pick % s.blobs.size]!
    let z := vec32 (c.z % KzgTest.r)
    let .ok (proof, y) := computeKzgProof env.setup stored.spec.blob z | failWith "no proof"
    s!"{hexVec proof} {hexVec y}" === (← env.oracle.ask ["kzgproof", blobHex stored.spec,
      hexVec z])
    verdict (verifyKzgProof env.setup stored.commitment z y proof) === "1"
    let other := vec32 ((beNat ⟨y.toArray⟩ + 1) % KzgTest.r)
    verdict (verifyKzgProof env.setup stored.commitment z other proof) === "0"
    classify "opened at a root of unity of the domain" (modPow KzgTest.r c.z 4096 == 1)
    classify "opened outside the domain" (modPow KzgTest.r c.z 4096 != 1)
    pure s
  label c := s!"OPEN_POINT({c.pick}, {c.z})"
  build _ := Gen.zipWith OpenPoint.mk (Gen.nat (.constant 0 2)) genZ

/-- The store, in random order. -/
def store (env : Env) (mode : Mode) : Property IO :=
  -- A sequence of 5 to 10 commands at every size, with a blob stored in one command of three.
  scenario mode env [
    Command.gen AddBlob, Command.gen VerifyAll, Command.gen Sample, Command.gen LoseAndRecover,
    Command.gen OpenPoint, Command.gen AddBlob, Command.gen AddBlob, Command.gen VerifyAll,
    Command.gen Sample] (.constant 5 10)

end CurvesProperty.Machines

import Property.Curves.Bls

/-!
# BLS signatures, key generation and key paths

The scheme is the proof of possession of the BLS signature draft, version 4, section 3.3.

The references are py_ecc and milagro, and a model of ERC-2333 written from its text.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.Bls12

open Bls Bls.Signatures

/-- The secret key of a number in `[1, r - 1]`. -/
def secret (k : Nat) : Option SecretKey :=
  (SecretKey.fromBytes (beBytes 32 k)).toOption

def pkOf (k : Nat) : ByteArray :=
  match secret k with
  | some sk => ⟨(skToPk sk).toArray⟩
  | none => ByteArray.empty

def sigOf (k : Nat) (msg : ByteArray) : ByteArray :=
  match secret k with
  | some sk => match sign sk msg with
    | .ok sig => ⟨sig.toArray⟩
    | .error _ => ByteArray.empty
  | none => ByteArray.empty

/-- A secret key decodes from 32 bytes of a number in `[1, r - 1]` only. -/
def secretKeys (oracle : Oracle) : Property IO := propertyM do
  let k ← forAll (genNear r)
  let len ← forAll (Gen.frequency [(8, pure 32), (1, pure 31), (1, pure 33), (1, pure 0)])
  classify "32 bytes of a number in [1, r - 1], accepted" (len == 32 && 0 < k && k < r)
  classify "refused: zero" (len == 32 && k == 0)
  classify "refused: exactly r" (len == 32 && k == r)
  classify "refused: above r" (len == 32 && k > r)
  classify "refused: 31 bytes" (len == 31)
  classify "refused: 33 bytes" (len == 33)
  classify "refused: no byte" (len == 0)
  classify "the key is 1 or r - 1" (len == 32 && (k == 1 || k + 1 == r))
  pure do
    let bytes := beBytes len k
    match SecretKey.fromBytes bytes with
    | .ok sk =>
      ensure (len == 32 && 0 < k && k < r) "a key outside [1, r - 1] is accepted"
      hexVec (skToPk sk) === (← oracle.ask ["sktopk", toString k])
    | .error _ => ensure (!(len == 32 && 0 < k && k < r)) "a valid key is refused"

/-- Signing is `SK * H(message)`, as py_ecc and milagro sign. -/
def signs (oracle : Oracle) : Property IO := propertyM do
  let k ← forAll (Gen.frequency [(1, Gen.element [1, 2, r - 1]), (4, genScalar r)])
  -- 55 bytes is the longest message whose first block of the expansion holds it whole.
  let msg ← forAllWith hex (Gen.frequency [(1, pure ByteArray.empty),
    (3, genBytes (.constant 1 55)), (3, genBytes (.constant 56 200))])
  classify "message empty" (msg.size == 0)
  classify "message of 1 to 55 bytes" (0 < msg.size && msg.size ≤ 55)
  classify "message above 55 bytes" (msg.size > 55)
  classify "the key is 1 or r - 1" (k == 1 || k + 1 == r)
  pure do
    hex (sigOf k msg) === (← oracle.ask ["blssign", toString k, hex msg])
    match secret k with
    | some sk =>
      let proof := (popProve sk).toOption.map hexVec
      proof === some (← oracle.ask ["popprove", toString k])
    | none => failWith "no key"

/-- A public key that key validation must refuse, or the key itself. -/
def genBadKey (good : ByteArray) : Gen ByteArray :=
  Gen.frequency [
    (4, pure good),
    (1, pure ⟨G1.infinityBytes.toArray⟩),
    (1, (fun pt => ⟨(G1.compress pt).toArray⟩) <$> genG1),
    (1, flipBit good <$> Gen.nat (.constant 0 383)),
    (1, pure ⟨(G1.compress (G1.neg ((G1.uncompress
        (vec 48 good)).toOption.getD G1.zero))).toArray⟩)]

/-- A signature that verification must refuse, or the signature itself. -/
def genBadSig (good : ByteArray) : Gen ByteArray :=
  Gen.frequency [
    (4, pure good),
    (1, pure ⟨G2.infinityBytes.toArray⟩),
    (1, (fun pt => ⟨(G2.compress pt).toArray⟩) <$> genG2),
    (1, flipBit good <$> Gen.nat (.constant 0 767)),
    (1, pure ⟨(G2.compress (G2.neg ((G2.uncompress
        (vec 96 good)).toOption.getD G2.zero))).toArray⟩)]

/-- The first rule of the core verification that refuses, in the order of the draft, for a label.

The signature is decoded and checked first, then the key. -/
def coreRefusal (pk sig : ByteArray) : String :=
  if sig.size != 96 then "the signature is not 96 bytes" else
  match G2.uncompress (vec 96 sig) with
  | .error _ => "the signature does not decode"
  | .ok point =>
    if !G2.inSubgroup point then "the signature is outside the subgroup"
    else if pk.size != 48 then "the key is not 48 bytes" else
    match G1.uncompress (vec 48 pk) with
    | .error _ => "the key does not decode"
    | .ok key =>
      if key.isInfinity then "the key is the point at infinity"
      else if !G1.inSubgroup key then "the key is outside the subgroup"
      else if point.isInfinity then "the pairing, with the signature at infinity"
      else "the pairing"

/-- Verification accepts what py_ecc and milagro accept.

The key, the message or the signature is changed at one place. -/
def verifies (oracle : Oracle) : Property IO := propertyM do
  let k ← forAll (genScalar r)
  let msg ← forAllWith hex (genBytes (.linear 0 40))
  let pk ← forAllWith hex (genBadKey (pkOf k))
  let sig ← forAllWith hex (genBadSig (sigOf k msg))
  let msg' ← forAllWith hex (Gen.frequency [(5, pure msg), (1, genBytes (.linear 0 40))])
  pure do
    let got := verify (vec 48 pk) msg' (vec 96 sig)
    classify "accepted" got
    if !got then label s!"refused: {coreRefusal pk sig}"
    classify "refused with a key and a signature that are valid points" (!got &&
      coreRefusal pk sig == "the pairing")
    classify "the message is another one" (msg' != msg)
    (if got then "1" else "0") === (← oracle.ask ["blsverify", hex pk, hex msg', hex sig])
    let proof := match secret k with
      | some sk => (popProve sk).toOption.map (fun (v : BLSSignature) => ByteArray.mk v.toArray)
      | none => none
    let proof := if sig.size == 96 && sig != sigOf k msg then sig else proof.getD sig
    classify "proof of possession: accepted" (popVerify (vec 48 pk) (vec 96 proof))
    classify "proof of possession: refused" (!popVerify (vec 48 pk) (vec 96 proof))
    (if popVerify (vec 48 pk) (vec 96 proof) then "1" else "0") ===
      (← oracle.ask ["popverify", hex pk, hex proof])

/-- Aggregation sums the signatures as py_ecc does, without a subgroup check.

It refuses an empty list and a signature that does not decode. -/
def aggregates (oracle : Oracle) : Property IO := propertyM do
  let one : Gen ByteArray := do
    let k ← genScalar r
    genBadSig (sigOf k (beBytes 4 k))
  -- Two signatures of one message under opposite keys sum to the point at infinity.
  let opposite : Gen (List ByteArray) := do
    let k ← genScalar r
    pure [sigOf k (beBytes 1 7), sigOf (r - k) (beBytes 1 7)]
  let sigs ← forAllWith (fun ss => toString (ss.map hex)) (Gen.frequency [
    (1, pure []), (2, Gen.list (.constant 1 1) one), (6, Gen.list (.constant 2 5) one),
    (1, opposite), (1, (fun pair extra => pair ++ [extra]) <$> opposite <*> one)])
  pure do
    let got := match aggregate (sigs.map (vec 96)).toArray with
      | .ok sig => hexVec sig
      | .error _ => "error"
    let points := sigs.map fun sig => (G2.uncompress (vec 96 sig)).toOption
    classify "refused: no signature" sigs.isEmpty
    classify "refused: a signature does not decode" (points.any Option.isNone)
    classify "aggregated" (got != "error")
    classify "aggregated one signature" (got != "error" && sigs.length == 1)
    classify "aggregated with a point at infinity" (got != "error" &&
      points.any fun pt => pt.any (·.isInfinity))
    classify "aggregated with a point outside the subgroup" (got != "error" &&
      points.any fun pt => pt.any (!G2.inSubgroup ·))
    classify "the aggregate is the point at infinity" (got == hexVec G2.infinityBytes)
    got === (← oracle.ask ["aggregate", listWord (sigs.map hex)])

/-- Signers of one message, or of several, with their aggregate signature. -/
structure Signers where
  keys : List Nat
  msgs : List ByteArray

instance : Repr Signers := ⟨fun s _ => repr (s.keys, s.msgs.map hex)⟩

/-- A few signers; a key or a message is often repeated, and keys may sum to zero. -/
def genSigners : Gen Signers := do
  let key := Gen.frequency [(1, Gen.nat (.constant 1 3)), (2, genScalar r)]
  -- The length does not follow the size: a short run would have no signer at all.
  let keys ← Gen.frequency [(1, pure []), (3, Gen.list (.constant 1 1) key),
    (8, Gen.list (.constant 2 4) key)]
  let keys ← Gen.frequency [(5, pure keys), (2, pure (keys ++ keys.map fun k => r - k))]
  let msgs ← Gen.frequency [
    (1, pure (keys.map fun _ => ByteArray.empty)),
    (2, keys.mapM fun _ => genBytes (.linear 0 8)),
    (1, keys.mapM fun k => pure (beBytes 2 (k % 3)))]
  pure ⟨keys, msgs⟩

/-- The aggregate of the honest signatures, by EthLib; the oracle checks it by verifying. -/
def aggregateOf (keys : List Nat) (msgs : List ByteArray) : ByteArray :=
  match aggregate ((keys.zip msgs).map fun (k, m) => vec 96 (sigOf k m)).toArray with
  | .ok sig => ⟨sig.toArray⟩
  | .error _ => ⟨G2.infinityBytes.toArray⟩

/-- The aggregate verification of several messages is py_ecc's and milagro's. -/
def aggregateVerifies (oracle : Oracle) : Property IO := propertyM do
  let signers ← forAll genSigners
  let good := aggregateOf signers.keys signers.msgs
  let sig ← forAllWith hex (genBadSig good)
  let drop ← forAll (Gen.frequency [(5, pure 0), (1, pure 1)])
  let badKey ← forAll (Gen.frequency [(5, pure false), (1, pure true)])
  pure do
    let pks := signers.keys.map pkOf
    let pks := if badKey then pks.map fun _ => ByteArray.mk G1.infinityBytes.toArray else pks
    let msgs := signers.msgs.drop drop
    let got := coreAggregateVerify pks.toArray msgs.toArray sig DST
    classify "accepted" got
    classify "accepted with a message twice" (got && (msgs.map hex).eraseDups.length < msgs.length)
    classify "accepted with one signer" (got && pks.length == 1)
    classify "refused: no signer" pks.isEmpty
    classify "refused: fewer messages than keys" (!pks.isEmpty && pks.length != msgs.length)
    classify "refused: a key at infinity" (badKey && !pks.isEmpty)
    classify "refused: the signature changed" (!got && sig != good && !pks.isEmpty)
    classify "refused: honest inputs" (!got && sig == good && !badKey && drop == 0 &&
      !pks.isEmpty)
    classify "accepted with keys that sum to the point at infinity" (got &&
      signers.keys.foldl (· + ·) 0 % r == 0)
    classify "accepted with two signers or more" (got && pks.length ≥ 2)
    (if got then "1" else "0") === (← oracle.ask
      ["aggverify", listWord (pks.map hex), listWord (msgs.map hex), hex sig])
    if !badKey && drop == 0 then
      (if aggregateVerify (pks.map (vec 48)).toArray msgs.toArray (vec 96 sig) then "1" else "0")
        === (if got then "1" else "0")

/-- The fast aggregate verification is that of the draft and of the consensus specification.

So are the two wrappers of Ethereum. -/
def fastAggregateVerifies (oracle : Oracle) : Property IO := propertyM do
  let signers ← forAll genSigners
  let msg ← forAllWith hex (genBytes (.linear 0 8))
  let good := aggregateOf signers.keys (signers.keys.map fun _ => msg)
  let sig ← forAllWith hex (genBadSig good)
  let keys ← forAllWith (fun ks => toString (ks.map hex))
    ((signers.keys.map pkOf).mapM fun pk =>
      Gen.frequency [(12, pure pk), (1, genBadKey pk)])
  pure do
    let pks := (keys.map (vec 48)).toArray
    let words := [listWord (keys.map hex), hex msg, hex sig]
    let got := fastAggregateVerify pks msg (vec 96 sig)
    let eth := ethFastAggregateVerify pks msg (vec 96 sig)
    classify "accepted" got
    classify "no key, and the signature at infinity: Ethereum accepts, the draft refuses"
      (eth && !got)
    classify "no key, and another signature: both refuse" (keys.isEmpty && !eth)
    classify "refused: a key fails validation" (!keys.isEmpty &&
      (ethAggregatePubkeys pks).toOption.isNone)
    classify "refused: the keys sum to the point at infinity" (!keys.isEmpty &&
      (ethAggregatePubkeys pks).toOption == some G1.infinityBytes)
    classify "refused: the signature changed" (!got && !keys.isEmpty && sig != good)
    classify "one key" (keys.length == 1)
    (if fastAggregateVerify pks msg (vec 96 sig) then "1" else "0") ===
      (← oracle.ask ("fastaggverify" :: words))
    (if ethFastAggregateVerify pks msg (vec 96 sig) then "1" else "0") ===
      (← oracle.ask ("ethfastaggverify" :: words))
    let sum := match ethAggregatePubkeys pks with
      | .ok pk => hexVec pk
      | .error _ => "error"
    sum === (← oracle.ask ["ethaggpk", listWord (keys.map hex)])

/-- Key generation is `HKDF_mod_r`, as py_ecc's `KeyGen` and a model of ERC-2333. -/
def keyGens (oracle : Oracle) : Property IO := propertyM do
  let ikm ← forAllWith hex (Gen.frequency [(5, genBytes (.linear 32 80)),
    (1, genBytes (.linear 0 31)), (1, pure (beBytes 32 0))])
  let info ← forAllWith hex (Gen.frequency [(2, pure ByteArray.empty), (1, genBytes
      (.linear 0 40))])
  classify "refused: fewer than 32 bytes" (ikm.size < 32)
  classify "exactly 32 bytes" (ikm.size == 32)
  classify "more than 32 bytes" (ikm.size > 32)
  classify "key info given" (info.size > 0)
  pure do
    let got := match keyGen ikm info with
      | .ok sk => toString sk.val.val
      | .error _ => "error"
    got === (← oracle.ask ["keygen", hex ikm, hex info])

/-- A child index at the edges of 32 bits. -/
def genIndex : Gen UInt32 :=
  UInt32.ofNat <$> Gen.frequency [(2, Gen.nat (.linear 0 4)), (1, Gen.element [12381, 3600,
    2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1]), (2, Gen.nat (.constant 0 (2 ^ 32 - 1)))]

/-- The tree of ERC-2333: the master key of a seed and its children, by a model of the text. -/
def derives (oracle : Oracle) : Property IO := propertyM do
  let seed ← forAllWith hex (Gen.frequency [(6, genBytes (.linear 32 64)), (1, genBytes
      (.linear 0 31))])
  let path ← forAll (Gen.list (.constant 0 3) genIndex)
  classify "refused: a seed below 32 bytes" (seed.size < 32)
  classify "the master key, no index" path.isEmpty
  classify "one index" (path.length == 1)
  classify "two or three indices" (path.length ≥ 2)
  classify "an index of 2^31 or more" (path.any (·.toNat ≥ 2 ^ 31))
  classify "the index 2^32 - 1" (path.any (·.toNat == 2 ^ 32 - 1))
  classify "the index 0" (path.any (·.toNat == 0))
  pure do
    let got := match KeyDerivation.derivePath seed path with
      | .ok sk => toString sk.val.val
      | .error _ => "error"
    got === (← oracle.ask ("derivepath" :: hex seed :: path.map fun i => toString i.toNat))

/-- A path text of ERC-2334, valid or changed at one place.

Half of the texts are valid, so that the accepting branch and its fields are read often. -/
def genPathText : Gen String := do
  let index := (fun i : UInt32 => toString i.toNat) <$> genIndex
  let bad := Gen.frequency [
    (3, Gen.element ["4294967296", "4294967297", "18446744073709551616"]),
    (1, pure "4294967295"),
    (4, Gen.element ["012381", "", "1'", " 1", "-1", "0x1", "١", "1 ", "+1"])]
  let spoil ← Gen.frequency [(5, pure false), (4, pure true)]
  let indices ← Gen.list (.constant 0 6) (if spoil then Gen.frequency [(5, index), (1, bad)]
    else index)
  -- The purpose is 12381, or another number, or missing.
  let purpose ← Gen.frequency [(12, pure ["12381"]), (1, pure []), (1, pure ["12380"]),
    (1, pure ["12382"]), (1, pure ["012381"])]
  let root ← Gen.frequency [(14, pure "m"), (1, pure "M"), (1, pure ""), (1, pure "m ")]
  pure ("/".intercalate (root :: purpose ++ indices))

/-- The model of a path: `m`, then four or more decimal indices below `2 ^ 32`, the first 12381. -/
def pathModel (text : String) : Option (List Nat) :=
  match text.splitOn "/" with
  | "m" :: parts =>
    let numbers := parts.map fun part =>
      if !part.isEmpty && part.all (fun c => '0' ≤ c && c ≤ '9') then part.toNat? else none
    if numbers.all Option.isSome && parts.length ≥ 4 then
      let values := numbers.filterMap id
      if values.all (· < 2 ^ 32) && values.head? == some 12381 then some values else none
    else none
  | _ => none

/-- The parser of key paths accepts the paths of ERC-2334 and writes them back. -/
def paths : Property IO := pureIO do
  let text ← forAll genPathText
  let parts := text.splitOn "/"
  classify "accepted" (pathModel text).isSome
  classify "accepted with exactly four indices" ((pathModel text).any (·.length == 4))
  classify "accepted with the index 2^32 - 1" ((pathModel text).any (·.contains (2 ^ 32 - 1)))
  classify "an index with a leading zero" (parts.tail.any fun part =>
    part.length > 1 && part.startsWith "0" && part.all fun c => '0' ≤ c && c ≤ '9')
  match KeyPath.parsePath text with
  | .ok path =>
    some (path.indices.map (·.toNat)) === pathModel text
    (KeyPath.parsePath path.toString).toOption === some path
  | .error e =>
    label s!"refused: {ctorName e}"
    pathModel text === none
  -- The two paths of a validator, as ERC-2334 writes them under "Validator keys".
  let index ← forAll genIndex
  (KeyPath.withdrawalPath index).toString === s!"m/12381/3600/{index.toNat}/0"
  (KeyPath.signingPath index).toString === s!"m/12381/3600/{index.toNat}/0/0"

end CurvesProperty.Bls12

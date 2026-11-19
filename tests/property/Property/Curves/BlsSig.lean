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
  pure do
    let bytes := beBytes len k
    match SecretKey.fromBytes bytes with
    | .ok sk =>
      ensure (len == 32 && 0 < k && k < r) "a key outside [1, r - 1] is accepted"
      hexVec (skToPk sk) === (← oracle.ask ["sktopk", toString k])
    | .error _ => ensure (!(len == 32 && 0 < k && k < r)) "a valid key is refused"

/-- Signing is `SK * H(message)`, as py_ecc and milagro sign. -/
def signs (oracle : Oracle) : Property IO := propertyM do
  let k ← forAll (genScalar r)
  let msg ← forAllWith hex (genBytes (.linear 0 100))
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

/-- Verification accepts what py_ecc and milagro accept, on a key, message or signature
changed at one place. -/
def verifies (oracle : Oracle) : Property IO := propertyM do
  let k ← forAll (genScalar r)
  let msg ← forAllWith hex (genBytes (.linear 0 40))
  let pk ← forAllWith hex (genBadKey (pkOf k))
  let sig ← forAllWith hex (genBadSig (sigOf k msg))
  let msg' ← forAllWith hex (Gen.frequency [(5, pure msg), (1, genBytes (.linear 0 40))])
  pure do
    let got := verify (vec 48 pk) msg' (vec 96 sig)
    (if got then "1" else "0") === (← oracle.ask ["blsverify", hex pk, hex msg', hex sig])
    let proof := match secret k with
      | some sk => (popProve sk).toOption.map (fun (v : BLSSignature) => ByteArray.mk v.toArray)
      | none => none
    let proof := if sig.size == 96 && sig != sigOf k msg then sig else proof.getD sig
    (if popVerify (vec 48 pk) (vec 96 proof) then "1" else "0") ===
      (← oracle.ask ["popverify", hex pk, hex proof])

/-- Aggregation sums the signatures as py_ecc does, without a subgroup check, and refuses
an empty list and a signature that does not decode. -/
def aggregates (oracle : Oracle) : Property IO := propertyM do
  let sigs ← forAllWith (fun ss => toString (ss.map hex)) (Gen.list (.linear 0 5) (do
    let k ← genScalar r
    genBadSig (sigOf k (beBytes 4 k))))
  pure do
    let got := match aggregate (sigs.map (vec 96)).toArray with
      | .ok sig => hexVec sig
      | .error _ => "error"
    got === (← oracle.ask ["aggregate", listWord (sigs.map hex)])

/-- Signers of one message, or of several, with their aggregate signature. -/
structure Signers where
  keys : List Nat
  msgs : List ByteArray

instance : Repr Signers := ⟨fun s _ => repr (s.keys, s.msgs.map hex)⟩

/-- A few signers; a key or a message is often repeated, and keys may sum to zero. -/
def genSigners : Gen Signers := do
  let keys ← Gen.list (.linear 0 4)
    (Gen.frequency [(1, Gen.nat (.constant 1 3)), (2, genScalar r)])
  let keys ← Gen.frequency [(6, pure keys), (1, pure (keys ++ keys.map fun k => r - k))]
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
    (if got then "1" else "0") === (← oracle.ask
      ["aggverify", listWord (pks.map hex), listWord (msgs.map hex), hex sig])
    if !badKey && drop == 0 then
      (if aggregateVerify (pks.map (vec 48)).toArray msgs.toArray (vec 96 sig) then "1" else "0")
        === (if got then "1" else "0")

/-- The fast aggregate verification, and the two wrappers of Ethereum, are those of the draft
and of the consensus specification. -/
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
  let path ← forAll (Gen.list (.linear 0 3) genIndex)
  pure do
    let got := match KeyDerivation.derivePath seed path with
      | .ok sk => toString sk.val.val
      | .error _ => "error"
    got === (← oracle.ask ("derivepath" :: hex seed :: path.map fun i => toString i.toNat))

/-- A path text of ERC-2334, valid or changed at one place. -/
def genPathText : Gen String := do
  let indices ← Gen.list (.linear 0 7) (Gen.frequency [
    (4, (fun i : UInt32 => toString i.toNat) <$> genIndex),
    (1, pure "12381"), (1, pure "4294967296"), (1, pure "012381"), (1, pure ""),
    (1, pure "1'"), (1, pure " 1"), (1, pure "-1"), (1, pure "0x1"), (1, pure "١")])
  let indices ← Gen.frequency [(3, pure ("12381" :: indices)), (1, pure indices)]
  let root ← Gen.frequency [(8, pure "m"), (1, pure "M"), (1, pure ""), (1, pure "m ")]
  pure ("/".intercalate (root :: indices))

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
  match KeyPath.parsePath text with
  | .ok path =>
    some (path.indices.map (·.toNat)) === pathModel text
    (KeyPath.parsePath path.toString).toOption === some path
  | .error _ => pathModel text === none

end CurvesProperty.Bls12

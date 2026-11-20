import Property.Curves.Common
import EthLib.Cryptography.Xmss

/-!
# leanXMSS against a model of its specification

The model (`oracle/curves_xmss.py`) is written from the formulas of the specification draft.

Verification runs on the valid signatures of `tests/cryptography/xmss/verify`, changed at one place.

The reason is that making a signature builds `2^16` one-time keys.

The parts of signing that are cheap run in full: one one-time signature, and a small subtree.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.XmssTest

open Xmss

/-- A public key, a message and a signature, as bytes. -/
structure Signed where
  pk : ByteArray
  msg : ByteArray
  sig : ByteArray

instance : Repr Signed := ⟨fun s _ => s!"pk {hex s.pk} msg {hex s.msg} sig {hex s.sig}"⟩

/-- The valid vectors of the repository. -/
def validNames : List String :=
  ["verify_valid_first_leaf", "verify_valid_known_answer", "verify_valid_last_leaf",
    "verify_valid_second_tree"]

/-- Read the valid vectors through the oracle. -/
def loadVectors (oracle : Oracle) : IO (List Signed) :=
  validNames.mapM fun name => do
    oracle.stdin.putStrLn s!"xmssvector\t{name}"
    oracle.stdin.flush
    let line := (← oracle.stdout.getLine).trimAscii.toString
    match (line.splitOn " ").map unhex? with
    | [some pk, some msg, some sig] => pure ⟨pk, msg, sig⟩
    | _ => throw (IO.userError s!"no vector {name}: {line.take 80}")

/-- EthLib's answer on bytes: `1`, `0`, or `error` for a wrong length. -/
def verdict (s : Signed) : String :=
  match decodePublicKey s.pk, decodeSignature s.sig with
  | .ok pk, .ok sig =>
    if h : s.msg.size = 32 then
      if verify pk ⟨s.msg.data, h⟩ sig then "1" else "0"
    else "error"
  | _, _ => "error"

/-- The offsets where the fields of a signature start.

The fields are the index, then per layer the randomizer, the 58 chain values and the 16 siblings. -/
def fieldStarts : List Nat :=
  [0] ++ [4, 1204].flatMap fun base =>
    [base] ++ (List.range 58).map (base + 16 + 16 * ·) ++
      (List.range 16).map (base + 944 + 16 * ·)

/-- One change to a signed message. -/
inductive Change where
  | none
  | sigBit (bit : Nat)
  | sigField (field : Nat) (bit : Nat)
  | msgBit (bit : Nat)
  | pkBit (bit : Nat)
  | index (value : Nat)
  | swapLayers
  | swapChains (i j : Nat)
  | sigSize (delta : Int)
  | msgSize (delta : Int)
  | pkSize (delta : Int)
  deriving Repr, BEq

def genChange : Gen Change :=
  Gen.frequency [
    (2, pure .none),
    (4, .sigBit <$> Gen.nat (.constant 0 (8 * 2404 - 1))),
    -- A field by its kind first: the index, a randomizer, a chain value or a sibling.
    (5, Gen.zipWith .sigField (Gen.frequency [(1, pure 0), (4, Gen.element [1, 76]),
      (2, Gen.nat (.constant 2 59)), (2, Gen.nat (.constant 77 134)),
      (2, Gen.nat (.constant 60 75)), (2, Gen.nat (.constant 135 150))])
      (Gen.nat (.constant 0 127))),
    (2, .msgBit <$> Gen.nat (.constant 0 255)),
    (2, .pkBit <$> Gen.nat (.constant 0 255)),
    (2, .index <$> Gen.frequency [(1, Gen.nat (.linear 0 3)), (1, pure (2 ^ 32 - 1)),
      (1, pure 65536), (2, Gen.nat (.constant 0 (2 ^ 32 - 1)))]),
    (1, pure .swapLayers),
    (1, Gen.zipWith .swapChains (Gen.nat (.constant 0 57)) (Gen.nat (.constant 0 57))),
    (1, .sigSize <$> Gen.element [-1, 1, -4, 16]),
    (1, .msgSize <$> Gen.element [-1, 1]),
    (1, .pkSize <$> Gen.element [-1, 1, -16])]

/-- Bytes made longer by zeros or shorter by their end. -/
def resize (bytes : ByteArray) (delta : Int) : ByteArray :=
  if delta ≥ 0 then bytes ++ ⟨Array.replicate delta.toNat 0⟩
  else bytes.extract 0 (bytes.size - (-delta).toNat)

def Change.apply (s : Signed) : Change → Signed
  | .none => s
  | .sigBit bit => { s with sig := flipBit s.sig bit }
  | .sigField field bit =>
    { s with sig := flipBit s.sig (8 * fieldStarts[field % fieldStarts.length]! + bit) }
  | .msgBit bit => { s with msg := flipBit s.msg bit }
  | .pkBit bit => { s with pk := flipBit s.pk bit }
  | .index value =>
    { s with sig := ⟨(Base.uintToBytes 4 value).toArray⟩ ++ s.sig.extract 4 s.sig.size }
  | .swapLayers =>
    { s with sig := s.sig.extract 0 4 ++ s.sig.extract 1204 2404 ++ s.sig.extract 4 1204 }
  | .swapChains i j =>
    let at_ (k : Nat) := s.sig.extract (20 + 16 * k) (36 + 16 * k)
    let put (sig : ByteArray) (k : Nat) (value : ByteArray) :=
      sig.extract 0 (20 + 16 * k) ++ value ++ sig.extract (36 + 16 * k) sig.size
    { s with sig := put (put s.sig i (at_ j)) j (at_ i) }
  | .sigSize delta => { s with sig := resize s.sig delta }
  | .msgSize delta => { s with msg := resize s.msg delta }
  | .pkSize delta => { s with pk := resize s.pk delta }

/-- The name of a change, for a label. -/
def Change.name : Change → String
  | .none => "nothing"
  | .sigBit _ => "any bit of the signature"
  | .sigField field _ =>
    let start := fieldStarts[field % fieldStarts.length]!
    let base := if start ≥ 1204 then 1204 else 4
    let layer := if start ≥ 1204 then "top" else "bottom"
    if start == 0 then "a bit of the leaf index"
    else if start == base then s!"a bit of the {layer} randomizer"
    else if start < base + 944 then s!"a bit of a {layer} chain value"
    else s!"a bit of a {layer} sibling"
  | .msgBit _ => "a bit of the message"
  | .pkBit bit => if bit < 128 then "a bit of the root" else "a bit of the public parameter"
  | .index _ => "the leaf index"
  | .swapLayers => "the two layers exchanged"
  | .swapChains _ _ => "two chain values exchanged"
  | .sigSize _ => "the length of the signature"
  | .msgSize _ => "the length of the message"
  | .pkSize _ => "the length of the key"

/-- Verification accepts a valid signature.

It agrees with the model on every signature changed at one place.

The change is a bit of any field, the leaf index, the order of two values, or a length. -/
def verifies (oracle : Oracle) (vectors : List Signed) : Property IO := propertyM do
  let which ← forAll (Gen.nat (.constant 0 (vectors.length - 1)))
  let change ← forAll genChange
  let some base := vectors[which]? | discard
  pure do
    let s := change.apply base
    let got := verdict s
    label s!"changed: {change.name}"
    label s!"vector {validNames[which]!}"
    classify "accepted" (got == "1")
    classify "refused: a wrong length" (got == "error")
    -- Which step of verification refuses, by the roots that the two layers lead to.
    match decodePublicKey s.pk, decodeSignature s.sig with
    | .ok pk, .ok sig =>
      if h : s.msg.size = 32 then
        let bottom := (layerRoot hashId pk.publicParam .bottom sig.leafIndex.toNat s.msg
          sig.bottom).run
        let top := bottom.bind fun root => (layerRoot hashId pk.publicParam .top
          (bottomTree sig.leafIndex) ⟨root.toArray⟩ sig.top).run
        classify "refused: the bottom digest is not a codeword" bottom.isNone
        classify "refused: the top digest is not a codeword" (bottom.isSome && top.isNone)
        classify "refused: the path ends at another root" (top.any (· != pk.root))
        classify "accepted after a change" (got == "1" && change != .none)
        let _ := h
    | _, _ => pure ()
    got === (← oracle.ask ["xmssverify", hex s.pk, hex s.msg, hex s.sig])
    if change == .none then got === "1"
    -- The index a signature carries is its first four bytes, little-endian.
    let first := (s.sig.extract 0 4).data.foldr (fun b acc => acc * 256 + b.toNat) 0
    match signatureIndex s.sig with
    | .ok index =>
      ensure (s.sig.size == 2404 && index.toNat == first) "the index is not the first four bytes"
    | .error _ => ensure (s.sig.size != 2404) "the index of a whole signature is refused"
    -- What decodes encodes back to the same bytes.
    match decodeSignature s.sig, decodePublicKey s.pk with
    | .ok sig, .ok pk =>
      hex (encodeSignature sig) === hex s.sig
      hex (encodePublicKey pk) === hex s.pk
    | _, _ => pure ()

/-- A digest near a codeword: 58 digits that sum to about 106, and a tail of zeros or not. -/
def genDigest : Gen (Vector UInt8 16) := do
  let digits ← Gen.list (.singleton 58) (Gen.nat (.constant 0 3))
  -- Move the sum to 106 or next to it, one digit at a time.
  let target ← Gen.frequency [(4, pure 106), (1, pure 105), (1, pure 107), (1, pure (digits.sum))]
  let fix (ds : List Nat) : List Nat := Id.run do
    let mut ds := ds.toArray
    for _ in [0:200] do
      let sum := ds.foldl (· + ·) 0
      if sum < target then
        match ds.findIdx? (· < 3) with
        | some i => ds := ds.set! i (ds[i]! + 1)
        | none => pure ()
      else if sum > target then
        match ds.findIdx? (· > 0) with
        | some i => ds := ds.set! i (ds[i]! - 1)
        | none => pure ()
    return ds.toList
  let digits ← Gen.shuffle (fix digits)
  let tail ← Gen.frequency [(4, pure [0, 0, 0, 0, 0, 0]),
    (2, Gen.list (.singleton 6) (Gen.nat (.constant 0 3))),
    (1, (fun i => (List.range 6).map fun j => if j == i then 1 else 0) <$> Gen.nat (.constant 0 5))]
  let value := (digits ++ tail).foldr (fun d acc => acc * 4 + d) 0
  pure (Vector.ofFn fun i => UInt8.ofNat (value >>> (8 * i.val)))

/-- A digest is a codeword when its last 6 digits are zero and its first 58 sum to 106. -/
def codewords (oracle : Oracle) : Property IO := propertyM do
  let digest ← forAllWith hexVec genDigest
  pure do
    let got := match codeword? digest with
      | some x => String.join (x.toList.map fun d => toString d.val)
      | none => "none"
    let value := digest.toList.foldr (fun b acc => acc * 256 + b.toNat) 0
    let all := (List.range 64).map fun i => value >>> (2 * i) % 4
    let sum := (all.take 58).foldl (· + ·) 0
    classify "a codeword" (got != "none")
    classify "refused: the sum is 105" (sum == 105)
    classify "refused: the sum is 107" (sum == 107)
    classify "refused: another sum" (sum != 106 && sum != 105 && sum != 107)
    classify "refused: the sum is 106 and a last digit is not zero" (sum == 106 &&
      (all.drop 58).any (· != 0))
    classify "refused: only digit 63 is not zero, at sum 106" (sum == 106 &&
      (all.drop 58) == [0, 0, 0, 0, 0, all[63]!] && all[63]! != 0)
    got === (← oracle.ask ["xmsscodeword", hexVec digest])

def genLayer : Gen Layer := Gen.element [.bottom, .top]

/-- A key index: the edges of 32 bits. -/
def genKeyIndex : Gen Nat :=
  Gen.frequency [(2, Gen.nat (.linear 0 4)), (1, Gen.element [65535, 65536, 2 ^ 32 - 1]),
    (2, Gen.nat (.constant 0 (2 ^ 32 - 1)))]

/-- The root a path leads to is the model's, for any leaf, key index and siblings. -/
def folds (oracle : Oracle) : Property IO := propertyM do
  let (pp, leaf) ← forAllWith (fun (a, b) => s!"{hex a} {hex b}") (Gen.zip (genBytesN 16)
      (genBytesN 16))
  let path ← forAllWith hex (genBytesN 256)
  let (layer, e) ← forAll (Gen.zip genLayer genKeyIndex)
  classify "the bottom layer" (layer == .bottom)
  classify "the top layer" (layer == .top)
  classify "a key index below 2^16" (e < 2 ^ 16)
  classify "a key index of 2^16 or more, past the 16 levels" (e ≥ 2 ^ 16)
  classify "the key index 2^32 - 1" (e == 2 ^ 32 - 1)
  classify "the key index 0, a left child at every level" (e == 0)
  classify "the key index 65535, a right child at every level" (e % 65536 == 65535)
  pure do
    let v16 (b : ByteArray) : Vector UInt8 16 := Vector.ofFn fun i => b[i.val]!
    let siblings : Vector Digest 16 :=
        Vector.ofFn fun i => v16 (path.extract (16 * i.val) (16 * i.val + 16))
    let got := (fold hashId (v16 pp) layer e (v16 leaf) siblings).run
    hexVec got === (← oracle.ask ["xmssfold", hex pp, toString layer.toNat, toString e, hex leaf,
      hex path])

/-- The leaf of a claimed one-time signature is the model's.

The digest must be a codeword, which a search over the randomizer finds here.

Each chain walks from its digit. -/
def otsLeaves (oracle : Oracle) : Property IO := propertyM do
  let (pp, msg) ← forAllWith (fun (a, b) => s!"{hex a} {hex b}")
    (Gen.zip (genBytesN 16) (Gen.frequency [(1, genBytesN 32), (1, genBytesN 16)]))
  let y ← forAllWith hex (genBytesN (58 * 16))
  let (layer, e) ← forAll (Gen.zip genLayer genKeyIndex)
  let search ← forAll Gen.bool
  let start ← forAll (Gen.nat (.constant 0 (2 ^ 64)))
  pure do
    let v16 (b : ByteArray) : Vector UInt8 16 := Vector.ofFn fun i => b[i.val]!
    let chains : Vector Digest 58 :=
        Vector.ofFn fun i => v16 (y.extract (16 * i.val) (16 * i.val + 16))
    let e32 := UInt32.ofNat e
    -- A random randomizer is almost never a codeword, so half the cases search for one.
    let rho : Randomizer := if search then
        match (Internal.findCodeword hashId (v16 pp) layer e32 msg (Base.uintToBytes 16 start) 0
          (2 ^ 23)).run with
        | some (rho, _) => rho
        | none => Base.uintToBytes 16 start
      else Base.uintToBytes 16 start
    let got := match (otsLeaf hashId (v16 pp) layer e32 msg rho chains).run with
      | some leaf => hexVec leaf
      | none => "none"
    classify "a leaf, from a codeword" (got != "none")
    classify "refused: the digest is not a codeword" (got == "none")
    classify "a message of 32 bytes" (msg.size == 32)
    classify "a message of 16 bytes, a root" (msg.size == 16)
    classify "the top layer" (layer == .top)
    -- Each digit names where a chain starts, so every digit should turn up.
    match codeword? (messageDigest hashId (v16 pp) layer e32 msg rho).run with
    | some x =>
      for d in [0, 1, 2, 3] do
        classify s!"a chain starts at digit {d}" (x.toList.any (·.val == d))
    | none => pure ()
    got === (← oracle.ask ["xmssotsleaf", hex pp, toString layer.toNat, toString e, hex msg,
      hexVec rho, hex y])

/-- The public parameter and a small subtree of a seed are the model's. -/
def subtrees (oracle : Oracle) : Property IO := propertyM do
  let seed ← forAllWith hex (genBytesN 32)
  let (layer, level) ← forAll (Gen.zip genLayer (Gen.frequency [(4, Gen.nat (.constant 0 3)),
    (2, Gen.nat (.constant 4 5)), (1, pure 6)]))
  let j ← forAll (Gen.frequency [(2, Gen.nat (.linear 0 4)), (1, pure (2 ^ (32 - level) - 1)),
    (1, Gen.nat (.constant 0 (2 ^ (32 - level) - 1)))])
  label s!"level {level}"
  classify "the top layer" (layer == .top)
  classify "the last node of its level" (j == 2 ^ (32 - level) - 1)
  pure do
    let s := (schemeSeed hashId (vec32 (beNat seed))).run
    let prf := seedPrf hashId s
    let pp := (publicParamOf prf).run
    let got := (node hashId pp prf layer level j).run
    s!"{hexVec pp} {hexVec got}" === (← oracle.ask ["xmsskey", hex seed, toString layer.toNat,
      toString level, toString j])

/-- One one-time signature is the model's.

It has the least randomizer trial whose digest is a codeword, and each chain revealed at its digit.

Its leaf is the public leaf of the key. -/
def otsSigns (oracle : Oracle) : Property IO := propertyM do
  let seed ← forAllWith hex (genBytesN 32)
  let msg ← forAllWith hex (Gen.frequency [(1, genBytesN 32), (1, genBytesN 16)])
  let (layer, e) ← forAll (Gen.zip genLayer genKeyIndex)
  classify "the top layer" (layer == .top)
  classify "a message of 16 bytes, a root" (msg.size == 16)
  pure do
    let s := (schemeSeed hashId (vec32 (beNat seed))).run
    let prf := seedPrf hashId s
    let pp := (publicParamOf prf).run
    let e32 := UInt32.ofNat e
    match (otsSign hashId pp prf layer e32 msg).run with
    | some (rho, y) =>
      s!"{hexVec rho} {hex (packDigests y)}" === (← oracle.ask ["xmssots", hex seed,
        toString layer.toNat, toString e, hex msg])
      (otsLeaf hashId pp layer e32 msg rho y).run === some
          (otsPublicLeaf hashId pp prf layer e32).run
    | none => failWith "no codeword"

end CurvesProperty.XmssTest

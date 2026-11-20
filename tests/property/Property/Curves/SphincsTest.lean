import Property.Curves.Common
import EthLib.Cryptography.Sphincs

/-!
# leanSPHINCS: signing against verification

The reference is a model of verification (`oracle/curves_sphincs.py`).

It is written from FIPS 205 and the formulas of the scheme.

It is checked against the vectors of the repository.

A signature of a key verifies.

Any single bit changed in the signature, the message or the key is refused, as in the model.

The fields of the digest are the bits that FIPS 205 Algorithm 19 names.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.SphincsTest

open Sphincs

/-- The offsets where the fields of a signature start.

The fields are the randomizer, then each FORS opening and its path nodes.

Then per layer come the counter, the chain values and the siblings. -/
def fieldStarts : List Nat :=
  [0] ++ (List.range (24 * 11)).map (16 + 16 * ·) ++
    [(4240, 8), (5396, 8), (6552, 10)].flatMap fun (base, height) =>
      [base] ++ (List.range (64 + height)).map (base + 4 + 16 * ·)

/-- The step of verification that refuses, or `accepted`, for a label.

The steps are those of `verifyWith`: a layer whose digest is no codeword, then the last root. -/
def refusalStep (pk : PublicKey) (msg : Message) (sig : Signature) : String := Id.run do
  let d ← hMsg hashId sig.randomizer pk.pkSeed pk.root msg
  let idx := digestIndex d
  let forsPk ← forsRecover hashId pk.pkSeed idx (digestLeaves d) sig.fors
  let some bottom ← layerRoot hashId pk.pkSeed .bottom idx forsPk sig.bottom
    | return "the bottom digest is not a codeword"
  let some middle ← layerRoot hashId pk.pkSeed .middle idx bottom sig.middle
    | return "the middle digest is not a codeword"
  let some root ← layerRoot hashId pk.pkSeed .top idx middle sig.top
    | return "the top digest is not a codeword"
  return if root == pk.root then "accepted" else "the path ends at another root"

/-- The field of a signature that starts at an offset, for a label. -/
def fieldName (start : Nat) : String :=
  if start == 0 then "the randomizer"
  else if start < 4240 then
    if (start - 16) % 176 == 0 then "a FORS secret" else "a FORS path node"
  else
    let (base, layer) := if start ≥ 6552 then (6552, "top") else if start ≥ 5396
      then (5396, "middle") else (4240, "bottom")
    if start == base then s!"the {layer} counter"
    else if start < base + 4 + 16 * 64 then s!"a {layer} chain value"
    else s!"a {layer} sibling"

/-- A key signs, and the signature verifies and encodes to 7740 bytes that decode back.

A signature, message or key with one bit changed, or of another length, is refused. -/
def signsAndVerifies (oracle : Oracle) : Property IO := propertyM do
  let (seed, msg) ← forAllWith (fun (a, b) => s!"{hex a} {hex b}")
    (Gen.zip (Gen.frequency [(1, pure (beBytes 32 0)), (3, genBytesN 32)])
      (Gen.frequency [(1, pure (beBytes 32 0)), (3, genBytesN 32)]))
  -- A field of the signature by its kind first, so that the few fields of the top are common.
  --
  -- The fields are the randomizer and 24 openings of 11 values.
  --
  -- Then each layer has a counter, 64 chain values and its siblings: 8, 8 and 10.
  let field : Gen Nat := Gen.frequency [
    (1, pure 0), (1, (1 + 11 * ·) <$> Gen.nat (.constant 0 23)),
    (1, Gen.nat (.constant 1 264)),
    (1, Gen.element [265, 338, 411]),
    (1, Gen.nat (.constant 266 329)), (1, Gen.nat (.constant 339 402)),
    (1, Gen.nat (.constant 412 475)),
    (2, Gen.nat (.constant 330 337)), (2, Gen.nat (.constant 403 410)),
    (3, Gen.nat (.constant 476 485))]
  let changes ← forAll (Gen.list (.constant 6 10) (Gen.zip (Gen.nat (.constant 0 5))
    (Gen.zip field (Gen.nat (.constant 0 127)))))
  pure do
    let v32 (b : ByteArray) : Vector UInt8 32 := Vector.ofFn fun i => b[i.val]!
    let (sk, pk) := keyGen (v32 seed)
    let .ok sig := sign sk (v32 msg) | failWith "signing failed"
    ensure (verify pk (v32 msg) sig) "an honest signature is refused"
    let sigBytes := encodeSignature sig
    let pkBytes := encodePublicKey pk
    sigBytes.size === 7740
    pkBytes.size === 32
    ensure ((decodeSignature sigBytes).toOption == some sig) "the signature does not decode back"
    ensure ((decodePublicKey pkBytes).toOption == some pk) "the key does not decode back"
    let verdict (pkBytes msg sigBytes : ByteArray) : String :=
      match decodePublicKey pkBytes, decodeSignature sigBytes with
      | .ok pk, .ok sig =>
        if msg.size == 32 then (if verify pk (v32 msg) sig then "1" else "0") else "error"
      | _, _ => "error"
    let agree (pkBytes msg sigBytes : ByteArray) (honest : Bool) : TestT IO Unit := do
      let got := verdict pkBytes msg sigBytes
      match decodePublicKey pkBytes, decodeSignature sigBytes with
      | .ok pk, .ok sig =>
        if msg.size == 32 then
          let step := refusalStep pk (v32 msg) sig
          label (if step == "accepted" then step else s!"refused: {step}")
        else label "refused: a wrong length"
      | _, _ => label "refused: a wrong length"
      got === (← oracle.ask ["sphincsverify", hex pkBytes, hex msg, hex sigBytes])
      ensure ((got == "1") == honest) "a changed input is accepted"
    agree pkBytes msg sigBytes true
    for (kind, field, bit) in changes do
      annotate s!"change {kind} {field} {bit}"
      label (match kind with
        | 0 => if field % 32 < 16 then "changed: a bit of the key's seed"
          else "changed: a bit of the key's root"
        | 1 => "changed: a bit of the message"
        | 2 => "changed: a length"
        | _ => s!"changed: a bit of {fieldName fieldStarts[field]!}")
      match kind with
      | 0 => agree (flipBit pkBytes (8 * (field % 32) + bit % 8)) msg sigBytes false
      | 1 => agree pkBytes (flipBit msg (8 * (field % 32) + bit % 8)) sigBytes false
      | 2 =>
        agree pkBytes msg (sigBytes.extract 0 7739) false
        agree pkBytes msg (sigBytes.push 0) false
        agree (pkBytes.push 0) msg sigBytes false
      | _ =>
        -- A counter has 4 bytes; every other field has 16.
        let start := fieldStarts[field]!
        let width := if start == 4240 || start == 5396 || start == 6552 then 32 else 128
        agree pkBytes msg (flipBit sigBytes (8 * start + bit % width)) false

/-- The fields of the digest are those of FIPS 205 Algorithm 19.

First come 24 leaves of 10 bits from the first 30 bytes, most significant bit first.

Then come a tree of 18 bits and a leaf of 8. -/
def digestFields : Property IO := pureIO do
  let bytes ← forAllWith hex (Gen.frequency [(1, pure (beBytes 34 0)),
    (1, pure ⟨Array.replicate 34 0xff⟩), (4, genBytesN 34)])
  let d : MessageDigest := Vector.ofFn fun i => bytes[i.val]!
  classify "every bit clear" (bytes.data.all (· == 0))
  classify "every bit set" (bytes.data.all (· == 0xff))
  classify "byte 30 has a bit above the 18 of the tree" (bytes[30]! ≥ 4)
  let md := beNat (bytes.extract 0 30)
  (digestLeaves d).toList.map (·.val) ===
    (List.range 24).map fun k => md >>> (10 * (23 - k)) % 1024
  digestTree d === beNat (bytes.extract 30 33) % 2 ^ 18
  digestLeaf d === bytes[33]!.toNat
  digestIndex d === beNat (bytes.extract 30 33) % 2 ^ 18 * 256 + bytes[33]!.toNat

end CurvesProperty.SphincsTest

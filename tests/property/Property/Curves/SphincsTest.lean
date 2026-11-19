import Property.Curves.Common
import EthLib.Cryptography.Sphincs

/-!
# leanSPHINCS: signing against verification

The reference is a model of verification (`oracle/curves_sphincs.py`), written from FIPS 205
and the formulas of the scheme, and checked against the vectors of the repository.
A signature of a key verifies, any single bit changed in the signature, the message or the
key is refused, as the model refuses it, and the fields of the digest are the bits that
FIPS 205 Algorithm 19 names.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.SphincsTest

open Sphincs

/-- The offsets where the fields of a signature start: the randomizer, each FORS opening and
its path nodes, then per layer the counter, the chain values and the siblings. -/
def fieldStarts : List Nat :=
  [0] ++ (List.range (24 * 11)).map (16 + 16 * ·) ++
    [(4240, 8), (5396, 8), (6552, 10)].flatMap fun (base, height) =>
      [base] ++ (List.range (64 + height)).map (base + 4 + 16 * ·)

/-- A key signs, the signature verifies and encodes to 7740 bytes that decode back, and a
signature, message or key with one bit changed, or of another length, is refused. -/
def signsAndVerifies (oracle : Oracle) : Property IO := propertyM do
  let (seed, msg) ← forAllWith (fun (a, b) => s!"{hex a} {hex b}")
    (Gen.zip (Gen.frequency [(1, pure (beBytes 32 0)), (3, genBytesN 32)])
      (Gen.frequency [(1, pure (beBytes 32 0)), (3, genBytesN 32)]))
  let changes ← forAll (Gen.list (.constant 4 8) (Gen.zip (Gen.nat (.constant 0 5))
    (Gen.zip (Gen.nat (.constant 0 (fieldStarts.length - 1))) (Gen.nat (.constant 0 127)))))
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
      got === (← oracle.ask ["sphincsverify", hex pkBytes, hex msg, hex sigBytes])
      ensure ((got == "1") == honest) "a changed input is accepted"
    agree pkBytes msg sigBytes true
    for (kind, field, bit) in changes do
      annotate s!"change {kind} {field} {bit}"
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

/-- The fields of the digest are those of FIPS 205 Algorithm 19: 24 leaves of 10 bits from
the first 30 bytes, most significant bit first, then a tree of 18 bits and a leaf of 8. -/
def digestFields : Property IO := pureIO do
  let bytes ← forAllWith hex (Gen.frequency [(1, pure (beBytes 34 0)),
    (1, pure ⟨Array.replicate 34 0xff⟩), (4, genBytesN 34)])
  let d : MessageDigest := Vector.ofFn fun i => bytes[i.val]!
  let md := beNat (bytes.extract 0 30)
  (digestLeaves d).toList.map (·.val) ===
    (List.range 24).map fun k => md >>> (10 * (23 - k)) % 1024
  digestTree d === beNat (bytes.extract 30 33) % 2 ^ 18
  digestLeaf d === bytes[33]!.toNat
  digestIndex d === beNat (bytes.extract 30 33) % 2 ^ 18 * 256 + bytes[33]!.toNat

end CurvesProperty.SphincsTest

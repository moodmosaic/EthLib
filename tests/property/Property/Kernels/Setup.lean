import Property.Kernels.Common
import EthLib.Cryptography.Kzg
import EthLib.Cryptography.HashSig
import EthLib.Cryptography.Wots

/-!
# The trusted setup of KZG, point by point, and the frame of the hash-based signatures

The setup is a table of 8,257 points, and a proof reads only a few of the 65 points of `G2`.

Each point is compared with the file of the ceremony that the consensus specifications ship.

The frame of the hash-based signatures is three loops that take their step as an argument.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace KernelsProperty.Setup

/-- Every point of the embedded setup is the point of the ceremony at the same index. -/
def ceremony (oracle : Oracle) : Property IO := propertyM do
  pure do
    let same (part : String) (table : Array String) : TestT IO Unit := do
      let want := words (← oracle.ask ["setup", part])
      table.size === want.length
      for (i, (got, want)) in (table.toList.zip want).zipIdx.map (fun (x, i) => (i, x)) do
        if got != want then failWith s!"{part}[{i}] is {got} and the ceremony has {want}"
    same "g1_lagrange" Kzg.TrustedSetupData.g1LagrangeHex
    same "g1_monomial" Kzg.TrustedSetupData.g1MonomialHex
    same "g2_monomial" Kzg.TrustedSetupData.g2MonomialHex

/-- The decoded setup holds the points of its text, the Lagrange points in bit-reversed order.

The Lagrange points sum to the generator, since the Lagrange polynomials sum to one.

The first monomial point of each group is its generator. -/
def decoded : Property IO := propertyM do
  let picks ← forAll (Gen.list (.singleton 24) (Gen.frequency [
    (1, Gen.element [0, 1, 2, 4095, 4094, 2048, 2047]), (2, Gen.nat (.constant 0 4095))]))
  pure do
    match Kzg.TrustedSetup.ofHex with
    | .error _ => failWith "the embedded setup does not decode"
    | .ok setup =>
      let hexOf {n : Nat} (v : Vector UInt8 n) : String := hex ⟨v.toArray⟩
      for i in picks do
        -- Bit `b` of the index moves to bit `11 - b`.
        let j := (List.range 12).foldl (fun acc b => acc * 2 + i / 2 ^ b % 2) 0
        hexOf (Bls.G1.compress setup.g1LagrangeBrp[i]!) === Kzg.TrustedSetupData.g1LagrangeHex[j]!
        hexOf (Bls.G1.compress setup.g1Monomial[i]!) === Kzg.TrustedSetupData.g1MonomialHex[i]!
      for i in List.range 65 do
        hexOf (Bls.G2.compress setup.g2Monomial[i]!) === Kzg.TrustedSetupData.g2MonomialHex[i]!
      let sum := setup.g1LagrangeBrp.foldl (· + ·) (Bls.G1.zero : Bls.G1)
      hexOf (Bls.G1.compress sum) === hexOf (Bls.G1.compress (Bls.G1.generator : Bls.G1))
      hexOf (Bls.G1.compress setup.g1Monomial[0]!) ===
        hexOf (Bls.G1.compress (Bls.G1.generator : Bls.G1))
      hexOf (Bls.G2.compress setup.g2Monomial[0]!) ===
        hexOf (Bls.G2.compress (Bls.G2.generator : Bls.G2))

/-- The three loops of the hash-based signatures, with a step that records where it ran.

A chain of `steps` steps from `start` runs the positions `start` to `start + steps - 1` in order.

The search returns the first trial from `c` that passes, among at most `fuel` trials.

A vector computed in order runs index 0 first. -/
def frame : Property IO := pureIO do
  let n ← forAll (Gen.nat (.constant 0 20))
  let start ← forAll (Gen.nat (.constant 0 (n / 2)))
  let steps ← forAll (Gen.frequency [
    (2, pure (n - start)), (1, pure 0), (5, Gen.nat (.constant 0 (n - start)))])
  classify "the chain is empty" (steps == 0)
  classify "the chain reaches the last position" (start + steps == n && steps > 0)
  if h : start + steps ≤ n then
    let step (k : Fin n) (seen : List Nat) : StateM Nat (List Nat) := do
      modify (· + 1)
      pure (seen ++ [k.val])
    let (seen, calls) := (Wots.chain step start steps h []).run 0
    seen === (List.range steps).map (start + ·)
    calls === steps
  -- The search.
  let passing ← forAll (Gen.list (.linear 0 4) (Gen.nat (.constant 0 12)))
  let c ← forAll (Gen.nat (.constant 0 12))
  let fuel ← forAll (Gen.nat (.constant 0 12))
  let test (k : Nat) : StateM Nat (Option Nat) := do
    modify (· + 1)
    pure (if passing.contains k then some (k * 10) else none)
  let (found, tried) := (Wots.findFirst (fun i => i) test c fuel).run 0
  let want := (List.range fuel).map (c + ·) |>.find? passing.contains
  classify "a trial passes" want.isSome
  classify "no trial passes within the fuel" want.isNone
  found === want.map fun k => (k, k * 10)
  tried === (match want with
    | some k => k - c + 1
    | none => fuel)
  -- A vector in order.
  let (vector, order) := (HashSig.ofFnInOrder (m := StateM (List Nat)) n fun i => do
    modify (· ++ [i.val])
    pure (i.val * 3)).run []
  vector.toList === (List.range n).map (· * 3)
  order === List.range n
  -- A read of a fixed-size object.
  let buffer ← forAllWith bytesHex (Gen.bytes (.constant 0 12))
  let offset ← forAll (Gen.nat (.constant 0 (buffer.size + 1)))
  let size ← forAll (Gen.frequency [
    (2, pure (buffer.size - offset)), (1, pure (buffer.size - offset + 1)),
    (3, Gen.nat (.constant 0 (buffer.size + 1)))])
  classify "the object ends at the end of the buffer" (offset + size == buffer.size)
  classify "the buffer is short" (offset + size > buffer.size)
  (HashSig.unpackBytes? size buffer offset).map (·.toList) ===
    (if offset + size ≤ buffer.size then some ((buffer.toList.drop offset).take size) else none)

end KernelsProperty.Setup

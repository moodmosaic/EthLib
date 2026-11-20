import Property.Curves.Common
import EthLib.Cryptography.Vrf

/-!
# The VRF tree against a model of EIP-8450's `vrf.Verify`

The model hashes a leaf, climbs 32 siblings by the bits of the index, and hashes the output.

A tree of `2^32` leaves cannot be built.

So an opening is a secret and 32 siblings of any values, and the root is the one they lead to.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.VrfTest

open Vrf

/-- An index at the edges of 32 bits. -/
def genIndex : Gen Nat :=
  Gen.frequency [(2, Gen.nat (.linear 0 4)), (1, Gen.element [2 ^ 31, 2 ^ 32 - 2, 2 ^ 32 - 1]),
    (3, Gen.nat (.constant 0 (2 ^ 32 - 1)))]

/-- One change to a root, an index and an opening that verify. -/
inductive Change where
  | none
  | openingBit (bit : Nat)
  | rootBit (bit : Nat)
  | indexBit (bit : Nat)
  | indexPast (extra : Nat)
  | openingSize (delta : Int)
  | rootSize (delta : Int)
  | swapSiblings (i : Nat)
  deriving Repr, BEq

def genChange : Gen Change :=
  Gen.frequency [
    (3, pure .none),
    (3, .openingBit <$> Gen.frequency [(1, Gen.nat (.constant 0 255)),
      (2, Gen.nat (.constant 0 (8 * 1056 - 1)))]),
    (1, .rootBit <$> Gen.nat (.constant 0 255)),
    (3, .indexBit <$> Gen.nat (.constant 0 31)),
    (1, .indexPast <$> Gen.element [0, 1, 2 ^ 32]),
    (1, .openingSize <$> Gen.element [-1, 1, -32, 32]),
    (1, .rootSize <$> Gen.element [-1, 1]),
    (1, .swapSiblings <$> Gen.nat (.constant 0 30))]

/-- The name of a change, for a label. -/
def Change.name : Change → String
  | .none => "nothing"
  | .openingBit bit => if bit < 256 then "a bit of the secret" else "a bit of a sibling"
  | .rootBit _ => "a bit of the root"
  | .indexBit _ => "a bit of the index"
  | .indexPast _ => "an index of 2^32 or more"
  | .openingSize _ => "the length of the opening"
  | .rootSize _ => "the length of the root"
  | .swapSiblings _ => "two siblings exchanged"

/-- Verification returns the output of the model, or nothing where the model refuses:

- A changed secret, sibling, root or index.
- An index from `2^32` on.
- A wrong length. -/
def verifies (oracle : Oracle) : Property IO := propertyM do
  let opening ← forAllWith hex (genBytesN 1056)
  let index ← forAll genIndex
  let change ← forAll genChange
  pure do
    let .some root := unhex? (← oracle.ask ["vrfroot", toString index, hex opening])
      | failWith "no root"
    let resize (bytes : ByteArray) (delta : Int) : ByteArray :=
      if delta ≥ 0 then bytes ++ ⟨Array.replicate delta.toNat 0⟩
      else bytes.extract 0 (bytes.size - (-delta).toNat)
    let (root, index, opening) := match change with
      | .none => (root, index, opening)
      | .openingBit bit => (root, index, flipBit opening bit)
      | .rootBit bit => (flipBit root bit, index, opening)
      | .indexBit bit => (root, index ^^^ (1 <<< bit), opening)
      | .indexPast extra => (root, index % 2 + 2 ^ 32 + extra, opening)
      | .openingSize delta => (root, index, resize opening delta)
      | .rootSize delta => (resize root delta, index, opening)
      | .swapSiblings i =>
        let at_ (k : Nat) := opening.extract (32 + 32 * k) (64 + 32 * k)
        (root, index, opening.extract 0 (32 + 32 * i) ++ at_ (i + 1) ++ at_ i ++
          opening.extract (96 + 32 * i) 1056)
    let got := match verifyBytes root index opening with
      | some output => hexVec output
      | none => "none"
    label s!"changed: {change.name}"
    classify "accepted" (got != "none")
    classify "accepted after a change" (got != "none" && change != .none)
    classify "refused" (got == "none")
    classify "the index 0, a left child at every level" (index == 0)
    classify "the index 2^32 - 1, a right child at every level" (index == 2 ^ 32 - 1)
    classify "an index of 2^31 or more, the last level" (2 ^ 31 ≤ index && index < 2 ^ 32)
    if let .openingBit bit := change then
      if bit ≥ 256 then label s!"a bit of sibling {(bit / 256 - 1) / 8 * 8} to +7"
    got === (← oracle.ask ["vrfverify", hex root, toString index, hex opening])
    if change == .none then ensure (got != "none") "a valid opening is refused"
    -- An opening of 1056 bytes decodes, and encodes back.
    match decodeOpening opening with
    | some o => hex (encodeOpening o) === hex opening
    | none => ensure (opening.size != 1056) "an opening of 1056 bytes does not decode"

/-- The secret and the output of a seed at an index are the hashes of the specification.

So is a mixed value. -/
def hashes (oracle : Oracle) : Property IO := propertyM do
  let (seed, randomness) ← forAllWith (fun (a, b) => s!"{hex a} {hex b}")
    (Gen.zip (genBytesN 32) (genBytesN 32))
  let index ← forAll genIndex
  classify "the index 0" (index == 0)
  classify "the index 2^32 - 1" (index == 2 ^ 32 - 1)
  classify "an index of 2^24 or more, four bytes" (index ≥ 2 ^ 24)
  pure do
    let v (b : ByteArray) : Vector UInt8 32 := Vector.ofFn fun i => b[i.val]!
    let i := UInt32.ofNat index
    let got := s!"{hexVec (secret (v seed) i)} {hexVec (evaluate (v seed) i)}"
    got === (← oracle.ask ["vrfsecret", hex seed, toString index])
    let output := evaluate (v seed) i
    hexVec (mixOutput output (v randomness)) === (← oracle.ask ["vrfmix", hexVec output,
      hex randomness])

end CurvesProperty.VrfTest

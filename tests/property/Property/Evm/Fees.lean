import Property.Evm.Run
import EthLib.Execution.Fees

/-!
# The fee functions beside the reference

The base fee of EIP-1559, `fake_exponential` of EIP-4844, the blob gas price and the excess blob
gas of each fork from Dencun, with the reserve price of EIP-7918 from Fusaka.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution.Fees

namespace EvmProperty

/-- The forks with a base fee, each with the name of its module in the reference. -/
def baseFeeForks : List (Fork × String) := forks.drop 12

/-- The forks with blob gas. -/
def blobForks : List (Fork × String) := forks.drop 19

/-- A number near another: below it, at it and above it. -/
def genNear (n : Nat) : Gen Nat :=
  Gen.frequency [(2, pure n), (2, (n + ·) <$> Gen.nat (.linear 0 4)),
    (2, (n - ·) <$> Gen.nat (.linear 0 4)), (1, Gen.nat (.linear 0 (2 * n + 1)))]

/-- The base fee of a child is the reference's, for a parent below, at and above its target. -/
def baseFee (oracle : Oracle) : Property IO := propertyM do
  let limit ← forAll (Gen.frequency [(3, Gen.nat (.exponential 5000 (2 ^ 40))),
    (2, Gen.element [5000, 5001, 30000000, 36000001, 2 ^ 63 - 1])])
  let used ← forAll (Gen.frequency [(3, genNear (limit / 2)), (1, genNear limit), (1, pure 0),
    (1, Gen.nat (.linear 0 limit))])
  let fee ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 20)), (2, genNatBits 64),
    (1, Gen.element [7, 8, 10 ^ 9, 2 ^ 255])])
  let fork ← forAllWith (·.2) (Gen.element baseFeeForks)
  pure do
    let want ← oracle.ask ["basefee", fork.2, toString limit, toString used, toString fee]
    toString (BaseFee.calculateBaseFeePerGas limit used fee) === want

/-- A gas limit may follow its parent's exactly when the reference says so.

The bounds are strict, a 1024th of the parent's limit away, and the limit is at least 5000. -/
def gasLimitRule (oracle : Oracle) : Property IO := propertyM do
  let parent ← forAll (Gen.frequency [(2, Gen.nat (.linear 0 12000)),
    (2, Gen.element [1023, 1024, 1025, 4996, 4997, 5000, 5120, 30000000]),
    (2, Gen.nat (.exponential 0 (2 ^ 40)))])
  let delta := parent / 1024
  let limit ← forAll (Gen.frequency [(3, genNear (parent + delta)), (3, genNear (parent - delta)),
    (1, genNear parent), (2, genNear 5000)])
  let fork ← forAllWith (·.2) (Gen.element forks)
  pure do
    let want ← oracle.ask ["gaslimit", fork.2, toString limit, toString parent]
    (if GasLimit.checkGasLimit limit parent then "1" else "0") === want

/-- `fakeExponential` is `fake_exponential` of EIP-4844, on any factor and numerator, and any
denominator but zero. -/
def fakeExponential (oracle : Oracle) : Property IO := propertyM do
  let factor ← forAll (Gen.frequency [(2, pure 1), (1, Gen.nat (.exponential 0 (2 ^ 64)))])
  let denominator ← forAll (Gen.frequency [(2, Gen.element [3338477, 5007716, 8346193, 11684671]),
    (1, Gen.nat (.exponential 1 (2 ^ 40)))])
  -- The loop of the EIP runs about `numerator / denominator` times, so the ratio stays modest.
  let ratio ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 60)), (1, Gen.nat (.linear 0 3000))])
  let rest ← forAll (Gen.nat (.linear 0 (denominator - 1)))
  pure do
    let numerator := ratio * denominator + rest
    let want ← oracle.ask ["taylor", toString factor, toString numerator, toString denominator]
    toString (BlobBaseFee.fakeExponential factor numerator denominator) === want

/-- A parent's excess and blob gas around the target and the maximum of a fork. -/
def genBlobParent (schedule : BlobSchedule) : Gen (Nat × Nat) := do
  let blob := BlobBaseFee.GAS_PER_BLOB
  let used ← Gen.frequency [(4, (· * blob) <$> Gen.nat (.constant 0 schedule.max)),
    (1, genNear (schedule.target * blob))]
  let excess ← Gen.frequency [(2, genNear (schedule.target * blob - used)),
    (2, (· * blob) <$> Gen.nat (.linear 0 400)), (1, Gen.nat (.exponential 0 (2 ^ 31))),
    (1, pure 0)]
  pure (excess, used)

/-- The excess blob gas and the blob gas price are the reference's at each fork from Dencun.

From Fusaka the base fee of the parent decides between the two rules of EIP-7918. -/
def blobGas (oracle : Oracle) : Property IO := propertyM do
  let fork ← forAllWith (·.2) (Gen.element blobForks)
  if h : .dencun ≤ fork.1 then
    let schedule := BlobBaseFee.blobSchedule fork.1 h
    let (excess, used) ← forAll (genBlobParent schedule)
    let fee ← forAll (Gen.frequency [(3, Gen.nat (.exponential 0 (10 ^ 12))),
      (2, Gen.nat (.linear 0 64)),
      -- The base fee at which the reserve price of EIP-7918 meets the blob base fee.
      (3, genNear (BlobBaseFee.GAS_PER_BLOB * BlobBaseFee.getBaseFeePerBlobGas schedule excess /
        BlobBaseFee.BLOB_BASE_COST))])
    pure do
      let want ← oracle.ask ["excess", fork.2, toString excess, toString used, toString fee]
      toString (BlobBaseFee.calcExcessBlobGas fork.1 schedule excess used fee) === want
      let price ← oracle.ask ["blobfee", fork.2, toString excess]
      toString (BlobBaseFee.getBaseFeePerBlobGas schedule excess) === price
  else pure (pure ())

end EvmProperty

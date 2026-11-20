import Property.Evm.Run
import EthLib.Execution.Fees

/-!
# The fee functions beside the reference

The base fee of EIP-1559 and `fake_exponential` of EIP-4844.

Also the blob gas price and the excess blob gas of each fork from Dencun.

From Fusaka they come with the reserve price of EIP-7918.
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
def baseFee (oracle : Oracle) (asked : Bool) : Property IO := propertyM do
  -- The reference refuses a limit under 5000 before it computes, so none is drawn.
  let limit ← forAll (Gen.frequency [(3, Gen.nat (.exponential 5000 (2 ^ 40))),
    (2, Gen.element [5000, 5001, 30000000, 36000001, 2 ^ 63 - 1])])
  let used ← forAll (Gen.frequency [(3, genNear (limit / 2)), (1, genNear limit), (1, pure 0),
    (1, Gen.nat (.linear 0 limit))])
  let fee ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 20)), (2, genNatBits 64),
    (1, Gen.element [7, 8, 10 ^ 9, 2 ^ 255])])
  let fork ← forAllWith (·.2) (Gen.element baseFeeForks)
  pure do
    let target := limit / 2
    let got := BaseFee.calculateBaseFeePerGas limit used fee
    label (if used = target then "the parent is at its target"
      else if used > target then "the parent is above its target"
      else "the parent is below its target")
    classify "one above the target" (used = target + 1)
    classify "one below the target" (used + 1 = target)
    classify "the parent is full" (used = limit)
    classify "the parent is empty" (used = 0)
    classify "the rise is the least, 1" (used > target ∧ got = fee + 1)
    classify "the rise is more than 1" (used > target ∧ got > fee + 1)
    classify "the fall is 0" (used < target ∧ got = fee)
    classify "the fall is more than 0" (used < target ∧ got < fee)
    classify "the rise is an eighth, the most" (used = limit ∧ limit % 2 = 0 ∧ fee ≥ 8)
    classify "a base fee of 0" (fee = 0)
    let least (percent : Nat) : Nat := if asked then percent else 0
    cover (least 8) "the parent is above its target" (used > target)
    cover (least 8) "the parent is below its target" (used < target)
    cover (least 8) "the parent is at its target" (used = target)
    cover (least 1) "one above the target" (used = target + 1)
    cover (least 1) "one below the target" (used + 1 = target)
    cover (least 3) "the rise is more than 1" (used > target ∧ got > fee + 1)
    cover (least 5) "the fall is more than 0" (used < target ∧ got < fee)
    let want ← oracle.ask ["basefee", fork.2, toString limit, toString used, toString fee]
    toString got === want

/-- A gas limit may follow its parent's exactly when the reference says so.

The bounds are strict, a 1024th of the parent's limit away, and the limit is at least 5000. -/
def gasLimitRule (oracle : Oracle) (asked : Bool) : Property IO := propertyM do
  let parent ← forAll (Gen.frequency [(2, Gen.nat (.linear 0 12000)),
    (2, Gen.element [1023, 1024, 1025, 4996, 4997, 5000, 5120, 30000000]),
    (2, Gen.nat (.exponential 0 (2 ^ 40)))])
  let delta := parent / 1024
  let limit ← forAll (Gen.frequency [(3, genNear (parent + delta)), (3, genNear (parent - delta)),
    (2, genNear parent), (2, genNear 5000),
    -- A limit strictly inside the bounds.
    (4, (parent - delta + 1 + ·) <$> Gen.nat (.constant 0 (2 * delta - 2)))])
  let fork ← forAllWith (·.2) (Gen.element forks)
  pure do
    let got := GasLimit.checkGasLimit limit parent
    label (if got then "accepted"
      else if limit ≥ parent + delta then "refused: too high"
      else if limit + delta ≤ parent then "refused: too low"
      else "refused: below 5000")
    classify "at the upper bound, refused" (limit = parent + delta)
    classify "one below the upper bound" (limit + 1 = parent + delta)
    classify "at the lower bound, refused" (limit + delta = parent)
    classify "one above the lower bound" (limit = parent - delta + 1)
    classify "at 5000" (limit = 5000)
    classify "at 4999" (limit = 4999)
    classify "the limit of the parent" (limit = parent)
    classify "a parent below 1024, with no room" (parent < 1024)
    let least (percent : Nat) : Nat := if asked then percent else 0
    cover (least 8) "accepted" got
    cover (least 5) "refused: too high" (!got ∧ limit ≥ parent + delta)
    cover (least 5) "refused: too low" (!got ∧ limit + delta ≤ parent)
    cover (least 1) "refused: below 5000 alone" (!got ∧ limit < 5000 ∧
      limit < parent + delta ∧ parent < limit + delta)
    cover (least 1) "one below the upper bound" (limit + 1 = parent + delta)
    cover (least 1) "one above the lower bound" (limit = parent - delta + 1)
    let want ← oracle.ask ["gaslimit", fork.2, toString limit, toString parent]
    (if got then "1" else "0") === want

/-- `fakeExponential` is `fake_exponential` of EIP-4844.

This holds on any factor and numerator, and any denominator but zero. -/
def fakeExponential (oracle : Oracle) : Property IO := propertyM do
  let factor ← forAll (Gen.frequency [(2, pure 1), (1, Gen.nat (.exponential 0 (2 ^ 64)))])
  let denominator ← forAll (Gen.frequency [(2, Gen.element [3338477, 5007716, 8346193, 11684671]),
    (1, Gen.nat (.exponential 1 (2 ^ 40)))])
  -- The loop of the EIP runs about `numerator / denominator` times, so the ratio stays modest.
  let ratio ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 60)), (1, Gen.nat (.linear 0 3000))])
  let rest ← forAll (Gen.nat (.linear 0 (denominator - 1)))
  pure do
    let numerator := ratio * denominator + rest
    label (if factor = 0 then "factor 0" else if factor = 1 then "factor 1" else "factor above 1")
    label (if numerator = 0 then "numerator 0" else if ratio = 0 then "ratio below 1"
      else if ratio ≤ 60 then "ratio 1 to 60" else "ratio above 60")
    classify "a denominator of 1" (denominator = 1)
    classify "a denominator of a fork" ([3338477, 5007716, 8346193, 11684671].contains denominator)
    let want ← oracle.ask ["taylor", toString factor, toString numerator, toString denominator]
    toString (BlobBaseFee.fakeExponential factor numerator denominator) === want

/-- A parent's excess and blob gas around the target and the maximum of a fork. -/
def genBlobParent (schedule : BlobSchedule) : Gen (Nat × Nat) := do
  let blob := BlobBaseFee.GAS_PER_BLOB
  let used ← Gen.frequency [(4, (· * blob) <$> Gen.nat (.constant 0 schedule.max)),
    (1, genNear (schedule.target * blob))]
  -- An excess of twenty update fractions gives a price in the hundreds of millions.
  let excess ← Gen.frequency [(2, genNear (schedule.target * blob - used)),
    (2, (· * blob) <$> Gen.nat (.linear 0 400)), (1, Gen.nat (.exponential 0 (2 ^ 31))),
    (3, Gen.nat (.linear 0 (20 * schedule.baseFeeUpdateFraction))), (1, pure 0)]
  pure (excess, used)

/-- The excess blob gas and the blob gas price are the reference's at each fork from Dencun.

From Fusaka the base fee of the parent decides between the two rules of EIP-7918. -/
def blobGas (oracle : Oracle) (asked : Bool) : Property IO := propertyM do
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
      let blob := BlobBaseFee.GAS_PER_BLOB
      let target := blob * schedule.target
      let reserve := decide (BlobBaseFee.BLOB_BASE_COST * fee >
        blob * BlobBaseFee.getBaseFeePerBlobGas schedule excess)
      label s!"at {fork.2}"
      label (if excess + used < target then "below the target: the excess is 0"
        else if fork.1 ≥ .fusaka ∧ reserve then "the reserve price of EIP-7918 rules"
        else if excess + used = target then "at the target: the excess is 0"
        else "above the target: the rule of EIP-4844")
      classify "one below the target" (excess + used + 1 = target)
      classify "the parent used the most blobs" (used = blob * schedule.max)
      classify "the parent used no blob" (used = 0)
      classify "an excess of 0 in the parent" (excess = 0)
      classify "the blob gas price is 1" (BlobBaseFee.getBaseFeePerBlobGas schedule excess = 1)
      classify "the reserve price meets the blob base fee" (BlobBaseFee.BLOB_BASE_COST * fee =
        blob * BlobBaseFee.getBaseFeePerBlobGas schedule excess)
      let least (percent : Nat) : Nat := if asked then percent else 0
      cover (least 5) "below the target" (excess + used < target)
      cover (least 5) "the reserve price of EIP-7918 rules"
        (excess + used ≥ target ∧ fork.1 ≥ .fusaka ∧ reserve)
      cover (least 10) "the rule of EIP-4844"
        (excess + used ≥ target ∧ !(fork.1 ≥ .fusaka ∧ reserve))
      cover (least 10) "a blob gas price above 1"
        (BlobBaseFee.getBaseFeePerBlobGas schedule excess > 1)
      let want ← oracle.ask ["excess", fork.2, toString excess, toString used, toString fee]
      toString (BlobBaseFee.calcExcessBlobGas fork.1 schedule excess used fee) === want
      let price ← oracle.ask ["blobfee", fork.2, toString excess]
      toString (BlobBaseFee.getBaseFeePerBlobGas schedule excess) === price
  else pure (pure ())

end EvmProperty

import Property.Transition.World

/-!
# The size of a block

From Fusaka, the RLP form of a block has at most 8 MiB, as EIP-7934 asks.

No generated block of the other properties comes near that size.

Here a block holds one byte string that brings it to the limit, one byte under or one byte over.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Blocks
open EthLib.Serialization.Rlp
open EvmProperty (word32)

namespace TransitionProperty

/-- The most bytes of the RLP form of a block: 10 MiB minus a margin of 2 MiB, by EIP-7934. -/
def mostBlockBytes : Nat := 10 * 1024 * 1024 - 2 * 1024 * 1024

/-- A header at a fork with small fields, which only its size matters for. -/
def plainHeader (fork : Fork) : Header fork where
  parentHash := word32 1
  ommersHash := word32 2
  coinbase := numberAddress 3
  stateRoot := word32 4
  transactionsRoot := word32 5
  receiptRoot := word32 6
  bloom := Vector.replicate 256 0
  difficulty := 0
  number := 7
  gasLimit := 30000000
  gasUsed := 0
  timestamp := 8
  extraData := .empty
  prevRandao := word32 9
  nonce := Vector.replicate 8 0
  baseFeePerGas := fun _ => 7
  withdrawalsRoot := fun _ => word32 10
  blobGasUsed := fun _ => 0
  excessBlobGas := fun _ => 0
  parentBeaconBlockRoot := fun _ => word32 11
  requestsHash := fun _ => word32 12
  blockAccessListHash := fun _ => word32 13
  slotNumber := fun _ => 14

/-- A block whose one transaction is a byte string of a length. -/
def paddedBlock (fork : Fork) (length : Nat) : Block fork Item :=
  ⟨plainHeader fork, [.bytes ⟨Array.replicate length 0x5a⟩], [], fun _ => []⟩

/-- A block passes the size rule exactly when it has at most 8 MiB, from Fusaka.

Before Fusaka no size is refused.

The block is padded to the limit, or to a few bytes under or over it. -/
def blockSize : Property IO := propertyM do
  let fork ← forAllWith (·.name) (Gen.element [.frontier, .paris, .dencun, .pectra, .fusaka,
    .bpo1, .bpo2, .bpo5, .glamsterdam])
  let over ← forAll (Gen.element ([0, 1, -1, 2, -2, 1000, -1000] : List Int))
  pure do
    -- The size of a block grows by one byte with its padding, at this length.
    let size (length : Nat) : Nat :=
      ((paddedBlock fork length).encode.toOption.map (·.size)).getD 0
    let length := ((8000000 + (mostBlockBytes - size 8000000) : Nat) + over).toNat
    let block := paddedBlock fork length
    let bytes := size length
    bytes === ((mostBlockBytes : Int) + over).toNat
    let accepted := (validateBlockSize block).toBool
    classify "over the limit from Fusaka, refused" (fork ≥ .fusaka ∧ over > 0)
    classify "at the limit or under it, accepted" (over ≤ 0)
    classify "over the limit before Fusaka, accepted" (fork < .fusaka ∧ over > 0)
    accepted === (fork < .fusaka || decide (bytes ≤ mostBlockBytes))

end TransitionProperty

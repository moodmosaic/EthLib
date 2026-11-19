import Property.Consensus.Operations
import EthLib.Consensus.Transition.Genesis

/-!
# Genesis from the deposits of the proof-of-work chain

The oracle builds the deposits, each with its proof against the tree of the deposits so far, and
the genesis state of consensus-specs.
EthLib must build the state of the same root, and agree on whether it launches the chain.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus EthLib.Serialization.Ssz

namespace ConsensusProperty

/-- The bytes of one deposit: a proof of 33 nodes and the deposit data. -/
def depositSize : Nat := 33 * 32 + 184

/-- The deposits of a concatenation of their SSZ bytes. -/
def depositsOf (bytes : ByteArray) : Except Err (Array Deposit) :=
  (List.range (bytes.size / depositSize)).toArray.mapM fun i =>
    SszType.deserialize Deposit (bytes.extract (i * depositSize) ((i + 1) * depositSize))

/-- A deposit at genesis: mostly 32 ETH for a new key, sometimes a top-up or a bad signature. -/
def genGenesisDeposit : Gen String :=
  (",".intercalate ·) <$> genFields [
    num (Gen.frequency [(6, Gen.nat (.linear 0 80)), (1, Gen.nat (.linear 0 3))]),
    num (Gen.element [1, 0]),
    num (Gen.nat (.linear 0 5)),
    num (Gen.frequency [(8, pure (32 * increment)),
      (2, (· * increment) <$> Gen.nat (.linear 0 40)),
      (1, Gen.element [32 * increment - 1, 32 * increment + 1, 31 * increment + increment / 2])]),
    num (Gen.frequency [(9, pure 1), (1, pure 0)])]

/-- The genesis state of generated deposits is that of consensus-specs, and launches as there. -/
def genesis (oracle : Oracle) : Property IO := propertyM do
  let timestamp ← forAll (Gen.frequency [
    -- Around the earliest genesis time less the delay, of the minimal configuration.
    (4, (1578009600 - 300 + · - 2) <$> Gen.nat (.constant 0 4)),
    (2, Gen.nat (.linear 0 2000000000)),
    (1, (2 ^ 64 - 1 - ·) <$> Gen.nat (.linear 0 400))])
  let deposits ← forAll (Gen.frequency [
    (4, Gen.list (.linear 0 12) genGenesisDeposit),
    -- Enough validators to launch the minimal chain, or just short of it.
    (1, Gen.list (.constant 62 68) genGenesisDeposit)])
  pure do
    let answer ← oracle.ask (["pure", "genesis", toString timestamp] ++ deposits)
    match answer.splitOn " " with
    | [sent, expected] =>
      let some bytes := unhex? sent | failWith "the oracle sent no deposits"
      match depositsOf bytes with
      | .error e => failWith s!"EthLib does not read the deposits: {repr e}"
      | .ok read =>
        let result : Except TransitionError (State .phase0) :=
          initializeBeaconStateFromEth1 Config.minimal checks
            (Vector.ofFn fun i : Fin 32 => (Cryptography.Hash.sha256 "eth1".toUTF8)[i.val]!)
            (UInt64.ofNat timestamp) read
        match result with
        | .error e =>
          ensure (expected.startsWith "error")
            s!"EthLib refuses ({repr e}), the reference answers {expected}"
        | .ok state =>
          match SszType.hashTreeRoot state with
          | .error _ => failWith "EthLib cannot hash its genesis state"
          | .ok root =>
            s!"ok:{hexVector root}:{showBool (isValidGenesisState Config.minimal state)}" ===
              expected
    | _ => failWith s!"the oracle answered: {answer.take 300}"

end ConsensusProperty

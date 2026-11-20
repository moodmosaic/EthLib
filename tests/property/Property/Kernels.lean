import Property.Kernels.Base
import Property.Kernels.Chain
import Property.Kernels.Curves
import Property.Kernels.Hashes
import Property.Kernels.Kdf
import Property.Kernels.Montgomery
import Property.Kernels.Setup
import Property.Kernels.TowerScenario
import Property.Kernels.Unicode

/-!
# The fundamental primitives, at every parameter

Each kernel is run at every value of its parameters, not only at those the protocol uses today.

    lake exe kernels-property            # 100 cases of each
    lake exe kernels-property 1000
    HEDGEHOG_ONLY=montgomery lake exe kernels-property 1000
-/

open Hedgehog Support EthLib EthLib.Cryptography KernelsProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let select ← Selection.fromEnv
  let gen8 := Mont.genModulus 8 Mont.named8
  let gen12 := Mont.genModulus 12 Mont.named12
  let montgomery ← checkGroup "kernels: Montgomery arithmetic" [
    ("montgomery machine: any modulus of 8 limbs",
      Mont.covered cases true ((Mont.machine 8 gen8 (Mont.mkModulus 8)).property.withTests cases)),
    ("montgomery machine: any modulus of 12 limbs",
      Mont.covered cases true
        ((Mont.machine 12 gen12 (Mont.mkModulus 12)).property.withTests cases)),
    ("montgomery machine: the field of secp256k1",
      Mont.covered cases true ((Mont.machine 8 (pure Secp256k1.Fp.modulus)
        (fun _ => some Secp256k1.Fp.params)).property.withTests cases)),
    ("montgomery machine: Fr of BLS12-381",
      Mont.covered cases false ((Mont.machine 8 (pure Bls.Fr.modulus)
        (fun _ => some Bls.Fr.params)).property.withTests cases)),
    ("montgomery machine: Fp of BLS12-381",
      Mont.covered cases false ((Mont.machine 12 (pure Bls.Fp.modulus)
        (fun _ => some Bls.Fp.params)).property.withTests cases)),
    ("montgomery bytes: any modulus of 8 limbs", (Mont.bytes 8 gen8).withTests cases),
    ("montgomery bytes: any modulus of 12 limbs", (Mont.bytes 12 gen12).withTests cases),
    ("montgomery words: the product on 1 to 16 limbs", withMinimums cases
      [(5, "the final subtraction fired")] (Mont.wordsProduct.withTests cases)),
    ("montgomery split: 8 limbs at every row", withMinimums cases [(15, "2 p ≤ R")]
      ((Mont.split 8 gen8).withTests cases)),
    ("montgomery split: 12 limbs at every row", withMinimums cases [(15, "2 p ≤ R")]
      ((Mont.split 12 gen12).withTests cases))]
    select
  let oracle ← Oracle.start "kernels"
  let chain ← checkGroup "kernels: forks and chain configurations" [
    ("fork order and comparison", (Chain.forkOrder oracle).withTests cases),
    ("fork names read back", Chain.forkNames.withTests cases),
    ("active fork: mainnet", withMinimums cases [(25, "on an activation or one before it"),
      (20, "a fork by timestamp is active")]
      ((Chain.activeNamed oracle "mainnet" .mainnet).withTests cases)),
    ("active fork: hoodi, before the time it gives Glamsterdam",
      (Chain.activeNamed oracle "hoodi" .hoodi (before := some 1793036568)).withTests cases),
    ("network constants: mainnet", (Chain.networkConstants oracle "mainnet" .mainnet).withTests 1),
    ("network constants: hoodi, without Glamsterdam",
      (Chain.networkConstants oracle "hoodi" .hoodi (without := [.glamsterdam])).withTests 1),
    ("active fork: generated configurations", withMinimums cases [(8, "no fork is active"),
      (12, "two reached forks share an activation"), (25, "the configuration is ordered")]
      (Chain.activeGenerated.withTests cases)),
    ("blob schedule of a chain at a block", withMinimums cases [(15, "the chain sets a schedule"),
      (15, "the chain sets none"), (3, "two reached schedules share an activation")]
      (Chain.blobScheduleAt.withTests cases)),
    ("blob schedule of every fork", (Chain.blobSchedules oracle).withTests cases)]
    select
  let base ← checkGroup "kernels: the base layer" [
    ("base: big-endian bytes at any width", withMinimums cases [(15, "the number fits"),
      (18, "the number does not fit")] (Base.bigEndian.withTests cases)),
    ("base: little-endian bytes at any width", withMinimums cases [(15, "the number fits"),
      (18, "the number does not fit")] (Base.littleEndian.withTests cases)),
    ("base: 32-bit word helpers", Base.words32.withTests cases),
    ("base: a word, its bytes, its address", Base.word.withTests cases),
    ("base: an integer as a signed word", Base.fromSigned.withTests cases),
    ("base: byte strings", withMinimums cases [(8, "the second string is shorter"),
      (8, "the second string is longer")] (Base.byteStrings.withTests cases)),
    ("base: hexadecimal", withMinimums cases [(10, "the width is below the digits"),
      (7, "the width is the digits"), (14, "the width is above the digits")]
      (Base.hexadecimal.withTests cases)),
    ("base: bounds on a length", Base.lengths.withTests cases),
    ("base: 64-bit helpers", Base.uint64.withTests cases),
    ("base: the gas limit toward a target", withMinimums cases [
      (9, "the target is above the step"), (9, "the target is below the step"),
      (5, "the target is exactly one step away"), (5, "the target is one past the step")]
      ((Base.gasLimit oracle).withTests cases))]
    select
  let hashes ← checkGroup "kernels: hash internals" [
    ("tables: every constant of the hashes and of AES", (Hashes.tables oracle).withTests 1),
    ("sha256: compression on any state", (Hashes.shaCompress oracle).withTests cases),
    ("ripemd160: compression on any state", (Hashes.ripemdCompress oracle).withTests cases),
    ("keccak: steps, rounds and permutation on any state",
      (Hashes.keccakPermutation oracle).withTests cases),
    ("keccak: the sponge at every rate", withMinimums cases [
      (9, "the rate is above 136 bytes"), (9, "the rate is below 72 bytes"),
      (7, "the message fills its last block"), (17, "the message has several blocks")]
      ((Hashes.keccakSponge oracle).withTests cases)),
    ("keccak: the padding at every rate", (Hashes.keccakPadding oracle).withTests cases),
    ("keccak: the hasher and both digests", (Hashes.keccakHasher oracle).withTests cases),
    ("crc: any generator", (Hashes.crcAny oracle).withTests cases)]
    select
  let slow := max 1 (cases / 20)
  let tower ← checkGroup "kernels: extension fields and pairings" [
    ("tower: constants of the curves", (Tower.curveConstants oracle).withTests 1),
    ("tower: Fp12 of BLS12-381", (Tower.blsFp12 oracle).withTests cases),
    ("tower: Fp2 and Fp6 of BLS12-381", (Tower.blsSubfields oracle).withTests cases),
    ("tower: final exponentiation and cyclotomic formulas",
      (Tower.blsFinal oracle).withTests (max 1 (cases / 4))),
    ("tower: the value of the BLS12-381 pairing", (Tower.blsPairing oracle).withTests slow),
    ("tower: the Miller loop of any parameter", (Tower.blsMiller oracle).withTests slow),
    ("tower: Fp12 and Fp2 of alt_bn128", (Tower.bnFp12 oracle).withTests cases),
    ("tower scenario in order: BLS12-381", TowerScenario.accumulator .deterministic
      (TowerScenario.blsField oracle)),
    ("tower scenario in madhouse: BLS12-381", (TowerScenario.accumulator .madhouse
      (TowerScenario.blsField oracle)).withTests (max 1 (cases / 4))),
    ("tower scenario in madhouse: alt_bn128", (TowerScenario.accumulator .madhouse
      (TowerScenario.bnField oracle)).withTests (max 1 (cases / 4)))]
    select
  let kdf ← checkGroup "kernels: key derivations" [
    ("kdf: HMAC-SHA-256", withMinimums cases [(15, "the key is longer than a block"),
      (1, "the key is exactly a block")] ((Kdf.hmac oracle).withTests cases)),
    ("kdf: HKDF", withMinimums cases [(2, "the output is exactly 255 blocks"),
      (6, "the output is longer than 255 blocks"), (8, "the key is shorter than 32 bytes")]
      ((Kdf.hkdf oracle).withTests cases)),
    ("kdf: PBKDF2", withMinimums cases [(6, "no iteration"),
      (20, "the output has several blocks")] ((Kdf.pbkdf2 oracle).withTests cases)),
    ("kdf: the Concatenation KDF", (Kdf.concatKdf oracle).withTests cases),
    ("kdf: the limits of the lengths", Kdf.limits.withTests (min cases 50)),
    ("kdf: scrypt", (Kdf.scrypt oracle).withTests (max 1 (cases / 4)))]
    select
  let curves ← checkGroup "kernels: Jacobian formulas" [
    ("jacobian: constants of secp256k1 and P-256", (Curves.constants oracle).withTests 1),
    ("jacobian: any curve over a small prime", withMinimums cases [
      (6, "P = Q, so the sum is a doubling"), (7, "P = -Q, so the sum is at infinity"),
      (4, "P is at infinity"), (1, "P has order two"), (10, "a = 0"), (10, "a = -3"),
      (5, "the scalar is the order of P")] (Curves.jacobian.withTests cases)),
    ("jacobian: generators at the edges of the order",
      (Curves.generators oracle).withTests (max 1 (cases / 4)))]
    select
  let unicode ← checkGroup "kernels: Unicode" [
    ("unicode: every code point", (Uni.everyCodePoint oracle).withTests 1),
    ("unicode: the order of marks", withMinimums cases [(5, "two marks are out of order"),
      (5, "two marks have one class")] ((Uni.ordering oracle).withTests cases))]
    select
  let setup ← checkGroup "kernels: trusted setup and signature frame" [
    ("setup: every point of the ceremony", (Setup.ceremony oracle).withTests 1),
    ("setup: the decoded points", Setup.decoded.withTests 1),
    ("frame: chains, search and ordered vectors", Setup.frame.withTests cases)]
    select
  -- What the properties found: each must fail, and passes once EthLib follows its source.
  --
  -- The group does not change the exit code.
  let _ ← checkGroup "kernels: findings (each must fail)" [
    ("finding: Hoodi activates Glamsterdam, which its sources withdrew",
      (Chain.activeNamed oracle "hoodi" .hoodi).withTests (max cases 200)),
    ("finding: the activations of Hoodi",
      (Chain.networkConstants oracle "hoodi" .hoodi).withTests 1)]
    select (mustFail := true)
  -- Each of these states less than its text asks for, and must fail with a counterexample.
  --
  -- The group does not change the exit code.
  let _ ← checkGroup "kernels: conditions that the texts state, each needed (must fail)" [
    ("pinned: the product in two parts above R / 2",
      (Mont.splitAbove 8).withTests (max cases 2000)),
    ("pinned: a scalar beyond the fuel", Curves.beyondFuel.withTests (max cases 500))]
    select (mustFail := true)
  pure (if montgomery && chain && base && hashes && tower && kdf && curves && unicode && setup
    then 0 else 1)

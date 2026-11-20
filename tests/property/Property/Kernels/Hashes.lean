import Property.Kernels.Common
import EthLib.Cryptography.Hash
import EthLib.Cryptography.Aes

/-!
# Hash internals at every parameter

Under each named hash lies a general function.

It is a compression on any state, a sponge at any rate, a CRC with any generator.

The vectors of a hash reach it from the initial state and at the parameters in use.

Here the state, the block, the rate and the generator are generated.

Each constant table is compared, entry by entry, with one computed from its standard.

`oracle/kernels_tables.py` computes them.
-/

open Hedgehog Support EthLib EthLib.Cryptography EthLib.Cryptography.Hash

namespace KernelsProperty.Hashes

/-- The numbers of an answer, or a failure when a word is not a number. -/
def parse (answer : String) : TestT IO (List Nat) :=
  match (words answer).mapM String.toNat? with
  | some xs => pure xs
  | none => failWith s!"the oracle answered: {answer.take 200}"

/-- A table of EthLib is the table computed from the standard, entry by entry. -/
def tableIs (oracle : Oracle) (name : String) (table : List Nat) : TestT IO Unit := do
  let want ← parse (← oracle.ask ["table", name])
  annotate s!"table {name}"
  table.length === want.length
  for (i, (got, want)) in (table.zip want).zipIdx.map (fun (x, i) => (i, x)) do
    if got != want then failWith s!"{name}[{i}] is {got} and the standard gives {want}"

/-- Every constant table of the hashes and of AES is the one its standard defines.

One test checks all entries.

They are 72 of SHA-256, 335 of RIPEMD-160, 49 of Keccak, 168 of BLAKE2b, and 512 of the S-boxes.

They are also 30 round constants of AES and the 65,536 products of GF(2^8). -/
def tables (oracle : Oracle) : Property IO := propertyM do
  pure do
    tableIs oracle "sha256_k" (Sha256.K.toList.map (·.toNat))
    tableIs oracle "sha256_iv" (Sha256.IV.toList.map (·.toNat))
    tableIs oracle "blake2b_iv" (Blake2b.IV.toList.map (·.toNat))
    tableIs oracle "blake2b_sigma" (Blake2b.SIGMA.toList.flatMap fun row =>
      row.toList.map (·.val))
    tableIs oracle "ripemd_k" (Ripemd160.K.toList.map (·.toNat))
    tableIs oracle "ripemd_kp" (Ripemd160.K'.toList.map (·.toNat))
    tableIs oracle "ripemd_r" (Ripemd160.r.toList.map (·.val))
    tableIs oracle "ripemd_rp" (Ripemd160.r'.toList.map (·.val))
    tableIs oracle "ripemd_s" (Ripemd160.s.toList.map (·.toNat))
    tableIs oracle "ripemd_sp" (Ripemd160.s'.toList.map (·.toNat))
    tableIs oracle "ripemd_iv" (Ripemd160.IV.toList.map (·.toNat))
    tableIs oracle "keccak_rc" (Keccak.RC.toList.map (·.toNat))
    tableIs oracle "keccak_rc" ((List.range 24).map fun i =>
      (Keccak.Internal.roundConstant i).toNat)
    tableIs oracle "keccak_rho" (Keccak.RHO.toList.map (·.toNat))
    tableIs oracle "keccak_rho" Keccak.Internal.rhoOffsets.toList
    tableIs oracle "aes_sbox" (Aes.SBOX.toList.map (·.toNat))
    tableIs oracle "aes_sbox" ((List.range 256).map fun b => (Aes.sbox (UInt8.ofNat b)).toNat)
    tableIs oracle "aes_sbox" ((List.range 256).map fun b =>
      (Aes.Internal.sbox (UInt8.ofNat b)).toNat)
    tableIs oracle "aes_inv_sbox" (Aes.INV_SBOX.toList.map (·.toNat))
    tableIs oracle "aes_inv_sbox" ((List.range 256).map fun b =>
      (Aes.invSbox (UInt8.ofNat b)).toNat)
    tableIs oracle "aes_rcon" ((List.range 30).map fun j => (Aes.rcon (j + 1))[0].toNat)
    for a in List.range 256 do
      let want ← parse (← oracle.ask ["aesmul", toString a])
      let got := (List.range 256).map fun b => (Aes.mul (UInt8.ofNat a) (UInt8.ofNat b)).toNat
      if got != want then failWith s!"a product of {a} in GF(2^8) differs"

/-- A block of `size` bytes: zeros, ones, or any bytes. -/
def genBlock (size : Nat) : Gen ByteArray :=
  Gen.frequency [
    (1, pure ⟨Array.replicate size 0⟩), (1, pure ⟨Array.replicate size 0xff⟩),
    (4, Gen.bytes (.singleton size))]

/-- A word of `bits` bits: all zeros, all ones, one bit, or any. -/
def genWordOf (bits : Nat) : Gen Nat :=
  Gen.frequency [
    (1, pure 0), (1, pure (2 ^ bits - 1)), (1, (2 ^ ·) <$> Gen.nat (.constant 0 (bits - 1))),
    (4, Gen.nat (.constant 0 (2 ^ bits - 1)))]

/-- The compression of SHA-256 on any hash value and any block, and its message schedule. -/
def shaCompress (oracle : Oracle) : Property IO := propertyM do
  let state ← forAll (Gen.frequency [
    (1, pure (Sha256.IV.toList.map (·.toNat))), (5, Gen.list (.singleton 8) (genWordOf 32))])
  let before ← forAll (Gen.nat (.linear 0 70))
  let block ← forAllWith bytesHex (genBlock 64)
  pure do
    let bytes := ByteArray.mk (Array.replicate before 0xaa) ++ block
    let w (i : Nat) : UInt32 := UInt32.ofNat state[i]!
    let s : Sha256.State := ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩
    classify "the state is the initial hash value" (state == Sha256.IV.toList.map (·.toNat))
    classify "the block is at an offset" (before > 0)
    if h : before + 64 ≤ bytes.size then
      let r := Sha256.compress s bytes before h
      [r.a, r.b, r.c, r.d, r.e, r.f, r.g, r.h].map (·.toNat) ===
        (← parse (← oracle.ask (["sha_compress"] ++ state.map toString ++ [hex block])))
      -- The schedule: `W_t` is the first word of the window after `t` steps.
      let window := Sha256.Window.ofBlock bytes before h
      let schedule := (List.range 64).map fun t => (Nat.repeat Sha256.Window.next t window).w0.toNat
      schedule === (← parse (← oracle.ask ["sha_schedule", hex block]))
    else failWith "the block is not whole"

/-- The compression of RIPEMD-160 on any chaining value and any block. -/
def ripemdCompress (oracle : Oracle) : Property IO := propertyM do
  let state ← forAll (Gen.list (.singleton 5) (genWordOf 32))
  let before ← forAll (Gen.nat (.linear 0 70))
  let block ← forAllWith bytesHex (genBlock 64)
  pure do
    let bytes := ByteArray.mk (Array.replicate before 0xaa) ++ block
    let h : Vector UInt32 5 := Vector.ofFn fun i => UInt32.ofNat state[i.val]!
    if whole : before + 64 ≤ bytes.size then
      (Ripemd160.compress h bytes before whole).toList.map (·.toNat) ===
        (← parse (← oracle.ask (["rmd_compress"] ++ state.map toString ++ [hex block])))
    else failWith "the block is not whole"

/-- A Keccak state from its 25 lanes, lane `(x, y)` at index `x + 5 y`. -/
def stateOf (l : List Nat) : Keccak.State :=
  let a (i : Nat) : UInt64 := UInt64.ofNat l[i]!
  ⟨a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11, a 12, a 13, a 14, a 15, a 16,
    a 17, a 18, a 19, a 20, a 21, a 22, a 23, a 24⟩

/-- The 25 lanes of a Keccak state. -/
def lanesOf (s : Keccak.State) : List Nat :=
  [s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13,
    s.a14, s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24].map (·.toNat)

/-- Each step mapping, each round and the whole permutation of Keccak, on any state. -/
def keccakPermutation (oracle : Oracle) : Property IO := propertyM do
  let lanes ← forAll (Gen.frequency [
    (4, Gen.list (.singleton 25) (genWordOf 64)),
    -- One lane set and the others zero: a wrong lane index shows at once.
    (2, (fun (i, x) => (List.range 25).map fun j => if i == j then x else 0) <$>
      Gen.zip (Gen.nat (.constant 0 24)) (genWordOf 64))])
  let ir ← forAll (Gen.nat (.constant 0 23))
  pure do
    let s := stateOf lanes
    let ask (command : List String) : TestT IO (List Nat) := do
      parse (← oracle.ask (command ++ lanes.map toString))
    lanesOf (Keccak.theta s) === (← ask ["keccak_step", "theta"])
    lanesOf (Keccak.rho s) === (← ask ["keccak_step", "rho"])
    lanesOf (Keccak.pi s) === (← ask ["keccak_step", "pi"])
    lanesOf (Keccak.chi s) === (← ask ["keccak_step", "chi"])
    if h : ir < Keccak.ROUNDS then
      lanesOf (Keccak.round ⟨ir, h⟩ s) === (← ask ["keccak_round", toString ir])
    lanesOf (Keccak.keccakF s) === (← ask ["keccak_f"])
    label s!"round {ir}"

/-- A rate in bytes for which FIPS 202 defines the sponge on whole lanes: 8, 16, up to 192. -/
def genRate : Gen Nat :=
  Gen.frequency [(1, Gen.element [136, 72]), (6, (8 * ·) <$> Gen.nat (.constant 1 24))]

/-- A message length near a multiple of the rate. -/
def genLength (rate : Nat) : Gen Nat :=
  Gen.frequency [
    (4, (fun (k, d) => k * rate + d - 2) <$>
      Gen.zip (Gen.nat (.constant 0 3)) (Gen.nat (.constant 0 4))),
    (2, Gen.nat (.linear 0 (3 * rate)))]

/-- The sponge of FIPS 202 absorbs at every rate of whole lanes, not only at 136 and 72 bytes.

The whole state after the last block is compared, so a lane past the digest counts too. -/
def keccakSponge (oracle : Oracle) : Property IO := propertyM do
  let rate ← forAll genRate
  let size ← forAll (genLength rate)
  let message ← forAllWith bytesHex (Gen.frequency [
    (1, pure ⟨Array.replicate size 0xff⟩), (3, Gen.bytes (.singleton size))])
  pure do
    classify "the rate is above 136 bytes" (rate > 136)
    classify "the rate is 136 or 72 bytes" (rate == 136 || rate == 72)
    classify "the rate is below 72 bytes" (rate < 72)
    classify "the message fills its last block" (size % rate == 0)
    classify "the message is one byte short of a block" (size % rate == rate - 1)
    classify "the message has several blocks" (size ≥ rate)
    let want ← parse (← oracle.ask ["keccak_absorb", toString rate, hex message])
    lanesOf (Keccak.spongeAbsorb Keccak.keccakF rate message) === want
    -- One block absorbed at an offset is the exclusive or of the lanes below the rate.
    let state := stateOf want
    let padded := Keccak.pad rate message
    let got := Keccak.Internal.absorbBlock rate state padded 0
    lanesOf got === (List.range 25).map fun i =>
      want[i]! ^^^ (if 8 * i < rate then
        (List.range 8).foldl (fun acc j => acc + (padded[8 * i + j]!).toNat * 256 ^ j) 0 else 0)
    Keccak.blockCount rate size === padded.size / rate

/-- The padding of Keccak at every rate, also one that is not whole lanes, for any length. -/
def keccakPadding (oracle : Oracle) : Property IO := propertyM do
  let rate ← forAll (Gen.frequency [(2, Gen.nat (.constant 1 250)), (1, genRate)])
  let size ← forAll (Gen.frequency [(3, genLength rate), (1, genNatBits 70)])
  pure do
    let padding := Keccak.padding rate size
    classify "the padding is one byte" (padding.size == 1)
    classify "the padding is a whole block" (padding.size == rate)
    hex padding === (← oracle.ask ["keccak_pad", toString rate, toString size])
    padding.toList === (List.range padding.size).map (Keccak.paddingByte rate size)

/-- The incremental hasher of Keccak-256 is the sponge at 136 bytes, however the bytes arrive. -/
def keccakHasher (oracle : Oracle) : Property IO := propertyM do
  let chunks ← forAll (Gen.list (.linear 0 6) (Gen.frequency [
    (2, Gen.nat (.constant 0 3)), (2, (fun d => 134 + d) <$> Gen.nat (.constant 0 4)),
    (1, (fun d => 270 + d) <$> Gen.nat (.constant 0 4)), (1, Gen.nat (.linear 0 300))]))
  let seed ← forAll genByte
  pure do
    let total := chunks.foldl (· + ·) 0
    let message : ByteArray := ⟨Array.ofFn (n := total) fun i => seed + UInt8.ofNat (i.val * 7)⟩
    let (hasher, _) := chunks.foldl (fun (h, done) size =>
      (h.absorb (message.extract done (done + size)), done + size)) (Keccak.Hasher256.empty, 0)
    classify "the bytes fill a block exactly" (total % 136 == 0 && total > 0)
    let want ← parse (← oracle.ask ["keccak_absorb", "136", hex message])
    let digest := (want.take 4).flatMap fun lane =>
      (List.range 8).map fun j => UInt8.ofNat (lane / 256 ^ j)
    hasher.digest.toList === digest
    (Keccak.keccak256 message).toList === digest
    -- Keccak-512 is the same sponge at 72 bytes, read over 64 bytes.
    let want ← parse (← oracle.ask ["keccak_absorb", "72", hex message])
    (Keccak.keccak512 message).toList === (want.take 8).flatMap fun lane =>
      (List.range 8).map fun j => UInt8.ofNat (lane / 256 ^ j)

/-- A 32-bit CRC with any generator polynomial, not only those of CRC-32 and CRC-32C. -/
def crcAny (oracle : Oracle) : Property IO := propertyM do
  let generator ← forAll (Gen.frequency [
    (1, Gen.element [0x04c11db7, 0x1edc6f41]), (1, genWordOf 32),
    (3, Gen.nat (.constant 0 (2 ^ 32 - 1)))])
  let data ← forAllWith bytesHex (Gen.frequency [
    (1, Gen.bytes (.constant 0 4)), (3, Gen.bytes (.linear 0 80))])
  pure do
    let g := UInt32.ofNat generator
    classify "the generator is the one of CRC-32 or of CRC-32C" (generator == 0x04c11db7 ||
      generator == 0x1edc6f41)
    classify "the message is shorter than 32 bits" (data.size < 4)
    let digest := Crc.digest g data
    hex ⟨digest.toArray⟩ === (← oracle.ask ["crc", toString generator, hex data])
    (Crc.value g data).toNat === digest.toList.zipIdx.foldl (fun acc (b, i) =>
      acc + b.toNat * 256 ^ i) 0
    if generator == 0x04c11db7 then (Crc32.crc32 data).toNat === (Crc.value g data).toNat
    if generator == 0x1edc6f41 then (Crc32c.crc32c data).toNat === (Crc.value g data).toNat
    let byte ← pure (UInt8.ofNat (generator % 256))
    (Crc.reverseBits byte).toNat === (List.range 8).foldl (fun acc i =>
      acc + (byte.toNat / 2 ^ i % 2) * 2 ^ (7 - i)) 0

end KernelsProperty.Hashes

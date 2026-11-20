import Property.Hashes.Common

/-!
# Hashes, checksums and key derivation against their references
-/

open Hedgehog Support EthLib EthLib.Cryptography EthLib.Cryptography.Hash

namespace HashesProperty

/-! ## Hashes -/

/-- Keccak-256 is the reference's, at every length around the rate of 136 bytes. -/
def keccak256 (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (orLong (genMsg 136))
  labelLength "message" 136 msg.size
  classify "message: 1,000 bytes or more" (msg.size ≥ 1000)
  labelSpongePadding 136 msg.size
  pure do hexv (Keccak.keccak256 msg) === (← oracle.ask ["keccak256", hex msg])

/-- Keccak-512 is the reference's, at every length around the rate of 72 bytes. -/
def keccak512 (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (orLong (genMsg 72 4))
  labelLength "message" 72 msg.size
  classify "message: 1,000 bytes or more" (msg.size ≥ 1000)
  labelSpongePadding 72 msg.size
  pure do hexv (Keccak.keccak512 msg) === (← oracle.ask ["keccak512", hex msg])

/-- The sponge at each rate of the Keccak family is the reference's: 144, 136, 104 and 72 bytes.

The state after the last block holds the digest in its first bytes.

At 144 bytes a block fills lane 17, which Keccak-256 and Keccak-512 leave to the capacity.

A block step that XORs only the lanes of Keccak-256 drops those bytes. -/
def keccakRates (oracle : Oracle) : Property IO := propertyM do
  let bits ← forAll (Gen.element [224, 256, 384, 512])
  let rate := 200 - bits / 4
  let msg ← forAll (genMsg rate 4)
  label s!"rate: {rate} bytes"
  labelLength "message" rate msg.size
  labelSpongePadding rate msg.size
  pure do
    let s := Keccak.spongeAbsorb Keccak.keccakF rate msg
    let lanes := [s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12,
      s.a13, s.a14, s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]
    -- A lane is eight bytes of the state, the low byte first.
    let bytesOf (lane : UInt64) : List UInt8 :=
      (List.range 8).map fun i => UInt8.ofNat (lane.toNat / 256 ^ i % 256)
    let digest := (lanes.flatMap bytesOf).take (bits / 8)
    hex ⟨digest.toArray⟩ === (← oracle.ask ["keccak", toString bits, hex msg])

/-- SHA-256 is the reference's, around 55, 56, 63, 64 and 65 bytes and their multiples. -/
def sha256 (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (orLong genMdMsg)
  labelLength "message" 64 msg.size
  classify "message: 1,000 bytes or more" (msg.size ≥ 1000)
  labelMdPadding msg.size
  pure do
    let expected ← oracle.ask ["sha256", hex msg]
    hex (Hash.sha256 msg) === expected
    hexv (Sha256.hash32 msg) === expected

/-- RIPEMD-160 is the reference's. -/
def ripemd160 (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (orLong genMdMsg)
  labelLength "message" 64 msg.size
  classify "message: 1,000 bytes or more" (msg.size ≥ 1000)
  labelMdPadding msg.size
  pure do hexv (Hash.ripemd160 msg) === (← oracle.ask ["ripemd160", hex msg])

/-- CRC-32 and CRC-32C are the references', and the digest is the value, low byte first. -/
def crc (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (Gen.frequency [(2, genBytes (.linear 0 5)), (1, genBytesOf 4), (3, genMsg 16)])
  classify "message: empty" msg.isEmpty
  classify "message: shorter than the register of 4 bytes" (0 < msg.size && msg.size < 4)
  classify "message: exactly 4 bytes" (msg.size == 4)
  classify "message: longer than 4 bytes" (msg.size > 4)
  pure do
    toString (Crc32.crc32 msg).toNat === (← oracle.ask ["crc32", hex msg])
    toString (Crc32c.crc32c msg).toNat === (← oracle.ask ["crc32c", hex msg])
    Base.bytesToUint (Crc32c.digest msg) === (Crc32c.crc32c msg).toNat
    Base.bytesToUint (Crc32.digest msg) === (Crc32.crc32 msg).toNat

/-- The 64-bit words that bytes spell, 8 bytes each, the first least significant. -/
def words64 (n : Nat) (bytes : ByteArray) : Vector UInt64 n :=
  Vector.ofFn fun i => UInt64.ofNat
    (Base.bytesToUint (vec 8 (bytes.extract (8 * i.val) (8 * i.val + 8))))

/-- The bytes of 64-bit words, the least significant first. -/
def unwords64 {n : Nat} (words : Vector UInt64 n) : ByteArray :=
  ⟨words.toArray.flatMap fun w => (Base.uintToBytes 8 w.toNat).toArray⟩

/-- The number of rounds of F: none, those around the 10 rows of the schedule, 12, or more.

A few run for thousands of rounds, where a count kept in a narrow word would wrap. -/
def genRounds : Gen Nat :=
  Gen.frequency [(8, Gen.element [0, 1, 2, 9, 10, 11, 12, 13, 19, 20, 21]),
    (4, Gen.nat (.linear 0 200)), (1, Gen.element [255, 256, 257, 1000, 4096, 5000])]

/-- The compression function F of BLAKE2b is that of RFC 7693, for any number of rounds. -/
def blake2f (oracle : Oracle) : Property IO := propertyM do
  let rounds ← forAll genRounds
  let h ← forAll (genBytesOf 64)
  let m ← forAll (genBytesOf 128)
  -- BLAKE2b itself keeps the high word of its offset at zero below `2^64` bytes.
  let (t0, t1) ← forAll (Gen.zip (genNatBits 64)
    (Gen.frequency [(1, pure 0), (2, genNatBits 64)]))
  let final ← forAll Gen.bool
  classify "rounds: none" (rounds == 0)
  classify "rounds: 1 to 9" (0 < rounds && rounds < 10)
  classify "rounds: 10 or 11, the schedule starts again" (rounds == 10 || rounds == 11)
  classify "rounds: 12, as BLAKE2b" (rounds == 12)
  classify "rounds: above 12" (rounds > 12)
  classify "the final block" final
  classify "rounds: 255 or more" (rounds ≥ 255)
  classify "the high word of the offset is not zero" (t1 != 0)
  classify "the high word of the offset is zero, as BLAKE2b" (t1 == 0)
  pure do
    let out := Blake2b.compress rounds (words64 8 h) (words64 16 m) (UInt64.ofNat t0)
      (UInt64.ofNat t1) final
    hex (unwords64 out) === (← oracle.ask ["blake2f", toString rounds, hex h, hex m, toString t0,
      toString t1, if final then "1" else "0"])

/-! ## HMAC and key derivation -/

/-- HMAC-SHA-256 is the reference's, with keys around the block of 64 bytes. -/
def hmac (oracle : Oracle) : Property IO := propertyM do
  let (key, msg) ← forAll (Gen.zip (genMsg 64 2) (genMsg 64 2))
  classify "key: empty" key.isEmpty
  classify "key: under a block" (0 < key.size && key.size < 64)
  classify "key: exactly a block" (key.size == 64)
  classify "key: longer than a block, hashed first" (key.size > 64)
  labelLength "message" 64 msg.size
  pure do
    let expected ← oracle.ask ["hmac", hex key, hex msg]
    hex (Hmac.hmac key msg) === expected
    hexv (Hmac.hmac32 key msg) === expected

/-- An output length: none, around a block of 32 bytes, or around a limit. -/
def genOutLen (limit : Nat) : Gen Nat :=
  Gen.frequency [
    (4, Gen.element [0, 1, 31, 32, 33, 63, 64, 65]),
    (2, Gen.nat (.linear 0 200)),
    (2, (fun d => limit + 2 - d) <$> Gen.nat (.constant 0 4))]

/-- Count the case under the class of an output length, in blocks of 32 bytes, against a limit. -/
def labelOutput {m : Type → Type} [Monad m] (limit length : Nat) : TestT m Unit := do
  classify "output: empty" (length == 0)
  classify "output: under a block" (0 < length && length < 32)
  classify "output: whole blocks" (0 < length && length % 32 == 0)
  classify "output: several blocks, the last one cut" (length > 32 && length % 32 != 0)
  classify "output: exactly the limit" (length == limit)
  classify "output: one past the limit" (length == limit + 1)

/-- HKDF-Expand is that of RFC 5869: short keys and more than 255 blocks are refused. -/
def hkdfExpand (oracle : Oracle) : Property IO := propertyM do
  let prk ← forAll (do genBytesOf (← Gen.element [32, 32, 31, 33, 0, 64, 65, 100]))
  let info ← forAll genShort
  let length ← forAll (genOutLen 8160)
  labelOutput 8160 length
  classify "key: exactly 32 bytes" (prk.size == 32)
  classify "info: empty" info.isEmpty
  pure do
    let got := Hkdf.expand prk info length
    labelOutcome got
    answerOf got === (← oracle.ask ["hkdf_expand", hex prk, hex info, toString length])

/-- HKDF is extract, then expand, with an absent salt as 32 zero bytes. -/
def hkdf (oracle : Oracle) : Property IO := propertyM do
  let salt ← forAll (Gen.choice [pure ByteArray.empty, genMsg 64 1])
  let (ikm, info) ← forAll (Gen.zip genShort genShort)
  let length ← forAll (genOutLen 8160)
  labelOutput 8160 length
  classify "salt: empty" salt.isEmpty
  classify "salt: longer than a block" (salt.size > 64)
  classify "key material: empty" ikm.isEmpty
  pure do
    let got := Hkdf.hkdf salt ikm info length
    labelOutcome got
    -- The extraction alone, as TLS 1.3 names it: HMAC keyed by the salt.
    hexv (Tls13.extract salt ikm) === (← oracle.ask ["hmac", hex salt, hex ikm])
    hex (Hkdf.extract salt ikm) === hexv (Tls13.extract salt ikm)
    answerOf got === (← oracle.ask ["hkdf", hex salt, hex ikm, hex info, toString length])

/-- HKDF-Expand-Label is that of RFC 8446 §7.1, and refuses the fields that do not fit. -/
def tls13 (oracle : Oracle) : Property IO := propertyM do
  let secret ← forAll (genBytesOf 32)
  let label ← forAll (do genBytesN (← Gen.frequency [(4, Gen.nat (.linear 0 20)),
    (3, Gen.element [0, 1, 248, 249, 250, 255, 256])]))
  let context ← forAll (do genBytesN (← Gen.frequency [(4, Gen.nat (.linear 0 40)),
    (3, Gen.element [0, 32, 254, 255, 256])]))
  let length ← forAll (Gen.frequency [(4, genOutLen 8160),
    (1, Gen.element [65535, 65536, 65537])])
  classify "label: 249 bytes, the longest" (label.size == 249)
  classify "context: 255 bytes, the longest" (context.size == 255)
  classify "context: empty" context.isEmpty
  pure do
    let got := (Tls13.expandLabel (vec 32 secret) label context length).map unvec
    labelOutcome got
    answerOf got === (← oracle.ask ["tls13", hex secret, hex label, hex context, toString length])

/-- The Concatenation KDF is the reference's, and refuses an empty output. -/
def concatKdf (oracle : Oracle) : Property IO := propertyM do
  let (z, info) ← forAll (Gen.zip (genMsg 64 1) genShort)
  let length ← forAll (genOutLen 100)
  labelOutput 100 length
  classify "secret: empty" z.isEmpty
  classify "info: empty" info.isEmpty
  pure do
    let got := ConcatKdf.concatKdf z info length
    labelOutcome got
    answerOf got === (← oracle.ask ["concatkdf", hex z, hex info, toString length])

/-- PBKDF2 is the reference's, and refuses no iterations and an empty output. -/
def pbkdf2 (oracle : Oracle) : Property IO := propertyM do
  let (password, salt) ← forAll (Gen.zip (genMsg 64 1) genShort)
  let count ← forAll (Gen.frequency [(1, pure 0), (6, Gen.nat (.linear 1 6))])
  let length ← forAll (genOutLen 100)
  labelOutput 100 length
  classify "iterations: one" (count == 1)
  classify "iterations: several" (count > 1)
  classify "password: longer than a block, hashed first" (password.size > 64)
  classify "salt: empty" salt.isEmpty
  pure do
    let got := Pbkdf2.pbkdf2 password salt count length
    labelOutcome got
    answerOf got
      === (← oracle.ask ["pbkdf2", hex password, hex salt, toString count, toString length])

/-! ## Scrypt -/

/-- Salsa20/8, BlockMix and ROMix are those of RFC 7914 §§3 to 5.

Each refuses an input that is not of its size, and ROMix a cost that RFC 7914 §2 excludes. -/
def scryptSteps (oracle : Oracle) : Property IO := propertyM do
  let r ← forAll (Gen.frequency [(10, Gen.nat (.constant 1 3)), (1, pure 0)])
  let n ← forAll (Gen.frequency [(8, Gen.element [2, 4, 8, 16]),
    (1, Gen.element [0, 1, 3, 6, 12]), (1, (2 ^ (16 * r) * ·) <$> Gen.element [1, 2])])
  let size ← forAll (Gen.frequency [(8, pure (128 * r)),
    (2, Gen.element [0, 64, 128 * r - 1, 128 * r + 1, 128 * r + 64, 128 * (r + 1)])])
  let block ← forAll (genBytesOf size)
  let salsaIn ← forAll (do genBytesOf (← Gen.frequency [(8, pure 64),
    (2, Gen.element [0, 63, 65, 128])]))
  label s!"r = {r}"
  classify "N: 2, 4, 8 or 16" ([2, 4, 8, 16].contains n)
  classify "block: of 128 r bytes" (size == 128 * r)
  pure do
    let salsa := Scrypt.salsa208 salsaIn
    let mix := Scrypt.blockMix block r
    let rom := Scrypt.romix block n r
    labelOutcome salsa "Salsa20/8"
    labelOutcome mix "BlockMix"
    labelOutcome rom "ROMix"
    answerOf salsa === (← oracle.ask ["salsa208", hex salsaIn])
    answerOf mix === (← oracle.ask ["blockmix", hex block, toString r])
    answerOf rom === (← oracle.ask ["romix", hex block, toString n, toString r])

/-- The cost and the block size: valid small ones, and the ones RFC 7914 §2 refuses. -/
def genCost : Gen (Nat × Nat) :=
  Gen.frequency [
    (8, Gen.zip (Gen.element [2, 4, 8, 16, 32]) (Gen.nat (.constant 1 3))),
    -- The block size of every keystore is 8, and a larger one mixes more blocks of 64 bytes.
    (2, Gen.zip (Gen.element [2, 4]) (Gen.element [4, 8, 16])),
    (2, Gen.zip (Gen.element [0, 1, 3, 5, 6, 7, 12, 24]) (Gen.nat (.constant 1 2))),
    (1, Gen.zip (Gen.element [2, 4]) (pure 0)),
    (1, pure (65536, 1)), (1, pure (2 ^ 32, 2)), (1, pure (2 ^ 64, 1))]

/-- Count the case under what scrypt does with the parameters, read from the rules alone.

The outcome of EthLib is not computed here, since a large `N` is costly before it is refused. -/
def labelScrypt {m : Type → Type} [Monad m] (n r p length : Nat) : TestT m Unit := do
  let reason :=
    if r == 0 then "refused, invalidBlockSize"
    else if !(n > 1 && n &&& (n - 1) == 0 && n < 2 ^ (16 * r)) then "refused, invalidCost"
    else if p == 0 || Pbkdf2.MAX_LENGTH < p * 128 * r then "refused, invalidParallelization"
    else if length == 0 then "refused, emptyOutput"
    else if Pbkdf2.MAX_LENGTH < length then "refused, outputTooLong"
    else "accepted"
  label s!"outcome: {reason}"
  classify "cost: not a power of two" (n > 1 && n &&& (n - 1) != 0)
  classify "cost: 0 or 1" (n < 2)
  classify "cost: a power of two, too large for r"
    (n > 1 && n &&& (n - 1) == 0 && n ≥ 2 ^ (16 * r))
  classify "p: several blocks mixed" (p > 1 && p < 2 ^ 20)
  classify "r: 4 or more" (r ≥ 4)

/-- Scrypt is the reference's, and the parameters it refuses are those of RFC 7914 §2. -/
def scrypt (oracle : Oracle) : Property IO := propertyM do
  let (password, salt) ← forAll (Gen.zip genShort genShort)
  let (n, r) ← forAll genCost
  let p ← forAll (Gen.frequency [(1, Gen.element [0, 2 ^ 30, 2 ^ 31]),
    (6, Gen.nat (.constant 1 3)), (1, pure 8)])
  let length ← forAll (Gen.element [0, 1, 31, 32, 33, 64, 65, 100])
  labelScrypt n r p length
  pure do
    answerOf (Scrypt.scrypt password salt n r p length) === (← oracle.ask ["scrypt",
      hex password, hex salt, toString n, toString r, toString p, toString length])

end HashesProperty

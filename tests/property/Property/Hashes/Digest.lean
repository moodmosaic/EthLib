import Property.Hashes.Common

/-!
# Hashes, checksums and key derivation against their references
-/

open Hedgehog Support EthLib EthLib.Cryptography EthLib.Cryptography.Hash

namespace HashesProperty

/-! ## Hashes -/

/-- Keccak-256 is the reference's, at every length around the rate of 136 bytes. -/
def keccak256 (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (genMsg 136)
  pure do hexv (Keccak.keccak256 msg) === (← oracle.ask ["keccak256", hex msg])

/-- Keccak-512 is the reference's, at every length around the rate of 72 bytes. -/
def keccak512 (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (genMsg 72 4)
  pure do hexv (Keccak.keccak512 msg) === (← oracle.ask ["keccak512", hex msg])

/-- The sponge at each rate of the Keccak family is the reference's: 144, 136, 104 and 72 bytes.

The state after the last block holds the digest in its first bytes.
At 144 bytes a block fills lane 17, which Keccak-256 and Keccak-512 leave to the capacity: a
block step that XORs only the lanes of Keccak-256 drops those bytes. -/
def keccakRates (oracle : Oracle) : Property IO := propertyM do
  let bits ← forAll (Gen.element [224, 256, 384, 512])
  let rate := 200 - bits / 4
  let msg ← forAll (genMsg rate 4)
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
  let msg ← forAll (genMsg 64 4)
  pure do
    let expected ← oracle.ask ["sha256", hex msg]
    hex (Hash.sha256 msg) === expected
    hexv (Sha256.hash32 msg) === expected

/-- RIPEMD-160 is the reference's. -/
def ripemd160 (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (genMsg 64 4)
  pure do hexv (Hash.ripemd160 msg) === (← oracle.ask ["ripemd160", hex msg])

/-- CRC-32 and CRC-32C are the references', and the digest is the value, low byte first. -/
def crc (oracle : Oracle) : Property IO := propertyM do
  let msg ← forAll (Gen.choice [genBytes (.linear 0 5), genMsg 16])
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

/-- The number of rounds of F: none, those around the 10 rows of the schedule, 12, or more. -/
def genRounds : Gen Nat :=
  Gen.frequency [(4, Gen.element [0, 1, 2, 9, 10, 11, 12, 13, 19, 20, 21]),
    (2, Gen.nat (.linear 0 200))]

/-- The compression function F of BLAKE2b is that of RFC 7693, for any number of rounds. -/
def blake2f (oracle : Oracle) : Property IO := propertyM do
  let rounds ← forAll genRounds
  let h ← forAll (genBytesOf 64)
  let m ← forAll (genBytesOf 128)
  let (t0, t1) ← forAll (Gen.zip (genNatBits 64) (genNatBits 64))
  let final ← forAll Gen.bool
  pure do
    let out := Blake2b.compress rounds (words64 8 h) (words64 16 m) (UInt64.ofNat t0)
      (UInt64.ofNat t1) final
    hex (unwords64 out) === (← oracle.ask ["blake2f", toString rounds, hex h, hex m, toString t0,
      toString t1, if final then "1" else "0"])

/-! ## HMAC and key derivation -/

/-- HMAC-SHA-256 is the reference's, with keys around the block of 64 bytes. -/
def hmac (oracle : Oracle) : Property IO := propertyM do
  let (key, msg) ← forAll (Gen.zip (genMsg 64 2) (genMsg 64 2))
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

/-- HKDF-Expand is that of RFC 5869: short keys and more than 255 blocks are refused. -/
def hkdfExpand (oracle : Oracle) : Property IO := propertyM do
  let prk ← forAll (do genBytesOf (← Gen.element [32, 32, 31, 33, 0, 64, 65, 100]))
  let info ← forAll genShort
  let length ← forAll (genOutLen 8160)
  pure do
    answerOf (Hkdf.expand prk info length)
      === (← oracle.ask ["hkdf_expand", hex prk, hex info, toString length])

/-- HKDF is extract, then expand, with an absent salt as 32 zero bytes. -/
def hkdf (oracle : Oracle) : Property IO := propertyM do
  let salt ← forAll (Gen.choice [pure ByteArray.empty, genMsg 64 1])
  let (ikm, info) ← forAll (Gen.zip genShort genShort)
  let length ← forAll (genOutLen 8160)
  pure do
    answerOf (Hkdf.hkdf salt ikm info length)
      === (← oracle.ask ["hkdf", hex salt, hex ikm, hex info, toString length])

/-- HKDF-Expand-Label is that of RFC 8446 §7.1, and refuses the fields that do not fit. -/
def tls13 (oracle : Oracle) : Property IO := propertyM do
  let secret ← forAll (genBytesOf 32)
  let label ← forAll (do genBytesN (← Gen.frequency [(4, Gen.nat (.linear 0 20)),
    (3, Gen.element [0, 1, 248, 249, 250, 255, 256])]))
  let context ← forAll (do genBytesN (← Gen.frequency [(4, Gen.nat (.linear 0 40)),
    (3, Gen.element [0, 32, 254, 255, 256])]))
  let length ← forAll (Gen.frequency [(4, genOutLen 8160),
    (1, Gen.element [65535, 65536, 65537])])
  pure do
    let got := (Tls13.expandLabel (vec 32 secret) label context length).map unvec
    answerOf got === (← oracle.ask ["tls13", hex secret, hex label, hex context, toString length])

/-- The Concatenation KDF is the reference's, and refuses an empty output. -/
def concatKdf (oracle : Oracle) : Property IO := propertyM do
  let (z, info) ← forAll (Gen.zip (genMsg 64 1) genShort)
  let length ← forAll (genOutLen 100)
  pure do
    answerOf (ConcatKdf.concatKdf z info length)
      === (← oracle.ask ["concatkdf", hex z, hex info, toString length])

/-- PBKDF2 is the reference's, and refuses no iterations and an empty output. -/
def pbkdf2 (oracle : Oracle) : Property IO := propertyM do
  let (password, salt) ← forAll (Gen.zip (genMsg 64 1) genShort)
  let count ← forAll (Gen.frequency [(1, pure 0), (6, Gen.nat (.linear 1 6))])
  let length ← forAll (genOutLen 100)
  pure do
    answerOf (Pbkdf2.pbkdf2 password salt count length)
      === (← oracle.ask ["pbkdf2", hex password, hex salt, toString count, toString length])

/-! ## Scrypt -/

/-- Salsa20/8, BlockMix and ROMix are those of RFC 7914 §§3 to 5. -/
def scryptSteps (oracle : Oracle) : Property IO := propertyM do
  let r ← forAll (Gen.nat (.constant 1 3))
  let n ← forAll (Gen.element [2, 4, 8, 16])
  let block ← forAll (genBytesOf (128 * r))
  pure do
    let salsaIn := block.extract 0 64
    answerOf (Scrypt.salsa208 salsaIn) === (← oracle.ask ["salsa208", hex salsaIn])
    answerOf (Scrypt.blockMix block r) === (← oracle.ask ["blockmix", hex block, toString r])
    answerOf (Scrypt.romix block n r)
      === (← oracle.ask ["romix", hex block, toString n, toString r])

/-- The cost and the block size: valid small ones, and the ones RFC 7914 §2 refuses. -/
def genCost : Gen (Nat × Nat) :=
  Gen.frequency [
    (8, Gen.zip (Gen.element [2, 4, 8, 16, 32]) (Gen.nat (.constant 1 3))),
    (2, Gen.zip (Gen.element [0, 1, 3, 5, 6, 7, 12, 24]) (Gen.nat (.constant 1 2))),
    (1, Gen.zip (Gen.element [2, 4]) (pure 0)),
    (1, pure (65536, 1)), (1, pure (2 ^ 32, 2)), (1, pure (2 ^ 64, 1))]

/-- Scrypt is the reference's, and the parameters it refuses are those of RFC 7914 §2. -/
def scrypt (oracle : Oracle) : Property IO := propertyM do
  let (password, salt) ← forAll (Gen.zip genShort genShort)
  let (n, r) ← forAll genCost
  let p ← forAll (Gen.frequency [(1, Gen.element [0, 2 ^ 30, 2 ^ 31]),
    (6, Gen.nat (.constant 1 3))])
  let length ← forAll (Gen.element [0, 1, 31, 32, 33, 64, 65, 100])
  pure do
    answerOf (Scrypt.scrypt password salt n r p length) === (← oracle.ask ["scrypt",
      hex password, hex salt, toString n, toString r, toString p, toString length])

end HashesProperty

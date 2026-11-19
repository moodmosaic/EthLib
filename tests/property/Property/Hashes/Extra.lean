import Property.Hashes.Machines

/-!
# Models written from the source text, and the branches that random inputs do not reach

Paddings and lengths as arithmetic on `Nat`, the limits of the parameters, AES-192 through the
general cipher, key derivations past 255 and past 65535 blocks, and what the documented
preconditions of the multiproof and of the keystore reader leave open.
-/

open Hedgehog Support EthLib EthLib.Cryptography EthLib.Cryptography.Hash

namespace HashesProperty

/-- A size in bytes: small, or around a power of two up to `2^70`. -/
def genSize : Gen Nat :=
  Gen.frequency [
    (2, Gen.nat (.linear 0 300)),
    (4, Gen.zipWith (fun k d => 2 ^ k + 2 - d) (Gen.nat (.constant 3 70))
      (Gen.nat (.constant 0 4))),
    (2, Gen.nat (.exponential 0 (2 ^ 70)))]

/-- The paddings are those of the standards, as arithmetic on the size alone.
FIPS 180-4 §5.1.1 and RFC 1320 §3: the padded size is the least multiple of 64 that holds the
message, one byte and eight bytes of length; the length is the size in bits modulo `2^64`,
big-endian for SHA-256 and little-endian for RIPEMD-160.
FIPS 202 §5.1: pad10*1 fills up to the next multiple of the rate, with at least one byte. -/
def paddings : Property IO := pureIO do
  let size ← forAll genSize
  let bits := 8 * size % 2 ^ 64
  (Sha256.lengthBytes size).toList === Base.natToBytes 8 bits
  (Ripemd160.lengthBytes size).toList === (Base.natToBytes 8 bits).reverse
  let zeros := Sha256.paddingZeros size
  ensure ((size + 1 + zeros + 8) % 64 == 0 && zeros < 64) "SHA-256 pads to no block, or too far"
  Ripemd160.paddingZeros size === zeros
  let rate ← forAll (Gen.frequency [(3, Gen.element [136, 72]), (1, Gen.nat (.constant 1 200))])
  let padding := (Keccak.padding rate size).toList
  let k := rate - size % rate
  padding === (if k = 1 then [0x81] else [0x01] ++ List.replicate (k - 2) 0x00 ++ [0x80])
  (List.range k).map (Keccak.paddingByte rate size) === padding
  Keccak.blockCount rate size === (size + k) / rate

/-- The message with its padding is whole blocks and ends with its length. -/
def padded : Property IO := pureIO do
  let msg ← forAll (genMsg 64 3)
  let sha := Sha256.pad msg
  ensure (sha.size % 64 == 0 && sha.size ≥ msg.size + 9 && sha.size < msg.size + 9 + 64) "SHA-256"
  hex (sha.extract 0 (msg.size + 1)) === hex (msg.push 0x80)
  Keystore.shaBlocks msg.size === sha.size / 64
  let rmd := Ripemd160.pad msg
  rmd.size === sha.size
  hex (rmd.extract 0 (rmd.size - 8)) === hex (sha.extract 0 (sha.size - 8))
  let keccak := Keccak.pad 136 msg
  ensure (keccak.size % 136 == 0 && keccak.size > msg.size && keccak.size ≤ msg.size + 136)
    "Keccak-256"

/-- The cost of scrypt is valid exactly when RFC 7914 §2 says: a power of two, above 1 and
below `2^(128 r / 8)`. -/
def scryptCost : Property IO := pureIO do
  let r ← forAll (Gen.frequency [(4, Gen.nat (.constant 0 4)), (1, Gen.nat (.linear 0 64))])
  let n ← forAll (Gen.frequency [
    (4, Gen.zipWith (fun k d => 2 ^ k + 1 - d) (Gen.nat (.constant 0 70))
      (Gen.nat (.constant 0 2))),
    (1, (2 ^ (16 * r) + 1 - ·) <$> Gen.nat (.constant 0 2)),
    (1, Gen.nat (.exponential 0 (2 ^ 80)))])
  let power := (List.range 1100).any fun k => 2 ^ k == n
  Scrypt.validCost n r === (power && 1 < n && n < 2 ^ (128 * r / 8))

/-- The length limits of the AEAD are those of RFC 8439 §2.8: `2^64 - 1` bytes of additional
data and `2^38 - 64` bytes of text. -/
def aeadLimits : Property IO := pureIO do
  let near (top : Nat) : Gen Nat :=
    Gen.frequency [(1, genNatBits 70), (2, (top + 2 - ·) <$> Gen.nat (.constant 0 4))]
  let aad ← forAll (near (2 ^ 64 - 1))
  let text ← forAll (near (2 ^ 38 - 64))
  (ChaCha20Poly1305.checkLengths aad text).isOk === (aad ≤ 2 ^ 64 - 1 && text ≤ 2 ^ 38 - 64)

/-- The general cipher of FIPS 197 with `Nk = 6` and `Nr = 12` is AES-192, and its inverse. -/
def aes192 (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll (genBytesOf 24)
  let block ← forAll (genBytesOf 16)
  pure do
    let schedule := Aes.keyExpansion 6 12 (vec 24 key)
    hexv (Aes.cipher 12 schedule (vec 16 block)) === (← oracle.ask ["aes", hex key, hex block])
    hexv (Aes.invCipher 12 schedule (vec 16 block))
      === (← oracle.ask ["aesinv", hex key, hex block])

/-- The last 64 bytes of a result, or `error`. -/
def tailOf {ε : Type} (result : Except ε ByteArray) : String :=
  match result with
  | .ok bytes => hex (bytes.extract (bytes.size - 64) bytes.size)
  | .error _ => "error"

/-- A key derivation whose block index passes one byte and two bytes ends as the reference's.
The index of PBKDF2 and the counter of the Concatenation KDF are four bytes, and the short
outputs of the other properties never leave the last one. -/
def longOutputs (oracle : Oracle) : Property IO := propertyM do
  let (secret, salt) ← forAll (Gen.zip genShort genShort)
  let length ← forAll (Gen.zipWith (fun blocks rest => 32 * blocks + rest)
    (Gen.element [255, 256, 257, 65535, 65536]) (Gen.element [0, 1, 31]))
  pure do
    tailOf (Pbkdf2.pbkdf2 secret salt 1 length)
      === (← oracle.ask ["pbkdf2_tail", hex secret, hex salt, toString length])
    tailOf (ConcatKdf.concatKdf secret salt length)
      === (← oracle.ask ["concatkdf_tail", hex secret, hex salt, toString length])

/-! ## What the documented preconditions leave open

These pass while EthLib behaves as it does now.
None is a deviation from a source: each pins a behaviour that a caller must know. -/

/-- `Merkle.verify` binds the opened values only under the preconditions of `verify_binding`.
A value opened below another opened node, at a repeated position or outside the tree is not
read, so the multiproof rebuilds the root whatever that value is. -/
def multiproofUnbound : Property IO := pureIO do
  let (h, leaves) ← forAll (Gen.filter (fun t => t.1 > 0) genTree)
  let tree := levels leaves h
  let root := modelNode tree ⟨h, 0⟩
  let j ← forAll (Gen.nat (.constant 0 (2 ^ h - 1)))
  let leaf : Merkle.Position := ⟨0, j⟩
  let check (opened : List Merkle.Position) (values : List String) : PropertyM Unit := do
    let helperValues := (Merkle.helpers h opened).map (modelNode tree)
    Id.run (Merkle.verify symbolic h opened values helperValues) === some root
  -- Below an opened node.
  check [leaf.parent, leaf] [modelNode tree leaf.parent, "bogus"]
  -- At a repeated position.
  check [leaf, leaf] [modelNode tree leaf, "bogus"]
  -- Outside the tree.
  check [leaf, ⟨0, 2 ^ h + j⟩] [modelNode tree leaf, "bogus"]
  -- With more helper values than helpers.
  let helperValues := (Merkle.helpers h [leaf]).map (modelNode tree)
  Id.run (Merkle.verify symbolic h [leaf] [modelNode tree leaf] (helperValues ++ ["bogus"]))
    === some root

/-- The keystore reader takes a number by its JSON text, not by its value.
`4e0` is read as the version 4 and `4.0` is refused, though both are the integer 4. -/
def keystoreNumbers : Property IO := pureIO do
  let read (text : String) : Option Nat :=
    (Lean.Json.parse text).toOption.bind fun json => (Keystore.number "version" json).toOption
  read "4" === some 4
  read "4e0" === some 4
  read "4.0" === none
  read "40e-1" === none
  read "-0" === some 0

end HashesProperty

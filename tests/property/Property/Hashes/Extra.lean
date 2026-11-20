import Property.Hashes.Machines

/-!
# Models written from the source text, and the branches that random inputs do not reach

The properties here cover:

- Paddings and lengths as arithmetic on `Nat`.
- The limits of the parameters.
- A message whose length in bits passes `2^32`.
- Key derivations past 255 and past 65535 blocks.
- What the documented preconditions of the multiproof and of the keystore reader leave open.
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

FIPS 180-4 §5.1.1 and RFC 1320 §3:

The padded size is the least multiple of 64 to hold the message, one byte and eight bytes of length.

The length is the size in bits modulo `2^64`.

It is big-endian for SHA-256 and little-endian for RIPEMD-160.

FIPS 202 §5.1: pad10*1 fills up to the next multiple of the rate, with at least one byte. -/
def paddings : Property IO := pureIO do
  let rate ← forAll (Gen.frequency [(3, Gen.element [136, 72]), (1, Gen.nat (.constant 1 200))])
  -- A size on each edge of a padding: 55 and 56 bytes into a block, and the end of a rate.
  let size ← forAll (Gen.frequency [(4, genSize),
    (2, Gen.zipWith (fun k d => 64 * k + 54 + d) genSize (Gen.nat (.constant 0 2))),
    (2, Gen.zipWith (fun k d => rate * (k + 1) + 1 - d) genSize (Gen.nat (.constant 0 2)))])
  classify "size: its bit length passes 2^32" (8 * size ≥ 2 ^ 32)
  classify "size: its bit length passes 2^64, reduced" (8 * size ≥ 2 ^ 64)
  labelMdPadding size
  let bits := 8 * size % 2 ^ 64
  (Sha256.lengthBytes size).toList === Base.natToBytes 8 bits
  (Ripemd160.lengthBytes size).toList === (Base.natToBytes 8 bits).reverse
  let zeros := Sha256.paddingZeros size
  ensure ((size + 1 + zeros + 8) % 64 == 0 && zeros < 64) "SHA-256 pads to no block, or too far"
  Ripemd160.paddingZeros size === zeros
  classify "rate: of Keccak-256 or Keccak-512" (rate == 136 || rate == 72)
  labelSpongePadding rate size
  let padding := (Keccak.padding rate size).toList
  let k := rate - size % rate
  padding === (if k = 1 then [0x81] else [0x01] ++ List.replicate (k - 2) 0x00 ++ [0x80])
  (List.range k).map (Keccak.paddingByte rate size) === padding
  Keccak.blockCount rate size === (size + k) / rate

/-- The message with its padding is whole blocks and ends with its length. -/
def padded : Property IO := pureIO do
  let msg ← forAll (Gen.choice [genMdMsg, genMsg 136 2])
  labelLength "message" 64 msg.size
  labelMdPadding msg.size
  labelSpongePadding 136 msg.size
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

/-- The cost of scrypt is valid exactly when RFC 7914 §2 says.

That is a power of two, above 1 and below `2^(128 r / 8)`. -/
def scryptCost : Property IO := pureIO do
  let r ← forAll (Gen.frequency [(4, Gen.nat (.constant 0 4)), (1, Gen.nat (.linear 0 64))])
  let n ← forAll (Gen.frequency [
    (4, Gen.zipWith (fun k d => 2 ^ k + 1 - d) (Gen.nat (.constant 0 70))
      (Gen.nat (.constant 0 2))),
    (1, (2 ^ (16 * r) + 1 - ·) <$> Gen.nat (.constant 0 2)),
    (2, (2 ^ (16 * r) / 2 ^ ·) <$> Gen.nat (.constant 0 2)),
    (1, Gen.nat (.exponential 0 (2 ^ 80)))])
  let power := (List.range 1100).any fun k => 2 ^ k == n
  classify "valid" (power && 1 < n && n < 2 ^ (128 * r / 8))
  classify "refused: 0 or 1" (n < 2)
  classify "refused: not a power of two" (n ≥ 2 && !power)
  classify "refused: a power of two, too large for r" (power && n ≥ 2 ^ (128 * r / 8))
  classify "the largest valid cost of r, 2^(16 r - 1)" (r > 0 && n == 2 ^ (16 * r - 1))
  classify "the least cost too large for r, 2^(16 r)" (n == 2 ^ (16 * r))
  classify "r: zero" (r == 0)
  Scrypt.validCost n r === (power && 1 < n && n < 2 ^ (128 * r / 8))

/-- The length limits of the AEAD are those of RFC 8439 §2.8.

They are `2^64 - 1` bytes of additional data and `2^38 - 64` bytes of text. -/
def aeadLimits : Property IO := pureIO do
  let near (top : Nat) : Gen Nat :=
    Gen.frequency [(1, genNatBits 70), (2, (top + 2 - ·) <$> Gen.nat (.constant 0 4))]
  let aad ← forAll (near (2 ^ 64 - 1))
  let text ← forAll (near (2 ^ 38 - 64))
  labelOutcome (ChaCha20Poly1305.checkLengths aad text)
  classify "additional data: exactly the limit" (aad == 2 ^ 64 - 1)
  classify "additional data: one past the limit" (aad == 2 ^ 64)
  classify "text: exactly the limit" (text == 2 ^ 38 - 64)
  classify "text: one past the limit" (text == 2 ^ 38 - 63)
  (ChaCha20Poly1305.checkLengths aad text).isOk === (aad ≤ 2 ^ 64 - 1 && text ≤ 2 ^ 38 - 64)

/-- The last 64 bytes of a result, or `error`. -/
def tailOf {ε : Type} (result : Except ε ByteArray) : String :=
  match result with
  | .ok bytes => hex (bytes.extract (bytes.size - 64) bytes.size)
  | .error _ => "error"

/-- A key derivation whose block index passes one byte and two bytes ends as the reference's.

The index of PBKDF2 and the counter of the Concatenation KDF are four bytes.

The short outputs of the other properties never leave the last one. -/
def longOutputs (oracle : Oracle) : Property IO := propertyM do
  let (secret, salt) ← forAll (Gen.zip genShort genShort)
  let length ← forAll (Gen.zipWith (fun blocks rest => 32 * blocks + rest)
    (Gen.element [255, 256, 257, 65535, 65536]) (Gen.element [0, 1, 31]))
  classify "blocks: the index passes one byte" ((length + 31) / 32 > 255)
  classify "blocks: the index passes two bytes" ((length + 31) / 32 > 65535)
  classify "output: the last block is cut" (length % 32 != 0)
  pure do
    tailOf (Pbkdf2.pbkdf2 secret salt 1 length)
      === (← oracle.ask ["pbkdf2_tail", hex secret, hex salt, toString length])
    tailOf (ConcatKdf.concatKdf secret salt length)
      === (← oracle.ask ["concatkdf_tail", hex secret, hex salt, toString length])

/-- SHA-256 and RIPEMD-160 of a message whose length in bits passes `2^32`.

Both end the padding with the length in bits as 64 bits, and a short message fills only the low 32.

The message is one byte repeated `2^29` times and a few more, so it is not sent to the reference.

Each side hashes half a gigabyte, so this runs once and only when asked. -/
def longMessage (oracle : Oracle) : Property IO := propertyM do
  let byte ← forAll (Gen.element [(0 : UInt8), 0x61, 0xff])
  let extra ← forAll (Gen.element [0, 1, 55, 56, 64])
  pure do
    let size := 2 ^ 29 + extra
    let message : ByteArray := ⟨Array.replicate size byte⟩
    s!"{hex (Hash.sha256 message)} {hexv (Hash.ripemd160 message)}"
      === (← oracle.ask ["filled", toString byte.toNat, toString size])

/-! ## What the documented preconditions leave open

Each property here states what EthLib does not do, so it fails by design.

None is a deviation from a source: each shows a behaviour that a caller must know. -/

/-- FAILS BY DESIGN: `Merkle.verify` binds every opened value that it is given.

It binds them only under the preconditions of `verify_binding`.

A value opened below another opened node, at a repeated position or outside the tree is not read.

Neither is a helper value past the last helper.

So the multiproof rebuilds the root whatever that value is. -/
def multiproofBinds : Property IO := pureIO do
  let (h, leaves) ← forAll (Gen.filter (fun t => t.1 > 0) genTree)
  let tree := levels leaves h
  let root := modelNode tree ⟨h, 0⟩
  let j ← forAll (Gen.nat (.constant 0 (2 ^ h - 1)))
  let leaf : Merkle.Position := ⟨0, j⟩
  let kind ← forAll (Gen.element ["below an opened node", "at a repeated position",
    "outside the tree", "a helper value too many"])
  let (opened, values) : List Merkle.Position × List String := match kind with
    | "below an opened node" => ([leaf.parent, leaf], [modelNode tree leaf.parent, "bogus"])
    | "at a repeated position" => ([leaf, leaf], [modelNode tree leaf, "bogus"])
    | "outside the tree" => ([leaf, ⟨0, 2 ^ h + j⟩], [modelNode tree leaf, "bogus"])
    | _ => ([leaf], [modelNode tree leaf])
  let helperValues := (Merkle.helpers h opened).map (modelNode tree) ++
    (if kind == "a helper value too many" then ["bogus"] else [])
  Id.run (Merkle.verify symbolic h opened values helperValues) /== some root

/-- FAILS BY DESIGN: the keystore reader takes a number by its value.

It takes it by its JSON text: `4e0` is read as the version 4 and `4.0` is refused.

Both are the integer 4. -/
def keystoreNumberByValue : Property IO := pureIO do
  let read (text : String) : Option Nat :=
    (Lean.Json.parse text).toOption.bind fun json => (Keystore.number "version" json).toOption
  read "4" === some 4
  read "4e0" === some 4
  read "4.0" === some 4

end HashesProperty

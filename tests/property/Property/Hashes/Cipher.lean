import Property.Hashes.Common
import EthLib.Cryptography.ChaCha20Poly1305
import EthLib.Cryptography.X25519

/-!
# AES and its modes, ChaCha20-Poly1305 and X25519 against their references
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace HashesProperty

/-! ## AES -/

/-- The forward cipher and its inverse are the reference's, for keys of 128 and of 256 bits. -/
def aesBlock (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let block ← forAll (genBytesOf 16)
  pure do
    let input : Aes.Block := vec 16 block
    hexv (aesCiph key input) === (← oracle.ask ["aes", hex key, hex block])
    let inverse := if key.size = 16 then Aes.ciphInv .aes128 (vec _ key) input
      else Aes.ciphInv .aes256 (vec _ key) input
    hexv inverse === (← oracle.ask ["aesinv", hex key, hex block])

/-- A counter block a few steps before its low bytes wrap: `k` bytes of ones at the end. -/
def genCounter : Gen ByteArray :=
  Gen.frequency [
    (2, genBytesN 16),
    (5, Gen.zipWith (fun (head : ByteArray) (kd : Nat × Nat) =>
        let ones := kd.1
        let tail : ByteArray := ⟨(Array.replicate ones 0xff).modify (ones - 1)
          (· - UInt8.ofNat kd.2)⟩
        head.extract 0 (16 - ones) ++ tail)
      (genBytesOf 16) (Gen.zip (Gen.element [1, 2, 4, 8, 12, 15, 16]) (Gen.nat (.constant 0 3))))]

/-- The width of the incrementing function: the usual ones, none, and past the block. -/
def genWidth : Gen Nat :=
  Gen.frequency [(6, Gen.element [128, 64, 32, 16, 8, 1, 0, 127, 129, 200]),
    (2, Gen.nat (.constant 0 128))]

/-- CTR is that of SP 800-38A §6.5 with the incrementing function of Appendix B.1.

The counters start where their low `m` bits wrap, at 2^8, 2^32, 2^64 and 2^128. -/
def aesCtr (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let m ← forAll genWidth
  let counter ← forAll genCounter
  let data ← forAll (genBytes (.linear 0 90))
  pure do
    hex (Aes.ctr (aesCiph key) m (vec 16 counter) data)
      === (← oracle.ask ["ctr", hex key, toString m, hex counter, hex data])

/-- A length of text or of additional data: none, and around one and two blocks. -/
def genTextLen : Gen Nat :=
  Gen.frequency [(4, Gen.element [0, 1, 15, 16, 17, 31, 32, 33]), (2, Gen.nat (.linear 0 70))]

/-- The length of a GCM IV: 96 bits, the other lengths, and none. -/
def genIvLen : Gen Nat :=
  Gen.frequency [(4, pure 12), (5, Gen.element [0, 1, 8, 11, 13, 15, 16, 17, 32, 60])]

/-- A tag length in bytes: the five supported, the two short ones, and others. -/
def genTagLen : Gen Nat :=
  Gen.frequency [(8, Gen.element [16, 15, 14, 13, 12]), (2, Gen.element [8, 4, 0, 11, 17, 32])]

/-- The pair of an answer, in hexadecimal, or `error`. -/
def pairOf {ε : Type} (result : Except ε (ByteArray × ByteArray)) : String :=
  match result with
  | .ok (c, tag) => s!"{hex c} {hex tag}"
  | .error _ => "error"

/-- GCM encryption is the reference's.

This covers any IV length, empty text or additional data.

It also covers the tag lengths that SP 800-38D §5.2.1.2 and Appendix C leave. -/
def gcmEncrypt (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let t ← forAll genTagLen
  let iv ← forAll (do genBytesOf (← genIvLen))
  let p ← forAll (do genBytesOf (← genTextLen))
  let aad ← forAll (do genBytesOf (← genTextLen))
  pure do
    pairOf (Aes.Gcm.encrypt (aesCiph key) t iv p aad)
      === (← oracle.ask ["gcm_enc", hex key, toString t, hex iv, hex p, hex aad])

/-- What is changed in a sealed message before it is opened. -/
inductive Tamper where
  | none | tag | text | aad | nonce | shortTag | longTag
  deriving Repr, BEq, Inhabited

/-- A change, the honest message most often. -/
def genTamper : Gen Tamper :=
  Gen.frequency [(3, pure .none),
    (6, Gen.element [.tag, .text, .aad, .nonce, .shortTag, .longTag])]

/-- GCM decryption opens what the reference opens.

A message with one bit changed in the tag, the ciphertext, the additional data or the IV is refused.

So is a tag of another length. -/
def gcmDecrypt (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let t ← forAll (Gen.element [16, 15, 14, 13, 12])
  let iv ← forAll (do genBytesOf (← genIvLen))
  let p ← forAll (do genBytesOf (← genTextLen))
  let aad ← forAll (do genBytesOf (← genTextLen))
  let tamper ← forAll genTamper
  let bit ← forAll (Gen.nat (.constant 0 1023))
  pure do
    match Aes.Gcm.encrypt (aesCiph key) t iv p aad with
    | .error _ => ensure iv.isEmpty "encryption refused a valid input"
    | .ok (c, tag) =>
      let (iv, c, aad, tag) := match tamper with
        | .none => (iv, c, aad, tag)
        | .tag => (iv, c, aad, flipBit tag bit)
        | .text => (iv, flipBit c bit, aad, tag)
        | .aad => (iv, c, flipBit aad bit, tag)
        | .nonce => (flipBit iv bit, c, aad, tag)
        | .shortTag => (iv, c, aad, tag.extract 0 (tag.size - 1))
        | .longTag => (iv, c, aad, tag.push 0)
      let expected ← oracle.ask ["gcm_dec", hex key, toString t, hex iv, hex c, hex aad, hex tag]
      answerOf (Aes.Gcm.decrypt (aesCiph key) t iv c aad tag) === expected
      if tamper == .none then expected === hex p

/-! ## ChaCha20 and Poly1305 -/

/-- A block counter: any, or a few blocks before `2^32`. -/
def genBlockCounter : Gen Nat :=
  Gen.frequency [(3, genNatBits 32), (3, (2 ^ 32 - 1 - ·) <$> Gen.nat (.constant 0 4))]

/-- A ChaCha20 block is the reference's keystream at that counter. -/
def chachaBlock (oracle : Oracle) : Property IO := propertyM do
  let (key, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 12))
  let counter ← forAll genBlockCounter
  pure do
    hexv (ChaCha20Poly1305.block (vec 32 key) (UInt32.ofNat counter) (vec 12 nonce))
      === (← oracle.ask ["chacha", hex key, toString counter, hex nonce,
        hex ⟨Array.replicate 64 0⟩])

/-- ChaCha20 encryption is the reference's.

It is refused exactly when a block would need the counter `2^32`. -/
def chachaCrypt (oracle : Oracle) : Property IO := propertyM do
  let (key, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 12))
  let counter ← forAll genBlockCounter
  let data ← forAll (do genBytesN (← genLen 64 4))
  pure do
    let blocks := (data.size + 63) / 64
    match ChaCha20Poly1305.crypt (vec 32 key) (UInt32.ofNat counter) (vec 12 nonce) data with
    | .error _ => ensure (counter + blocks > 2 ^ 32) "refused below the last counter"
    | .ok out =>
      ensure (counter + blocks ≤ 2 ^ 32) "accepted past the last counter"
      hex out === (← oracle.ask ["chacha", hex key, toString counter, hex nonce, hex data])

/-- Poly1305 is the reference's: keys and messages of ones reach the carries past `2^130 - 5`. -/
def poly1305 (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll (genBytesOf 32)
  let msg ← forAll (genMsg 16 4)
  pure do
    hexv (ChaCha20Poly1305.poly1305 (vec 32 key) msg)
      === (← oracle.ask ["poly1305", hex key, hex msg])

/-- The AEAD seals as the reference does. -/
def aeadEncrypt (oracle : Oracle) : Property IO := propertyM do
  let (key, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 12))
  let aad ← forAll (do genBytesOf (← genTextLen))
  let p ← forAll (do genBytesOf (← genLen 64 2))
  pure do
    let got := (ChaCha20Poly1305.encrypt (vec 32 key) (vec 12 nonce) aad p).map
      fun (c, tag) => (c, unvec tag)
    pairOf got === (← oracle.ask ["aead_enc", hex key, hex nonce, hex aad, hex p])

/-- The AEAD opens what the reference opens, and refuses a message with one bit changed. -/
def aeadDecrypt (oracle : Oracle) : Property IO := propertyM do
  let (key, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 12))
  let aad ← forAll (do genBytesOf (← genTextLen))
  let p ← forAll (do genBytesOf (← genTextLen))
  let tamper ← forAll (Gen.frequency [(2, pure Tamper.none),
    (6, Gen.element [.tag, .text, .aad, .nonce])])
  let bit ← forAll (Gen.nat (.constant 0 1023))
  pure do
    match ChaCha20Poly1305.encrypt (vec 32 key) (vec 12 nonce) aad p with
    | .error _ => failWith "encryption refused a valid input"
    | .ok (c, tag) =>
      let tag := unvec tag
      let (nonce, c, aad, tag) := match tamper with
        | .tag => (nonce, c, aad, flipBit tag bit)
        | .text => (nonce, flipBit c bit, aad, tag)
        | .aad => (nonce, c, flipBit aad bit, tag)
        | .nonce => (flipBit nonce bit, c, aad, tag)
        | _ => (nonce, c, aad, tag)
      let expected ← oracle.ask ["aead_dec", hex key, hex nonce, hex aad, hex c, hex tag]
      let got := ChaCha20Poly1305.decrypt (vec 32 key) (vec 12 nonce) aad c (vec 16 tag)
      answerOf got === expected
      if tamper == .none then expected === hex p

/-! ## X25519 -/

/-- The u-coordinates of the points of small order, and their other encodings below `2^255`. -/
def lowOrder : List Nat :=
  let p := 2 ^ 255 - 19
  [0, 1, 325606250916557431795983626356110631294008115727848805560023387167927233504,
    39382357235489614581723060781553021112529911719440698176882885853963445705823,
    p - 1, p, p + 1]

/-- A u-coordinate: any, of small order, or non-canonical (`p` to `2^255 - 1`).

Each comes with the high bit set or not. -/
def genU : Gen ByteArray := do
  let u ← Gen.frequency [
    (3, genNatBits 255),
    (2, Gen.element lowOrder),
    (2, (2 ^ 255 - 19 + ·) <$> Gen.nat (.constant 0 18)),
    (1, Gen.element [9, 2, 2 ^ 255 - 20, 2 ^ 255 - 1])]
  let high ← Gen.bool
  pure (unvec (Base.uintToBytes 32 (if high then u + 2 ^ 255 else u)))

/-- X25519 is the function of RFC 7748 §5.

It masks the high bit of the coordinate and reduces a non-canonical one.

It gives zero on a point of small order. -/
def x25519 (oracle : Oracle) : Property IO := propertyM do
  let scalar ← forAll (genBytesOf 32)
  let u ← forAll genU
  pure do
    hexv (X25519.x25519 (vec 32 scalar) (vec 32 u))
      === (← oracle.ask ["x25519", hex scalar, hex u])
    hexv (X25519.publicKey (vec 32 scalar))
      === (← oracle.ask ["x25519", hex scalar, hexv (Base.uintToBytes 32 9)])

end HashesProperty

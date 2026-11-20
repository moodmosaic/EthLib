import Property.Hashes.Common
import EthLib.Cryptography.ChaCha20Poly1305
import EthLib.Cryptography.X25519

/-!
# AES and its modes, ChaCha20-Poly1305 and X25519 against their references
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace HashesProperty

/-! ## AES -/

/-- The forward cipher and its inverse are the reference's, for keys of 128, 192 and 256 bits.

EthLib names the first and the last, and AES-192 is its general cipher with 6 key words. -/
def aesBlock (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let block ← forAll (genBytesOf 16)
  label s!"key: {8 * key.size} bits"
  pure do
    let input : Aes.Block := vec 16 block
    hexv (aesCiph key input) === (← oracle.ask ["aes", hex key, hex block])
    let inverse := if key.size = 16 then Aes.ciphInv .aes128 (vec _ key) input
      else if key.size = 24 then Aes.invCipher 12 (Aes.keyExpansion 6 12 (vec 24 key)) input
      else Aes.ciphInv .aes256 (vec _ key) input
    hexv inverse === (← oracle.ask ["aesinv", hex key, hex block])

/-- The key words and the rounds of the general cipher: those of AES, of Rijndael, or any. -/
def genRijndael : Gen (Nat × Nat) :=
  Gen.frequency [
    (3, Gen.element [(4, 10), (6, 12), (8, 14)]),
    (2, Gen.element [(5, 11), (7, 13)]),
    (2, Gen.zip (Gen.element [4, 6, 8]) (Gen.nat (.constant 0 16))),
    (2, Gen.zip (Gen.nat (.constant 1 10)) (Gen.element [0, 1, 2])),
    (5, Gen.zip (Gen.nat (.constant 1 10)) (Gen.nat (.constant 0 16)))]

/-- The general cipher and key expansion are those of FIPS 197 at any `Nk` and `Nr`.

`keyExpansion` and `cipher` take both numbers, and AES fixes three pairs of them.

The reference is Algorithms 1 to 3 written from the text, which a library confirms at those pairs.

A key of more than 6 words takes the extra SUBWORD of Algorithm 2, line 11.

A key longer than the schedule is cut, and a cipher of no round is its last round alone. -/
def rijndael (oracle : Oracle) : Property IO := propertyM do
  let (nk, nr) ← forAll genRijndael
  let key ← forAll (genBytesOf (4 * nk))
  let block ← forAll (genBytesOf 16)
  classify "a pair of AES: 4 and 10, 6 and 12, 8 and 14"
    ([(4, 10), (6, 12), (8, 14)].contains (nk, nr))
  classify "a key of Rijndael that AES leaves out: 5 or 7 words" (nk == 5 || nk == 7)
  classify "Nk: under 4 words" (nk < 4)
  classify "Nk: above 6, the extra SUBWORD" (nk > 6 && 4 * (nr + 1) > nk + 4)
  classify "Nk: above 8 words" (nk > 8)
  classify "the key is longer than the schedule" (nk > 4 * (nr + 1))
  classify "Nr: no round" (nr == 0)
  classify "Nr: one round, with no middle round" (nr == 1)
  classify "Nr: above 14" (nr > 14)
  classify "the round constant passes x^7, reduced" ((4 * (nr + 1) - 1) / nk > 8)
  pure do
    let schedule := Aes.keyExpansion nk nr (vec (4 * nk) key)
    let words := ["rijndael", toString nk, toString nr, hex key, hex block]
    hexv (Aes.cipher nr schedule (vec 16 block)) === (← oracle.ask words)
    hexv (Aes.invCipher nr schedule (vec 16 block))
      === (← oracle.ask ("rijndaelinv" :: words.drop 1))

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

/-- The width of the incrementing function: the usual ones, none, past the block, and any. -/
def genWidth : Gen Nat :=
  Gen.frequency [(5, Gen.element [128, 64, 32, 16, 8, 1, 0, 127, 129, 200]),
    (4, Gen.nat (.constant 0 128))]

/-- The `len` big-endian bytes of a number, its higher bytes dropped. -/
def beBytes (len n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := len) fun i => UInt8.ofNat (n >>> (8 * (len - 1 - i.val)))⟩

/-- A counter block for a width of `m` bits: any, or one whose low `m` bits are about to wrap. -/
def genCounterFor (m : Nat) : Gen ByteArray :=
  let top := 2 ^ min m 128
  Gen.frequency [
    (2, genCounter),
    (3, Gen.zipWith (fun (head : ByteArray) (back : Nat) =>
        beBytes 16 (head.foldl (fun acc b => acc * 256 + b.toNat) 0 / top * top +
          (top - 1 - back % top)))
      (genBytesOf 16) (Gen.nat (.constant 0 3)))]

/-- The number that bytes spell, the first byte most significant. -/
def beNat (bytes : ByteArray) : Nat := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Count the case under the classes of a counter mode: the width, the wrap and the data.

The counter of block `j` is the first one plus `j` in its low `m` bits.

So the low bits wrap inside the data when the last block needs a counter of `2^m` or more. -/
def labelCtr {m : Type → Type} [Monad m] (width : Nat) (counter : ByteArray) (size : Nat) :
    TestT m Unit := do
  let blocks := (size + 15) / 16
  let low := beNat counter % 2 ^ min width 128
  classify "width: 0, the counter never moves" (width == 0)
  classify "width: 1 to 31 bits" (0 < width && width < 32)
  classify "width: 32 bits, as GCM" (width == 32)
  classify "width: 33 to 127 bits" (32 < width && width < 128)
  classify "width: 128 bits, the whole block" (width == 128)
  classify "width: above 128 bits" (width > 128)
  classify "counter: its low bits wrap inside the data"
    (width > 0 && blocks > 0 && low + (blocks - 1) ≥ 2 ^ min width 128)
  classify "counter: the last block uses the last value before the wrap"
    (width > 0 && blocks > 0 && low + (blocks - 1) + 1 == 2 ^ min width 128)
  classify "data: empty" (size == 0)
  classify "data: one block or less" (0 < size && size ≤ 16)
  classify "data: several blocks" (size > 16)
  classify "data: the last block is partial" (size % 16 != 0)

/-- CTR is that of SP 800-38A §6.5 with the incrementing function of Appendix B.1.

A counter starts a few steps before its low `m` bits wrap, for any `m` from 0 to 128 and above.

The cipher is AES under a key of 128, 192 or 256 bits. -/
def aesCtr (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let m ← forAll genWidth
  let counter ← forAll (genCounterFor m)
  let data ← forAll (Gen.frequency [(2, genBytes (.linear 0 90)),
    (1, do genBytesN (16 * (← Gen.nat (.constant 0 5))))])
  label s!"key: {8 * key.size} bits"
  labelCtr m counter data.size
  pure do
    hex (Aes.ctr (aesCiph key) m (vec 16 counter) data)
      === (← oracle.ask ["ctr", hex key, toString m, hex counter, hex data])

/-- A length of text or of additional data: none, and around one and two blocks. -/
def genTextLen : Gen Nat :=
  Gen.frequency [(4, Gen.element [0, 1, 15, 16, 17, 31, 32, 33]), (2, Gen.nat (.linear 0 70))]

/-- The length of a GCM IV that seals: 96 bits, or another length, which goes through GHASH. -/
def genIvLen : Gen Nat :=
  Gen.frequency [(4, pure 12), (3, Gen.element [1, 8, 11, 13, 15]),
    (2, Gen.element [16, 32, 48, 64]), (2, Gen.element [17, 31, 33, 60, 100]),
    (1, Gen.nat (.linear 1 130))]

/-- A tag length in bytes: the five supported, the two short ones, and others. -/
def genTagLen : Gen Nat :=
  Gen.frequency [(8, Gen.element [16, 15, 14, 13, 12]), (2, Gen.element [8, 4]),
    (2, Gen.element [0, 11, 17, 32]), (1, Gen.nat (.constant 0 20))]

/-- Count the case under its tag length: each one of SP 800-38D §5.2.1.2, or another. -/
def labelTag {m : Type → Type} [Monad m] (what : String) (t : Nat) : TestT m Unit :=
  if [16, 15, 14, 13, 12, 8, 4].contains t then label s!"{what}: {t} bytes"
  else label s!"{what}: a length that SP 800-38D does not have"

/-- The pair of an answer, in hexadecimal, or `error`. -/
def pairOf {ε : Type} (result : Except ε (ByteArray × ByteArray)) : String :=
  match result with
  | .ok (c, tag) => s!"{hex c} {hex tag}"
  | .error _ => "error"

/-- Count the case under the classes of a GCM call: the key, the IV, the text and the data.

An IV of 96 bits is the counter block itself, and any other length goes through GHASH. -/
def labelGcm {m : Type → Type} [Monad m] (key iv text aad : ByteArray) : TestT m Unit := do
  label s!"key: {8 * key.size} bits"
  classify "IV: 96 bits, the counter block itself" (iv.size == 12)
  classify "IV: by GHASH, under a block" (0 < iv.size && iv.size < 16 && iv.size != 12)
  classify "IV: by GHASH, whole blocks" (iv.size > 0 && iv.size % 16 == 0)
  classify "IV: by GHASH, over a block with a partial one" (iv.size > 16 && iv.size % 16 != 0)
  classify "text: empty" text.isEmpty
  classify "text: one block or less" (0 < text.size && text.size ≤ 16)
  classify "text: several blocks" (text.size > 16)
  classify "text: the last block is partial" (text.size % 16 != 0)
  classify "additional data: empty" aad.isEmpty
  classify "additional data: the last block is partial" (aad.size % 16 != 0)
  classify "additional data: whole blocks" (aad.size > 0 && aad.size % 16 == 0)

/-- An element of GF(2^128) as a block: zero, one, one bit, all ones, the constant `R`, or any.

The first bit of a block is the coefficient of `x^0`, so the element one is `0x80` then zeros. -/
def genFieldBlock : Gen ByteArray :=
  Gen.frequency [(1, pure (beBytes 16 0)), (1, pure (beBytes 16 (2 ^ 127))),
    (1, pure (beBytes 16 (0xe1 * 2 ^ 120))), (1, pure (beBytes 16 (2 ^ 128 - 1))),
    (3, (fun k => beBytes 16 (2 ^ k)) <$> Gen.nat (.constant 0 127)), (6, genBytesOf 16)]

/-- The product of GF(2^128) and GHASH are those of SP 800-38D §§6.3 and 6.4, on any blocks.

Inside GCM the hash subkey is a cipher output and never a chosen element.

The reference multiplies the two polynomials and reduces by `x^128 + x^7 + x^2 + x + 1`. -/
def gcmField (oracle : Oracle) : Property IO := propertyM do
  let (x, y) ← forAll (Gen.zip genFieldBlock genFieldBlock)
  let blocks ← forAll (Gen.list (.constant 0 4) genFieldBlock)
  let (xn, yn) := (beNat x, beNat y)
  classify "a factor is zero" (xn == 0 || yn == 0)
  classify "a factor is one" (xn == 2 ^ 127 || yn == 2 ^ 127)
  classify "the first factor is a power of x" (xn != 0 && xn &&& (xn - 1) == 0)
  classify "the last bit of a factor is set, so a shift reduces" (xn % 2 == 1 || yn % 2 == 1)
  classify "GHASH: of no block" blocks.isEmpty
  classify "GHASH: of several blocks" (blocks.length > 1)
  pure do
    hexv (Aes.Gcm.mul (vec 16 x) (vec 16 y)) === (← oracle.ask ["gf128", hex x, hex y])
    let data := blocks.foldl (· ++ ·) ByteArray.empty
    hexv (Aes.Gcm.ghash (vec 16 x) (blocks.map (vec 16)))
      === (← oracle.ask ["ghash", hex x, hex data])

/-- GCM encryption is the reference's.

This covers any IV length, empty text or additional data, and keys of 128, 192 and 256 bits.

It also covers the tag lengths that SP 800-38D §5.2.1.2 and Appendix C leave. -/
def gcmEncrypt (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let t ← forAll genTagLen
  let iv ← forAll (do genBytesOf (← Gen.frequency [(12, genIvLen), (1, pure 0)]))
  let p ← forAll (do genBytesOf (← genTextLen))
  let aad ← forAll (do genBytesOf (← genTextLen))
  labelGcm key iv p aad
  classify "IV: empty" iv.isEmpty
  labelTag "tag" t
  pure do
    let got := Aes.Gcm.encrypt (aesCiph key) t iv p aad
    labelOutcome got
    pairOf got === (← oracle.ask ["gcm_enc", hex key, toString t, hex iv, hex p, hex aad])

/-- What is changed in a sealed message before it is opened. -/
inductive Tamper where
  | none | tag | text | aad | nonce | shortTag | longTag | emptyIv
  deriving Repr, BEq, Inhabited

/-- A change, the honest message most often. -/
def genTamper : Gen Tamper :=
  Gen.frequency [(3, pure .none),
    (7, Gen.element [.tag, .text, .aad, .nonce, .shortTag, .longTag, .emptyIv])]

/-- GCM decryption opens what the reference opens.

A message with one bit changed in the tag, the ciphertext, the additional data or the IV is refused.

So is a tag of another length than the declared one, and a declared length that is not supported.

So is an empty IV. -/
def gcmDecrypt (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let t ← forAll (Gen.element [16, 15, 14, 13, 12])
  -- The length that decryption is told: the one that sealed, another supported one, or neither.
  let declared ← forAll (Gen.frequency [(10, pure t), (1, Gen.element [16, 15, 14, 13, 12]),
    (1, Gen.element [8, 4]), (1, Gen.element [0, 11, 17])])
  let iv ← forAll (do genBytesOf (← genIvLen))
  let p ← forAll (do genBytesOf (← genTextLen))
  let aad ← forAll (do genBytesOf (← genTextLen))
  let tamper ← forAll genTamper
  let bit ← forAll (Gen.nat (.constant 0 1023))
  labelGcm key iv p aad
  labelTag "sealed with a tag" t
  classify "declared: the length that sealed" (declared == t)
  classify "declared: another supported length" (declared != t && declared ≥ 12 && declared ≤ 16)
  classify "declared: 8 or 4 bytes" (declared == 8 || declared == 4)
  classify "declared: a length that SP 800-38D does not have"
    (![16, 15, 14, 13, 12, 8, 4].contains declared)
  label s!"change: {ctorName tamper}"
  pure do
    match Aes.Gcm.encrypt (aesCiph key) t iv p aad with
    | .error _ => failWith "encryption refused a valid input"
    | .ok (c, tag) =>
      let (iv, c, aad, tag) := match tamper with
        | .none => (iv, c, aad, tag)
        | .tag => (iv, c, aad, flipBit tag bit)
        | .text => (iv, flipBit c bit, aad, tag)
        | .aad => (iv, c, flipBit aad bit, tag)
        | .nonce => (flipBit iv bit, c, aad, tag)
        | .shortTag => (iv, c, aad, tag.extract 0 (tag.size - 1))
        | .longTag => (iv, c, aad, tag.push 0)
        | .emptyIv => (.empty, c, aad, tag)
      let expected ← oracle.ask
        ["gcm_dec", hex key, toString declared, hex iv, hex c, hex aad, hex tag]
      let got := Aes.Gcm.decrypt (aesCiph key) declared iv c aad tag
      labelOutcome got
      answerOf got === expected
      if tamper == .none && declared == t then expected === hex p

/-- GCM is that of SP 800-38D where its 32-bit counter wraps inside the text.

A 96-bit IV starts the counter at 2, so no message reaches the wrap.

Another IV goes through GHASH, which is linear, so the reference solves for the IV of a counter.

EthLib then takes that IV to the chosen pre-counter block, and encrypts across the wrap.

The reference is Algorithm 4 written from the text, and a library confirms each answer. -/
def gcmChosen (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll genAesKey
  let head ← forAll (genBytesOf 12)
  let back ← forAll (Gen.nat (.constant 0 4))
  let p ← forAll (do genBytesOf (← Gen.frequency [(1, genTextLen),
    (2, Gen.nat (.constant 17 100))]))
  let aad ← forAll (do genBytesOf (← genTextLen))
  let j0 := head ++ beBytes 4 (2 ^ 32 - 1 - back)
  let blocks := (p.size + 15) / 16
  label s!"key: {8 * key.size} bits"
  classify "the counter wraps on the first block of the text" (back == 0 && blocks > 0)
  classify "the counter wraps inside the text" (back > 0 && blocks > back)
  classify "the text ends on the last counter before the wrap" (blocks == back && blocks > 0)
  classify "the text ends before the wrap" (blocks < back)
  pure do
    let answer ← oracle.ask ["gcm_chosen", hex key, hex j0, hex p, hex aad]
    let [ivHex, c, tag] := answer.splitOn " " | failWith s!"the reference answered {answer}"
    let some iv := unhex? ivHex | failWith "the IV is not hexadecimal"
    hexv (Aes.Gcm.preCounter (aesCiph key Aes.Gcm.zeroBlock) iv) === hex j0
    pairOf (Aes.Gcm.encrypt (aesCiph key) 16 iv p aad) === s!"{c} {tag}"
    let sealed := (unhex? c).getD .empty
    answerOf (Aes.Gcm.decrypt (aesCiph key) 16 iv sealed aad ((unhex? tag).getD .empty))
      === hex p

/-! ## ChaCha20 and Poly1305 -/

/-- A block counter: any, the first ones, or a few blocks before `2^32`. -/
def genBlockCounter : Gen Nat :=
  Gen.frequency [(3, genNatBits 32), (4, (2 ^ 32 - 1 - ·) <$> Gen.nat (.constant 0 4)),
    (2, Gen.element [0, 1, 2])]

/-- A ChaCha20 block is the reference's keystream at that counter. -/
def chachaBlock (oracle : Oracle) : Property IO := propertyM do
  let (key, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 12))
  let counter ← forAll genBlockCounter
  classify "counter: 0" (counter == 0)
  classify "counter: 1, the first of the AEAD text" (counter == 1)
  classify "counter: 2^32 - 1, the last" (counter == 2 ^ 32 - 1)
  classify "counter: 2^31 or more, the high bit" (counter ≥ 2 ^ 31)
  pure do
    hexv (ChaCha20Poly1305.block (vec 32 key) (UInt32.ofNat counter) (vec 12 nonce))
      === (← oracle.ask ["chacha", hex key, toString counter, hex nonce,
        hex ⟨Array.replicate 64 0⟩])

/-- ChaCha20 encryption is the reference's.

It is refused exactly when a block would need the counter `2^32`. -/
def chachaCrypt (oracle : Oracle) : Property IO := propertyM do
  let (key, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 12))
  let data ← forAll (do genBytesN (← genLen 64 4))
  -- Any counter, or one that leaves the data two blocks short of `2^32` to two blocks past it.
  let counter ← forAll (Gen.frequency [(3, genBlockCounter),
    (3, (fun d => min (2 ^ 32 - 1) (2 ^ 32 + 2 - d - (data.size + 63) / 64)) <$>
      Gen.nat (.constant 0 4))])
  labelLength "data" 64 data.size
  classify "data: the last block is partial" (data.size % 64 != 0)
  classify "counter: the data ends on the last counter, 2^32 - 1"
    (data.size > 0 && counter + (data.size + 63) / 64 == 2 ^ 32)
  classify "counter: the data needs one counter past the last"
    (counter + (data.size + 63) / 64 == 2 ^ 32 + 1)
  classify "counter: the data needs two counters or more past the last"
    (counter + (data.size + 63) / 64 > 2 ^ 32 + 1)
  pure do
    let blocks := (data.size + 63) / 64
    let got := ChaCha20Poly1305.crypt (vec 32 key) (UInt32.ofNat counter) (vec 12 nonce) data
    labelOutcome got
    match got with
    | .error _ => ensure (counter + blocks > 2 ^ 32) "refused below the last counter"
    | .ok out =>
      ensure (counter + blocks ≤ 2 ^ 32) "accepted past the last counter"
      hex out === (← oracle.ask ["chacha", hex key, toString counter, hex nonce, hex data])

/-- The accumulator and the pad of Poly1305 on `Nat`, RFC 8439 §2.5.1.

It is here to name the classes of a case, and it is a second answer for the tag. -/
def polyModel (key msg : ByteArray) : Nat × Nat × Nat :=
  let le (bytes : ByteArray) : Nat := bytes.data.foldr (fun b acc => acc * 256 + b.toNat) 0
  let r := le (key.extract 0 16) &&& 0x0ffffffc0ffffffc0ffffffc0fffffff
  let acc := (List.range ((msg.size + 15) / 16)).foldl (fun acc i =>
    let chunk := msg.extract (16 * i) (16 * i + 16)
    (acc + le chunk + 2 ^ (8 * chunk.size)) * r % (2 ^ 130 - 5)) 0
  (acc, le (key.extract 16 32), r)

/-- Poly1305 is the reference's: keys and messages of ones reach the carries past `2^130 - 5`. -/
def poly1305 (oracle : Oracle) : Property IO := propertyM do
  let key ← forAll (genBytesOf 32)
  let msg ← forAll (genMsg 16 4)
  let (acc, pad, r) := polyModel key msg
  labelLength "message" 16 msg.size
  classify "message: the last block is partial" (msg.size % 16 != 0)
  classify "accumulator: 2^128 or more, its high bits are dropped" (acc ≥ 2 ^ 128)
  classify "tag: the sum with the pad passes 2^128" (acc % 2 ^ 128 + pad ≥ 2 ^ 128)
  classify "r: zero after the clamp" (r == 0)
  pure do
    let tag := ChaCha20Poly1305.poly1305 (vec 32 key) msg
    hexv tag === (← oracle.ask ["poly1305", hex key, hex msg])
    Base.bytesToUint tag === (acc + pad) % 2 ^ 128

/-- Count the case under the classes of an AEAD call: the additional data and the text.

Both are padded to 16 bytes for the tag, and the text is encrypted in blocks of 64. -/
def labelAead {m : Type → Type} [Monad m] (aad text : ByteArray) : TestT m Unit := do
  classify "additional data: empty" aad.isEmpty
  classify "additional data: padded for the tag" (aad.size % 16 != 0)
  classify "additional data: whole blocks of 16" (aad.size > 0 && aad.size % 16 == 0)
  classify "text: empty" text.isEmpty
  classify "text: padded for the tag" (text.size % 16 != 0)
  classify "text: whole blocks of 16" (text.size > 0 && text.size % 16 == 0)
  classify "text: exactly one block of 64" (text.size == 64)
  classify "text: more than one block of 64" (text.size > 64)

/-- The AEAD seals as the reference does. -/
def aeadEncrypt (oracle : Oracle) : Property IO := propertyM do
  let (key, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 12))
  let aad ← forAll (do genBytesOf (← genTextLen))
  let p ← forAll (do genBytesOf (← genLen 64 2))
  labelAead aad p
  pure do
    let got := (ChaCha20Poly1305.encrypt (vec 32 key) (vec 12 nonce) aad p).map
      fun (c, tag) => (c, unvec tag)
    pairOf got === (← oracle.ask ["aead_enc", hex key, hex nonce, hex aad, hex p])

/-- The AEAD opens what the reference opens, and refuses a message with one bit changed. -/
def aeadDecrypt (oracle : Oracle) : Property IO := propertyM do
  let (key, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 12))
  let aad ← forAll (do genBytesOf (← genTextLen))
  let p ← forAll (do genBytesOf (← Gen.choice [genTextLen, genLen 64 2]))
  let tamper ← forAll (Gen.frequency [(2, pure Tamper.none),
    (6, Gen.element [.tag, .text, .aad, .nonce])])
  let bit ← forAll (Gen.nat (.constant 0 1023))
  labelAead aad p
  label s!"change: {ctorName tamper}"
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
      labelOutcome got
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
    (1, pure 9), (1, Gen.element [2, 2 ^ 255 - 20, 2 ^ 255 - 1])]
  let high ← Gen.bool
  pure (unvec (Base.uintToBytes 32 (if high then u + 2 ^ 255 else u)))

/-- X25519 is the function of RFC 7748 §5.

It masks the high bit of the coordinate and reduces a non-canonical one.

It gives zero on a point of small order. -/
def x25519 (oracle : Oracle) : Property IO := propertyM do
  let scalar ← forAll (genBytesOf 32)
  let u ← forAll genU
  let p := 2 ^ 255 - 19
  let uNat := Base.bytesToUint (vec 32 u)
  let low := uNat % 2 ^ 255
  classify "u: the high bit is set, to be masked" (uNat ≥ 2 ^ 255)
  classify "u: not canonical, p to 2^255 - 1" (low ≥ p)
  classify "u: zero after reduction" (low % p == 0)
  classify "u: of small order" (lowOrder.contains low)
  classify "u: the base point 9" (low == 9)
  classify "scalar: a low bit to clear" (scalar.data.getD 0 0 &&& 7 != 0)
  classify "scalar: the high bit to clear" (scalar.data.getD 31 0 &&& 128 != 0)
  classify "scalar: bit 254 to set" (scalar.data.getD 31 0 &&& 64 == 0)
  pure do
    let shared := X25519.x25519 (vec 32 scalar) (vec 32 u)
    classify "the result is zero" (shared.toList.all (· == 0))
    hexv shared === (← oracle.ask ["x25519", hex scalar, hex u])
    hexv (X25519.publicKey (vec 32 scalar))
      === (← oracle.ask ["x25519", hex scalar, hexv (Base.uintToBytes 32 9)])

end HashesProperty

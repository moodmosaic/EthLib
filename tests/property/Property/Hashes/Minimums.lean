import Hedgehog

/-!
# The share of each class that a long run of the hashes driver must reach

Each minimum is about a third of the least share seen in runs of 1,000 cases.

A class under 5% has none, and a change to a keystore has none: there are 40 of them.
-/

namespace HashesProperty

/-- For each property, the minimum share in percent of each class that it names. -/
def minimums : List (String × List (Nat × String)) := [
  ("Keccak-256", [
    (2, "message: 1,000 bytes or more"), (2, "message: a block plus one"),
    (2, "message: exactly a block"), (9, "message: many blocks"),
    (12, "message: under a block"), (4, "padding: a whole block"),
    (4, "padding: the one byte 0x81"), (23, "padding: two bytes or more, under a block")]),
  ("Keccak-512", [
    (2, "message: 1,000 bytes or more"), (2, "message: a block plus one"),
    (1, "message: empty"), (2, "message: exactly a block"), (11, "message: many blocks"),
    (11, "message: under a block"), (5, "padding: a whole block"),
    (4, "padding: the one byte 0x81"), (22, "padding: two bytes or more, under a block")]),
  ("the Keccak sponge at each rate of the family", [
    (2, "message: a block plus one"), (2, "message: exactly a block"),
    (9, "message: many blocks"), (11, "message: under a block"), (6, "padding: a whole block"),
    (4, "padding: the one byte 0x81"), (22, "padding: two bytes or more, under a block"),
    (8, "rate: 104 bytes"), (8, "rate: 136 bytes"), (7, "rate: 144 bytes"),
    (8, "rate: 72 bytes")]),
  ("SHA-256", [
    (2, "message: 1,000 bytes or more"), (1, "message: a block plus one"),
    (3, "message: empty"), (1, "message: exactly a block"), (12, "message: many blocks"),
    (9, "message: under a block"), (2, "padding: fills the last block exactly"),
    (18, "padding: fits in the last block"), (10, "padding: needs one more block")]),
  ("RIPEMD-160", [
    (2, "message: 1,000 bytes or more"), (1, "message: a block plus one"),
    (2, "message: empty"), (12, "message: many blocks"), (9, "message: under a block"),
    (3, "padding: fills the last block exactly"), (19, "padding: fits in the last block"),
    (9, "padding: needs one more block")]),
  ("CRC-32 and CRC-32C", [
    (6, "message: empty"), (5, "message: exactly 4 bytes"),
    (12, "message: longer than 4 bytes"), (7, "message: shorter than the register of 4 bytes")]),
  ("BLAKE2b F", [
    (7, "rounds: 1 to 9"), (4, "rounds: 10 or 11, the schedule starts again"),
    (1, "rounds: 12, as BLAKE2b"), (2, "rounds: 255 or more"), (17, "rounds: above 12"),
    (1, "rounds: none"), (16, "the final block"),
    (21, "the high word of the offset is not zero"),
    (11, "the high word of the offset is zero, as BLAKE2b")]),
  ("HMAC-SHA-256", [
    (1, "key: empty"), (3, "key: exactly a block"),
    (13, "key: longer than a block, hashed first"), (14, "key: under a block"),
    (3, "message: a block plus one"), (1, "message: empty"), (2, "message: exactly a block"),
    (3, "message: many blocks"), (14, "message: under a block")]),
  ("HKDF-Expand", [
    (3, "info: empty"), (7, "key: exactly 32 bytes"), (21, "outcome: accepted"),
    (8, "outcome: refused, keyTooShort"), (2, "outcome: refused, outputTooLong"),
    (2, "output: empty"), (1, "output: one past the limit"),
    (17, "output: several blocks, the last one cut"), (7, "output: under a block"),
    (6, "output: whole blocks")]),
  ("HKDF", [
    (3, "key material: empty"), (29, "outcome: accepted"),
    (3, "outcome: refused, outputTooLong"), (2, "output: empty"),
    (1, "output: one past the limit"), (17, "output: several blocks, the last one cut"),
    (7, "output: under a block"), (5, "output: whole blocks"), (16, "salt: empty"),
    (3, "salt: longer than a block")]),
  ("TLS 1.3 HKDF-Expand-Label", [
    (2, "context: 255 bytes, the longest"), (5, "context: empty"),
    (1, "label: 249 bytes, the longest"), (13, "outcome: accepted"),
    (1, "outcome: refused, contextLength"), (2, "outcome: refused, hkdf"),
    (11, "outcome: refused, labelLength"), (2, "outcome: refused, lengthOverflow")]),
  ("Concatenation KDF", [
    (3, "info: empty"), (30, "outcome: accepted"), (2, "outcome: refused, emptyOutput"),
    (2, "output: empty"), (19, "output: several blocks, the last one cut"),
    (7, "output: under a block"), (4, "output: whole blocks"), (1, "secret: empty")]),
  ("PBKDF2", [
    (13, "iterations: one"), (15, "iterations: several"), (26, "outcome: accepted"),
    (1, "outcome: refused, emptyOutput"), (4, "outcome: refused, zeroIterations"),
    (2, "output: empty"), (18, "output: several blocks, the last one cut"),
    (7, "output: under a block"), (4, "output: whole blocks"),
    (6, "password: longer than a block, hashed first"), (3, "salt: empty")]),
  ("scrypt steps", [
    (23, "BlockMix: accepted"), (3, "BlockMix: refused, invalidBlockSize"),
    (5, "BlockMix: refused, invalidInputSize"), (26, "N: 2, 4, 8 or 16"),
    (18, "ROMix: accepted"), (3, "ROMix: refused, invalidBlockSize"),
    (6, "ROMix: refused, invalidCost"), (4, "ROMix: refused, invalidInputSize"),
    (26, "Salsa20/8: accepted"), (5, "Salsa20/8: refused, invalidInputSize"),
    (26, "block: of 128 r bytes"), (3, "r = 0"), (10, "r = 1"), (9, "r = 2"), (9, "r = 3")]),
  ("scrypt", [
    (7, "cost: a power of two, too large for r"), (3, "cost: not a power of two"),
    (14, "outcome: accepted"), (1, "outcome: refused, emptyOutput"),
    (2, "outcome: refused, invalidBlockSize"), (10, "outcome: refused, invalidCost"),
    (2, "outcome: refused, invalidParallelization"), (19, "p: several blocks mixed"),
    (4, "r: 4 or more")]),
  ("AES block", [
    (11, "key: 128 bits"), (10, "key: 192 bits"), (10, "key: 256 bits")]),
  ("the general cipher at any key length and round count", [
    (10, "Nk: above 6, the extra SUBWORD"), (3, "Nk: above 8 words"), (4, "Nk: under 4 words"),
    (2, "Nr: no round"), (2, "Nr: one round, with no middle round"),
    (8, "a key of Rijndael that AES leaves out: 5 or 7 words"),
    (7, "a pair of AES: 4 and 10, 6 and 12, 8 and 14"),
    (2, "the key is longer than the schedule"), (10, "the round constant passes x^7, reduced")]),
  ("AES-CTR", [
    (7, "counter: its low bits wrap inside the data"),
    (4, "counter: the last block uses the last value before the wrap"), (3, "data: empty"),
    (11, "data: one block or less"), (18, "data: several blocks"),
    (19, "data: the last block is partial"), (10, "key: 128 bits"), (10, "key: 192 bits"),
    (11, "key: 256 bits"), (2, "width: 0, the counter never moves"), (8, "width: 1 to 31 bits"),
    (1, "width: 128 bits, the whole block"), (14, "width: 33 to 127 bits"),
    (3, "width: above 128 bits")]),
  ("the product of GF(2^128) and GHASH", [
    (6, "GHASH: of no block"), (19, "GHASH: of several blocks"), (4, "a factor is one"),
    (7, "a factor is zero"), (10, "the first factor is a power of x"),
    (16, "the last bit of a factor is set, so a shift reduces")]),
  ("AES-GCM encryption", [
    (10, "IV: 96 bits, the counter block itself"),
    (6, "IV: by GHASH, over a block with a partial one"), (7, "IV: by GHASH, under a block"),
    (4, "IV: by GHASH, whole blocks"), (2, "IV: empty"), (3, "additional data: empty"),
    (23, "additional data: the last block is partial"), (5, "additional data: whole blocks"),
    (10, "key: 128 bits"), (10, "key: 192 bits"), (11, "key: 256 bits"),
    (19, "outcome: accepted"), (5, "outcome: refused, shortTag"),
    (6, "outcome: refused, tagLength"), (4, "tag: 12 bytes"), (3, "tag: 13 bytes"),
    (4, "tag: 14 bytes"), (4, "tag: 15 bytes"), (3, "tag: 16 bytes"), (2, "tag: 4 bytes"),
    (2, "tag: 8 bytes"), (6, "tag: a length that SP 800-38D does not have"), (3, "text: empty"),
    (13, "text: one block or less"), (15, "text: several blocks"),
    (24, "text: the last block is partial")]),
  ("AES-GCM decryption", [
    (11, "IV: 96 bits, the counter block itself"),
    (6, "IV: by GHASH, over a block with a partial one"), (8, "IV: by GHASH, under a block"),
    (5, "IV: by GHASH, whole blocks"), (2, "additional data: empty"),
    (24, "additional data: the last block is partial"), (6, "additional data: whole blocks"),
    (3, "change: aad"), (3, "change: emptyIv"), (3, "change: longTag"), (2, "change: nonce"),
    (9, "change: none"), (3, "change: shortTag"), (3, "change: tag"), (3, "change: text"),
    (2, "declared: 8 or 4 bytes"), (2, "declared: a length that SP 800-38D does not have"),
    (25, "declared: the length that sealed"), (10, "key: 128 bits"), (11, "key: 192 bits"),
    (10, "key: 256 bits"), (7, "outcome: accepted"), (10, "outcome: refused, authentication"),
    (2, "outcome: refused, ivLength"), (2, "outcome: refused, shortTag"),
    (9, "outcome: refused, tagLength"), (6, "sealed with a tag: 12 bytes"),
    (6, "sealed with a tag: 13 bytes"), (6, "sealed with a tag: 14 bytes"),
    (6, "sealed with a tag: 15 bytes"), (6, "sealed with a tag: 16 bytes"), (3, "text: empty"),
    (12, "text: one block or less"), (16, "text: several blocks"),
    (23, "text: the last block is partial")]),
  ("AES-GCM across the wrap of its counter", [
    (8, "key: 128 bits"), (8, "key: 192 bits"), (7, "key: 256 bits"),
    (10, "the counter wraps inside the text"),
    (4, "the counter wraps on the first block of the text"),
    (6, "the text ends before the wrap"),
    (2, "the text ends on the last counter before the wrap")]),
  ("ChaCha20 block", [
    (2, "counter: 0"), (2, "counter: 1, the first of the AEAD text"),
    (19, "counter: 2^31 or more, the high bit"), (2, "counter: 2^32 - 1, the last")]),
  ("ChaCha20 encryption", [
    (7, "counter: the data ends on the last counter, 2^32 - 1"),
    (3, "counter: the data needs one counter past the last"),
    (1, "counter: the data needs two counters or more past the last"),
    (2, "data: a block plus one"), (1, "data: empty"), (2, "data: exactly a block"),
    (9, "data: many blocks"), (26, "data: the last block is partial"),
    (11, "data: under a block"), (28, "outcome: accepted"),
    (5, "outcome: refused, counterExhausted")]),
  ("Poly1305", [
    (20, "accumulator: 2^128 or more, its high bits are dropped"),
    (2, "message: a block plus one"), (2, "message: empty"), (2, "message: exactly a block"),
    (8, "message: many blocks"), (26, "message: the last block is partial"),
    (11, "message: under a block"), (3, "r: zero after the clamp"),
    (14, "tag: the sum with the pad passes 2^128")]),
  ("ChaCha20-Poly1305 encryption", [
    (2, "additional data: empty"), (24, "additional data: padded for the tag"),
    (5, "additional data: whole blocks of 16"), (1, "text: empty"),
    (3, "text: exactly one block of 64"), (13, "text: more than one block of 64"),
    (26, "text: padded for the tag"), (4, "text: whole blocks of 16")]),
  ("ChaCha20-Poly1305 decryption", [
    (3, "additional data: empty"), (23, "additional data: padded for the tag"),
    (5, "additional data: whole blocks of 16"), (4, "change: aad"), (5, "change: nonce"),
    (8, "change: none"), (5, "change: tag"), (6, "change: text"), (8, "outcome: accepted"),
    (24, "outcome: refused, authenticationFailed"), (2, "text: empty"),
    (6, "text: more than one block of 64"), (24, "text: padded for the tag"),
    (5, "text: whole blocks of 16")]),
  ("X25519", [
    (25, "scalar: a low bit to clear"), (15, "scalar: bit 254 to set"),
    (16, "scalar: the high bit to clear"), (9, "the result is zero"),
    (10, "u: not canonical, p to 2^255 - 1"), (9, "u: of small order"),
    (3, "u: the base point 9"), (16, "u: the high bit is set, to be masked"),
    (2, "u: zero after reduction")]),
  ("RFC 6979 seed", [
    (9, "hash: above the order, reduced"), (21, "hash: below the order"),
    (14, "key: below the order"), (14, "key: the order or more"), (3, "key: zero"),
    (16, "order: another number of 256 bits"), (8, "order: of P-256"),
    (7, "order: of secp256k1")]),
  ("ERC-2335 keystore", [
    (2, "derived key: 16 to 31 bytes, sealed as the slices of the ERC read it"),
    (21, "derived key: longer than 32 bytes"), (2, "derived key: shorter than 16 bytes"),
    (16, "kdf: pbkdf2"), (16, "kdf: scrypt"), (1, "limit: on both costs exactly, opened"),
    (2, "limit: one byte under the memory"), (2, "limit: one unit under the work"),
    (6, "limit: the memory exactly"), (6, "limit: the work exactly"), (7, "outcome: accepted"),
    (10, "outcome: refused, invalidField"), (1, "outcome: refused, limitExceeded"),
    (2, "outcome: refused, pbkdf2"), (2, "outcome: refused, scrypt"),
    (3, "outcome: refused, shortKey"), (1, "outcome: refused, unsupportedVersion"),
    (6, "password: holds a character next to a range of control codes"),
    (13, "password: holds a character that NFKD changes"),
    (17, "password: holds a control code"),
    (6, "password: holds the first or the last of a range of control codes"),
    (29, "password: the one that sealed"), (12, "secret: 32 bytes, as a BLS key"),
    (5, "secret: empty"), (18, "secret: more than one block of the cipher")]),
  ("Ethash sizes", [
    (6, "block: the first of its epoch"), (6, "block: the last of its epoch"),
    (3, "cache: the first candidate is prime"), (4, "dataset: the first candidate is prime"),
    (5, "epoch: 0"), (9, "epoch: past 512, beyond the chain's last")]),
  ("Ethash primality and size search", [
    (28, "number: composite"), (3, "number: prime"), (3, "number: the square of a prime"),
    (24, "search: several steps down"), (4, "search: the first candidate is prime"),
    (10, "search: unit 1"), (11, "search: unit 128"), (11, "search: unit 64")]),
  ("Ethash cache, item and proof of work", [
    (4, "cache: more than 16 items"), (3, "cache: one item"), (2, "cache: two items"),
    (12, "dataset: its size is not whole pairs"), (2, "dataset: one pair of items"),
    (13, "index: 2^31 or more"), (24, "index: beyond the cache")]),
  ("Merkle tree", [
    (4, "height: 0"), (4, "height: 1"), (4, "height: 2"), (5, "height: 3"), (4, "height: 4"),
    (5, "height: 5"), (4, "height: 6"), (8, "leaf: the first"), (8, "leaf: the last"),
    (11, "node: a leaf"), (11, "node: the root")]),
  ("Merkle multiproof", [
    (4, "height: 0"), (3, "height: 1"), (4, "height: 2"), (4, "height: 3"), (5, "height: 4"),
    (5, "height: 5"), (4, "height: 6"), (16, "helpers: none"),
    (10, "helpers: on several levels"), (7, "helpers: two or more on one level"),
    (7, "opened: every leaf"), (6, "opened: leaves only, several"),
    (9, "opened: nodes of several levels"), (10, "opened: not in order of position"),
    (15, "opened: one node"), (11, "opened: the root alone"),
    (8, "opened: two siblings, which need no helper between them")]),
  ("paddings as arithmetic", [
    (3, "padding: a whole block"), (3, "padding: fills the last block exactly"),
    (21, "padding: fits in the last block"), (7, "padding: needs one more block"),
    (3, "padding: the one byte 0x81"), (27, "padding: two bytes or more, under a block"),
    (24, "rate: of Keccak-256 or Keccak-512"), (15, "size: its bit length passes 2^32"),
    (4, "size: its bit length passes 2^64, reduced")]),
  ("padded messages", [
    (2, "message: empty"), (16, "message: many blocks"), (7, "message: under a block"),
    (4, "padding: a whole block"), (1, "padding: fills the last block exactly"),
    (25, "padding: fits in the last block"), (5, "padding: needs one more block"),
    (2, "padding: the one byte 0x81"), (25, "padding: two bytes or more, under a block")]),
  ("scrypt cost bound", [
    (5, "r: zero"), (2, "refused: 0 or 1"), (7, "refused: a power of two, too large for r"),
    (17, "refused: not a power of two"), (1, "the largest valid cost of r, 2^(16 r - 1)"),
    (4, "the least cost too large for r, 2^(16 r)"), (6, "valid")]),
  ("ChaCha20-Poly1305 length limits", [
    (4, "additional data: exactly the limit"), (4, "additional data: one past the limit"),
    (7, "outcome: accepted"), (15, "outcome: refused, aadTooLong"),
    (9, "outcome: refused, counterExhausted"), (4, "text: exactly the limit"),
    (4, "text: one past the limit")]),
  ("machine: incremental Keccak-256", [
    (8, "absorb: an empty chunk"), (29, "absorb: the chunk crosses a block"),
    (22, "absorb: the chunk ends exactly on a block"),
    (21, "absorb: the chunk ends one byte before a block"),
    (15, "absorb: the chunk holds two blocks or more"),
    (23, "absorb: the chunk stays inside a block"),
    (6, "digest: 135 bytes pending, the padding is one byte"),
    (15, "digest: after two blocks or more"),
    (7, "digest: nothing pending, the padding is a whole block"), (6, "digest: of nothing")]),
  ("machine: AES-CTR stream", [
    (17, "piece: a tail, which closes the stream"), (12, "piece: empty"),
    (14, "piece: starts after the counter wrapped"), (13, "piece: the counter wraps inside it"),
    (4, "width: 128 bits"), (4, "width: 32 bits, as GCM"), (15, "width: not whole bytes"),
    (8, "width: under 8 bits")]),
  ("scenario: RFC 6979 generator, madhouse", [
    (23, "a candidate drawn"), (16, "a candidate drawn after a rejection"),
    (25, "a candidate rejected"), (22, "a rejection with no candidate drawn before"),
    (18, "seeded again, over a state in use"),
    (11, "two candidates drawn with no rejection between"),
    (19, "two rejections or more since the seed")]),
  ("scenario: AEAD session, madhouse", [
    (17, "opened a packet"), (8, "opened a packet out of order"),
    (6, "opened a packet sealed under an earlier key"), (9, "refused a packet, changed: aad"),
    (8, "refused a packet, changed: key"), (9, "refused a packet, changed: nonce"),
    (10, "refused a packet, changed: tag"), (9, "refused a packet, changed: text"),
    (11, "sealed at a number whose bytes carry next"),
    (2, "sealed at the number 2^96, whose nonce is zeros again"), (25, "sealed under AES-GCM"),
    (27, "sealed under ChaCha20-Poly1305"), (23, "sealed with packets in flight")])
]

end HashesProperty

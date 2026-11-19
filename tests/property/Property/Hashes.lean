import Property.Hashes.Digest
import Property.Hashes.Cipher
import Property.Hashes.Misc
import Property.Hashes.Machines
import Property.Hashes.Extra

/-!
# Symmetric cryptography, on generated inputs

Hashes, checksums, key derivation, AES and its modes, ChaCha20-Poly1305, X25519, the nonces of
RFC 6979, ERC-2335 keystores, Ethash and the Merkle tree, each against a reference that EthLib
did not compute (`oracle/hashes.py`) or a model written from the source text.

    lake exe hashes-property            # 100 cases of each
    lake exe hashes-property 2000
    lake exe hashes-property 1000 slow  # Also the ERC-2335 vectors and the cache of epoch 0.
-/

open Hedgehog Support HashesProperty

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "hashes"
  let ok ← checkGroup "hashes" [
    ("Keccak-256", (keccak256 oracle).withTests cases),
    ("Keccak-512", (keccak512 oracle).withTests cases),
    ("the Keccak sponge at each rate of the family", (keccakRates oracle).withTests cases),
    ("SHA-256", (sha256 oracle).withTests cases),
    ("RIPEMD-160", (ripemd160 oracle).withTests cases),
    ("CRC-32 and CRC-32C", (crc oracle).withTests cases),
    ("BLAKE2b F", (blake2f oracle).withTests cases),
    ("HMAC-SHA-256", (hmac oracle).withTests cases),
    ("HKDF-Expand", (hkdfExpand oracle).withTests cases),
    ("HKDF", (hkdf oracle).withTests cases),
    ("TLS 1.3 HKDF-Expand-Label", (tls13 oracle).withTests cases),
    ("Concatenation KDF", (concatKdf oracle).withTests cases),
    ("PBKDF2", (pbkdf2 oracle).withTests cases),
    ("scrypt steps", (scryptSteps oracle).withTests cases),
    ("scrypt", (scrypt oracle).withTests cases),
    ("AES block", (aesBlock oracle).withTests cases),
    ("AES-CTR", (aesCtr oracle).withTests cases),
    ("AES-GCM encryption", (gcmEncrypt oracle).withTests cases),
    ("AES-GCM decryption", (gcmDecrypt oracle).withTests cases),
    ("ChaCha20 block", (chachaBlock oracle).withTests cases),
    ("ChaCha20 encryption", (chachaCrypt oracle).withTests cases),
    ("Poly1305", (poly1305 oracle).withTests cases),
    ("ChaCha20-Poly1305 encryption", (aeadEncrypt oracle).withTests cases),
    ("ChaCha20-Poly1305 decryption", (aeadDecrypt oracle).withTests cases),
    ("X25519", (x25519 oracle).withTests cases),
    ("RFC 6979 seed", (rfc6979Seed oracle).withTests cases),
    ("ERC-2335 keystore", (keystore oracle).withTests cases),
    ("Ethash sizes", (ethashSizes oracle).withTests cases),
    ("Ethash primality and size search", ethashPrimes.withTests cases),
    ("Ethash seed", (ethashSeed oracle).withTests (cases / 10)),
    ("Ethash cache, item and proof of work", (ethashPow oracle).withTests (cases / 4)),
    ("Merkle tree", merkleTree.withTests cases),
    ("Merkle multiproof", merkleMultiproof.withTests cases),
    ("paddings as arithmetic", paddings.withTests cases),
    ("padded messages", padded.withTests cases),
    ("scrypt cost bound", scryptCost.withTests cases),
    ("ChaCha20-Poly1305 length limits", aeadLimits.withTests cases),
    ("AES-192 by the general cipher", (aes192 oracle).withTests cases),
    ("key derivations past 255 and 65535 blocks", (longOutputs oracle).withTests (cases / 50)),
    ("machine: incremental Keccak-256",
      ((hasherMachine oracle).property (.linear 1 30)).withTests cases),
    ("machine: AES-CTR stream", ((streamMachine oracle).property (.linear 1 20)).withTests cases),
    ("scenario: RFC 6979 generator, in order", drbgScenario .deterministic oracle),
    ("scenario: RFC 6979 generator, madhouse", (drbgScenario .madhouse oracle).withTests cases),
    ("scenario: AEAD session, in order", sessionScenario .deterministic oracle),
    ("scenario: AEAD session, madhouse", (sessionScenario .madhouse oracle).withTests cases)]
  let pinned ← checkGroup "hashes: outside the documented preconditions" [
    ("a multiproof does not bind every value given", multiproofUnbound.withTests cases),
    ("a keystore number is read by its text", keystoreNumbers.withTests 1)]
  -- The slow properties run once each, and only when asked: `lake exe hashes-property slow`.
  let slow ← if args.contains "slow" then checkGroup "hashes: slow" [
    ("ERC-2335 test vectors", keystoreVectors.withTests 1),
    ("Ethash epoch 0", (ethashEpoch oracle).withTests 1)] else pure true
  pure (if ok && pinned && slow then 0 else 1)

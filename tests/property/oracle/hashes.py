"""References for symmetric cryptography: one command per line, one answer per line."""

# Words are separated by tabs, bytes are in hexadecimal, `-` is the empty string.
# An answer that starts with `error` says the reference refused the input.
# Each reference is a library (hashlib, cryptography, pycryptodome, crc32c) or a transcription.
# The transcriptions are of RFC 7693, 7748, 7914 and 6979, SP 800-38A, Ethash and ERC-2335.
# Each transcription is checked against a library at start.
# `hashes_aes.py` holds Rijndael and GCM from their texts, and `hashes_cost.py` counted work.

import hashlib
import hmac
import json
import os
import struct
import sys
import unicodedata
import zlib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import hashes_aes
import hashes_cost
from Crypto.Cipher import AES
from Crypto.Hash import RIPEMD160, keccak
from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives import hashes, poly1305
from cryptography.hazmat.primitives.asymmetric import x25519 as cx25519
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
from cryptography.hazmat.primitives.kdf.concatkdf import ConcatKDFHash
from cryptography.hazmat.primitives.kdf.hkdf import HKDFExpand

import crc32c

M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return data.hex() if data else "-"


def sha256(data):
    return hashlib.sha256(data).digest()


def keccak256(data):
    return keccak.new(digest_bits=256, data=data).digest()


def keccak512(data):
    return keccak.new(digest_bits=512, data=data).digest()


def ripemd160(data):
    # Two libraries, since OpenSSL may lack the legacy provider.
    digest = RIPEMD160.new(data).digest()
    try:
        assert hashlib.new("ripemd160", data).digest() == digest
    except ValueError:
        pass
    return digest


# BLAKE2b F, RFC 7693 section 3.2, with the round count as an argument.

BLAKE_IV = [
    0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
    0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179,
]  # fmt: skip
BLAKE_SIGMA = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
]


def rotr64(x, n):
    return ((x >> n) | (x << (64 - n))) & M64


def blake_g(v, a, b, c, d, x, y):
    v[a] = (v[a] + v[b] + x) & M64
    v[d] = rotr64(v[d] ^ v[a], 32)
    v[c] = (v[c] + v[d]) & M64
    v[b] = rotr64(v[b] ^ v[c], 24)
    v[a] = (v[a] + v[b] + y) & M64
    v[d] = rotr64(v[d] ^ v[a], 16)
    v[c] = (v[c] + v[d]) & M64
    v[b] = rotr64(v[b] ^ v[c], 63)


def blake2f(rounds, h, m, t0, t1, final):
    v = h + BLAKE_IV
    v[12] ^= t0
    v[13] ^= t1
    if final:
        v[14] ^= M64
    for i in range(rounds):
        s = BLAKE_SIGMA[i % 10]
        blake_g(v, 0, 4, 8, 12, m[s[0]], m[s[1]])
        blake_g(v, 1, 5, 9, 13, m[s[2]], m[s[3]])
        blake_g(v, 2, 6, 10, 14, m[s[4]], m[s[5]])
        blake_g(v, 3, 7, 11, 15, m[s[6]], m[s[7]])
        blake_g(v, 0, 5, 10, 15, m[s[8]], m[s[9]])
        blake_g(v, 1, 6, 11, 12, m[s[10]], m[s[11]])
        blake_g(v, 2, 7, 8, 13, m[s[12]], m[s[13]])
        blake_g(v, 3, 4, 9, 14, m[s[14]], m[s[15]])
    return [h[i] ^ v[i] ^ v[i + 8] for i in range(8)]


def blake2b(data):
    """BLAKE2b-512 by RFC 7693 section 3.3, to check F against hashlib."""
    h = list(BLAKE_IV)
    h[0] ^= 0x01010040
    blocks = [data[i : i + 128] for i in range(0, len(data), 128)] or [b""]
    done = 0
    for index, block in enumerate(blocks):
        done += len(block)
        m = list(struct.unpack("<16Q", block.ljust(128, b"\0")))
        last = index == len(blocks) - 1
        h = blake2f(12, h, m, done & M64, done >> 64, last)
    return struct.pack("<8Q", *h)


# Scrypt's steps, RFC 7914 sections 3 to 5.


def rotl32(x, n):
    return ((x << n) | (x >> (32 - n))) & M32


def salsa208(block):
    x = list(struct.unpack("<16I", block))
    start = list(x)

    def quarter(a, b, c, d):
        x[b] ^= rotl32((x[a] + x[d]) & M32, 7)
        x[c] ^= rotl32((x[b] + x[a]) & M32, 9)
        x[d] ^= rotl32((x[c] + x[b]) & M32, 13)
        x[a] ^= rotl32((x[d] + x[c]) & M32, 18)

    for _ in range(4):
        quarter(0, 4, 8, 12)
        quarter(5, 9, 13, 1)
        quarter(10, 14, 2, 6)
        quarter(15, 3, 7, 11)
        quarter(0, 1, 2, 3)
        quarter(5, 6, 7, 4)
        quarter(10, 11, 8, 9)
        quarter(15, 12, 13, 14)
    return struct.pack("<16I", *[(a + b) & M32 for a, b in zip(x, start, strict=True)])


def xor(a, b):
    return bytes(p ^ q for p, q in zip(a, b, strict=False))


def blockmix(data, r):
    x = data[-64:]
    y = []
    for i in range(2 * r):
        x = salsa208(xor(x, data[64 * i : 64 * i + 64]))
        y.append(x)
    return b"".join(y[0::2] + y[1::2])


def romix(data, n, r):
    x = data
    table = []
    for _ in range(n):
        table.append(x)
        x = blockmix(x, r)
    for _ in range(n):
        j = int.from_bytes(x[-64:], "little") % n
        x = blockmix(xor(x, table[j]), r)
    return x


def scrypt_steps(password, salt, n, r, p, length):
    b = hashlib.pbkdf2_hmac("sha256", password, salt, 1, p * 128 * r)
    mixed = b"".join(romix(b[128 * r * i : 128 * r * (i + 1)], n, r) for i in range(p))
    return hashlib.pbkdf2_hmac("sha256", password, mixed, 1, length)


def scrypt(password, salt, n, r, p, length):
    """RFC 7914 section 2 and 6: the parameter rules, then the library."""
    if r < 1 or n < 2 or n & (n - 1) or n >= 2 ** (128 * r // 8):
        return None
    if p < 1 or p > ((2**32 - 1) * 32) // (128 * r):
        return None
    if length < 1 or length > (2**32 - 1) * 32:
        return None
    return hashlib.scrypt(password, salt=salt, n=n, r=r, p=p, dklen=length, maxmem=2**30)


# HKDF and its TLS 1.3 labels, RFC 5869 and RFC 8446 section 7.1.


def hmac256(key, message):
    return hmac.new(key, message, hashlib.sha256).digest()


def hkdf_expand(prk, info, length):
    """RFC 5869 section 2.3, from the text; the library agrees where it runs."""
    if len(prk) < 32 or length > 255 * 32:
        return None
    okm, t = b"", b""
    for i in range(1, -(-length // 32) + 1):
        t = hmac256(prk, t + info + bytes([i]))
        okm += t
    okm = okm[:length]
    if length > 0:
        assert HKDFExpand(hashes.SHA256(), length, info).derive(prk) == okm
    return okm


def tls13_label(secret, label, context, length):
    full = b"tls13 " + label
    if not 7 <= len(full) <= 255 or len(context) > 255 or length > 65535:
        return None
    info = struct.pack(">H", length) + bytes([len(full)]) + full
    info += bytes([len(context)]) + context
    return hkdf_expand(secret, info, length)


# AES modes.


def aes_ecb(key, block, decrypt=False):
    cipher = Cipher(algorithms.AES(key), modes.ECB())
    op = cipher.decryptor() if decrypt else cipher.encryptor()
    return op.update(block) + op.finalize()


def aes_ctr(key, m, counter, data):
    """SP 800-38A section 6.5, with the incrementing function of Appendix B.1."""
    m = min(m, 128)
    t = int.from_bytes(counter, "big")
    out = b""
    for i in range(0, len(data), 16):
        out += xor(data[i : i + 16], aes_ecb(key, t.to_bytes(16, "big")))
        t = (t >> m << m) | ((t + 1) & ((1 << m) - 1))
    if m == 128:
        op = Cipher(algorithms.AES(key), modes.CTR(counter)).encryptor()
        assert op.update(data) + op.finalize() == out
    return out


def gcm_cross(key, t, iv, p, aad, c, tag):
    """The second library, where it takes the IV: 8 to 128 bytes."""
    if 8 <= len(iv) <= 128:
        op = Cipher(algorithms.AES(key), modes.GCM(iv)).encryptor()
        op.authenticate_additional_data(aad)
        assert op.update(p) + op.finalize() == c
        assert op.tag[:t] == tag


def gcm_encrypt(key, t, iv, p, aad):
    # SP 800-38D section 5.2.1.2 and Appendix C: 12 to 16 bytes of tag.
    if t not in (12, 13, 14, 15, 16) or len(iv) == 0:
        return None
    cipher = AES.new(key, AES.MODE_GCM, nonce=iv, mac_len=t)
    cipher.update(aad)
    c, tag = cipher.encrypt_and_digest(p)
    gcm_cross(key, t, iv, p, aad, c, tag)
    return c, tag


def gcm_decrypt(key, t, iv, c, aad, tag):
    if t not in (12, 13, 14, 15, 16) or len(iv) == 0 or len(tag) != t:
        return None
    cipher = AES.new(key, AES.MODE_GCM, nonce=iv, mac_len=t)
    cipher.update(aad)
    try:
        return cipher.decrypt_and_verify(c, tag)
    except ValueError:
        return None


# ChaCha20 and Poly1305, RFC 8439.


def chacha_stream(key, counter, nonce, data):
    full = struct.pack("<I", counter) + nonce
    op = Cipher(algorithms.ChaCha20(key, full), None).encryptor()
    return op.update(data) + op.finalize()


def aead_decrypt(key, nonce, aad, c, tag):
    try:
        return ChaCha20Poly1305(key).decrypt(nonce, c + tag, aad)
    except InvalidTag:
        return None


# X25519, RFC 7748 section 5, from the text.

P25519 = 2**255 - 19


def x25519(k, u):
    scalar = int.from_bytes(k, "little")
    scalar &= ~7 & ((1 << 255) - 1)
    scalar |= 1 << 254
    x1 = (int.from_bytes(u, "little") & ((1 << 255) - 1)) % P25519
    x2, z2, x3, z3, swap = 1, 0, x1, 1, 0
    for t in reversed(range(255)):
        bit = (scalar >> t) & 1
        swap ^= bit
        if swap:
            x2, x3, z2, z3 = x3, x2, z3, z2
        swap = bit
        a = (x2 + z2) % P25519
        aa = a * a % P25519
        b = (x2 - z2) % P25519
        bb = b * b % P25519
        e = (aa - bb) % P25519
        c = (x3 + z3) % P25519
        d = (x3 - z3) % P25519
        da = d * a % P25519
        cb = c * b % P25519
        x3 = (da + cb) ** 2 % P25519
        z3 = x1 * (da - cb) ** 2 % P25519
        x2 = aa * bb % P25519
        z2 = e * (aa + 121665 * e) % P25519
    if swap:
        x2, x3, z2, z3 = x3, x2, z3, z2
    out = (x2 * pow(z2, P25519 - 2, P25519) % P25519).to_bytes(32, "little")
    # The library refuses the all-zero output; elsewhere it must agree.
    try:
        private = cx25519.X25519PrivateKey.from_private_bytes(k)
        public = cx25519.X25519PublicKey.from_public_bytes(u)
        assert private.exchange(public) == out
    except ValueError:
        assert out == bytes(32)
    return out


# The nonce generator of RFC 6979 section 3.2, for HMAC-SHA-256 and a 256-bit order.


def rfc6979_seed(q, x, h1):
    material = x.to_bytes(32, "big")
    material += (int.from_bytes(h1, "big") % q).to_bytes(32, "big")
    v, k = b"\x01" * 32, b"\x00" * 32
    k = hmac256(k, v + b"\x00" + material)
    v = hmac256(k, v)
    k = hmac256(k, v + b"\x01" + material)
    v = hmac256(k, v)
    return k, v


# Ethash, from the specification of the Ethereum Foundation.

FNV_PRIME = 0x01000193
CACHES = {}


def fnv(a, b):
    return (a * FNV_PRIME ^ b) & M32


def words(data):
    return list(struct.unpack(f"<{len(data) // 4}I", data))


def unwords(items):
    return struct.pack(f"<{len(items)}I", *items)


def isprime(x):
    return x >= 2 and all(x % i for i in range(2, int(x**0.5) + 1))


def ethash_size(block, init, growth, unit):
    size = init + growth * (block // 30000) - unit
    while not isprime(size // unit):
        size -= 2 * unit
    return size


def ethash_seed(block):
    s = bytes(32)
    for _ in range(block // 30000):
        s = keccak256(s)
    return s


def mkcache(n, seed):
    if (n, seed) in CACHES:
        return CACHES[(n, seed)]
    o = [words(keccak512(seed))]
    for _ in range(1, n):
        o.append(words(keccak512(unwords(o[-1]))))
    for _ in range(3):
        for i in range(n):
            v = o[i][0] % n
            mixed = [a ^ b for a, b in zip(o[(i - 1 + n) % n], o[v], strict=True)]
            o[i] = words(keccak512(unwords(mixed)))
    CACHES.clear()
    CACHES[(n, seed)] = o
    return o


def dataset_item(cache, i):
    n = len(cache)
    mix = list(cache[i % n])
    mix[0] ^= i
    mix = words(keccak512(unwords(mix)))
    for j in range(256):
        index = fnv(i ^ j, mix[j % 16])
        mix = [fnv(a, b) for a, b in zip(mix, cache[index % n], strict=True)]
    return words(keccak512(unwords(mix)))


def hashimoto(cache, full_size, header, nonce):
    n = full_size // 64
    s = words(keccak512(header + nonce[::-1]))
    mix = s + s
    for i in range(64):
        p = fnv(i ^ s[0], mix[i % 32]) % (n // 2) * 2
        data = dataset_item(cache, p) + dataset_item(cache, p + 1)
        mix = [fnv(a, b) for a, b in zip(mix, data, strict=True)]
    cmix = [fnv(fnv(fnv(mix[i], mix[i + 1]), mix[i + 2]), mix[i + 3]) for i in range(0, 32, 4)]
    digest = unwords(cmix)
    return digest, keccak256(unwords(s) + digest)


# ERC-2335 keystores.


def ks_password(text):
    out = unicodedata.normalize("NFKD", text)
    out = "".join(c for c in out if not (ord(c) <= 0x1F or 0x7F <= ord(c) <= 0x9F))
    return out.encode()


def ks_key(kdf, password):
    params = kdf["params"]
    salt = bytes.fromhex(params["salt"])
    if kdf["function"] == "scrypt":
        return hashlib.scrypt(
            password, salt=salt, n=params["n"], r=params["r"], p=params["p"],
            dklen=params["dklen"], maxmem=2**30,
        )  # fmt: skip
    if kdf["function"] == "pbkdf2" and params["prf"] == "hmac-sha256":
        return hashlib.pbkdf2_hmac("sha256", password, salt, params["c"], params["dklen"])
    raise ValueError("kdf")


def ks_decrypt(store, password):
    """Decryption by ERC-2335: the required fields, the three steps."""
    try:
        if store["version"] != 4:
            return None
        if not isinstance(store["path"], str) or not isinstance(store["uuid"], str):
            return None
        # The schema of the ERC gives both optional fields the type string.
        for name in ("description", "pubkey"):
            if name in store and not isinstance(store[name], str):
                return None
        crypto = store["crypto"]
        for name in ("kdf", "checksum", "cipher"):
            module = crypto[name]
            if not isinstance(module["function"], str):
                return None
            if not isinstance(module["params"], dict):
                return None
            if not isinstance(module["message"], str):
                return None
        # Password verification reads bytes 16 to 32 of the key, so a shorter key is refused.
        if crypto["kdf"]["params"]["dklen"] < 32:
            return None
        key = ks_key(crypto["kdf"], ks_password(password))
        if crypto["checksum"]["function"] != "sha256":
            return None
        if crypto["cipher"]["function"] != "aes-128-ctr":
            return None
        message = bytes.fromhex(crypto["cipher"]["message"])
        checksum = bytes.fromhex(crypto["checksum"]["message"])
        iv = bytes.fromhex(crypto["cipher"]["params"]["iv"])
        if len(iv) != 16 or sha256(key[16:32] + message) != checksum:
            return None
        op = Cipher(algorithms.AES(key[:16]), modes.CTR(iv)).decryptor()
        return op.update(message) + op.finalize()
    except (KeyError, ValueError, TypeError):
        return None


def ks_make(mutation, kdf, cost, r, p, dklen, salt, iv, password, tried, secret):
    """A keystore of the secret, mutated, and what decryption must give."""
    params = {"dklen": dklen, "salt": salt.hex()}
    if kdf == "scrypt":
        params |= {"n": cost, "r": r, "p": p}
    else:
        params |= {"c": cost, "prf": "hmac-sha256"}
    module = {"function": kdf, "params": params, "message": ""}
    # A key of 16 to 31 bytes seals as the slices of the ERC read it, `key[16:32]` cut short.
    # A shorter one is no AES key: the store is then sealed with 32 bytes, and says less.
    sealing = {"function": kdf, "params": params | {"dklen": dklen if dklen >= 16 else 32}}
    key = ks_key(sealing, ks_password(password))
    op = Cipher(algorithms.AES(key[:16]), modes.CTR(iv)).encryptor()
    message = op.update(secret) + op.finalize()
    crypto = {
        "kdf": module,
        "checksum": {
            "function": "sha256",
            "params": {},
            "message": sha256(key[16:32] + message).hex(),
        },
        "cipher": {
            "function": "aes-128-ctr",
            "params": {"iv": iv.hex()},
            "message": message.hex(),
        },
    }
    store = {
        "crypto": crypto,
        "description": "A keystore.",
        "pubkey": "00" * 48,
        "path": "m/12381/60/0/0",
        "uuid": "1d85ae20-35c5-4611-98e8-aa14a633906f",
        "version": 4,
    }
    match mutation:
        case "checksum":
            byte = int(crypto["checksum"]["message"][:2], 16) ^ 1
            crypto["checksum"]["message"] = f"{byte:02x}" + crypto["checksum"]["message"][2:]
        case "cipher":
            # One bit of the ciphertext, or one byte more where there is none.
            changed = bytes([message[0] ^ 0x80]) + message[1:] if message else b"\x00"
            crypto["cipher"]["message"] = changed.hex()
        case "version":
            store["version"] = 3
        case "version5":
            store["version"] = 5
        case "versiontext":
            store["version"] = "4"
        case "nocrypto":
            del store["crypto"]
        case "nokdf" | "nochecksum" | "nocipher":
            del crypto[mutation[2:]]
        case "nosalt" | "nodklen":
            del params[mutation[2:]]
        case "noiv":
            del crypto["cipher"]["params"]["iv"]
        case "nocost":
            del params["n" if kdf == "scrypt" else "c"]
        case "dklentext":
            params["dklen"] = str(dklen)
        case "checksum31":
            crypto["checksum"]["message"] = crypto["checksum"]["message"][2:]
        case "checksum33":
            crypto["checksum"]["message"] += "00"
        case "iv17":
            crypto["cipher"]["params"]["iv"] = iv.hex() + "00"
        case "nothex":
            params["salt"] = "zz" + params["salt"]
        case "numdescription":
            store["description"] = 5
        case "numpubkey":
            store["pubkey"] = 5
        case "numpath":
            store["path"] = 5
        case "extra":
            store["name"] = "an unknown field"
            crypto["cipher"]["params"]["mode"] = "ctr"
        case "cost0" if kdf == "pbkdf2":
            params["c"] = 0
        case "cost0":
            params["n"] = 0
        case "cost1" if kdf == "scrypt":
            params["n"] = 1
        case "cost3" if kdf == "scrypt":
            params["n"] = 3 * cost
        case "r0" if kdf == "scrypt":
            params["r"] = 0
        case "p0" if kdf == "scrypt":
            params["p"] = 0
        case "upper":
            for name in ("checksum", "cipher"):
                crypto[name]["message"] = crypto[name]["message"].upper()
            params["salt"] = params["salt"].upper()
            crypto["cipher"]["params"]["iv"] = iv.hex().upper()
        case "nopath" | "nouuid" | "nopubkey" | "nodescription":
            del store[mutation[2:]]
        case "prf" if kdf == "pbkdf2":
            params["prf"] = "hmac-sha512"
        case "cipherfn":
            crypto["cipher"]["function"] = "aes-256-ctr"
        case "checksumfn":
            crypto["checksum"]["function"] = "keccak256"
        case "kdffn":
            module["function"] = "argon2"
        case "iv15":
            crypto["cipher"]["params"]["iv"] = iv.hex()[2:]
        case "oddhex":
            crypto["checksum"]["message"] = crypto["checksum"]["message"][1:]
        case "prefix":
            crypto["cipher"]["message"] = "0x" + crypto["cipher"]["message"]
        case "nomessage":
            del module["message"]
        case "noparams":
            del crypto["checksum"]["params"]
        case "listparams":
            crypto["checksum"]["params"] = []
    expected = ks_decrypt(store, tried)
    price = hashes_cost.cost(module, ks_password(tried)) if "crypto" in store else None
    return json.dumps(store).encode(), expected, price or (0, 0)


def opt(data):
    return "error" if data is None else tohex(data)


def answer(w):
    match w:
        case ["keccak256", data]:
            return tohex(keccak256(unhex(data)))
        case ["keccak512", data]:
            return tohex(keccak512(unhex(data)))
        case ["keccak", bits, data]:
            # Keccak of a digest of 224, 256, 384 or 512 bits: the rate is 200 - bits / 4 bytes.
            return tohex(keccak.new(digest_bits=int(bits), data=unhex(data)).digest())
        case ["sha256", data]:
            return tohex(sha256(unhex(data)))
        case ["ripemd160", data]:
            return tohex(ripemd160(unhex(data)))
        case ["filled", byte, count]:
            # Both digests of one byte repeated, for a message too long to send.
            data = bytes([int(byte)]) * int(count)
            return f"{sha256(data).hex()} {ripemd160(data).hex()}"
        case ["crc32", data]:
            return str(zlib.crc32(unhex(data)))
        case ["crc32c", data]:
            return str(crc32c.crc32c(unhex(data)))
        case ["blake2f", rounds, h, m, t0, t1, final]:
            out = blake2f(
                int(rounds),
                list(struct.unpack("<8Q", unhex(h))),
                list(struct.unpack("<16Q", unhex(m))),
                int(t0), int(t1), final == "1",
            )  # fmt: skip
            return struct.pack("<8Q", *out).hex()
        case ["hmac", key, message]:
            return tohex(hmac256(unhex(key), unhex(message)))
        case ["hkdf_expand", prk, info, length]:
            return opt(hkdf_expand(unhex(prk), unhex(info), int(length)))
        case ["hkdf", salt, ikm, info, length]:
            prk = hmac256(unhex(salt) or bytes(32), unhex(ikm))
            return opt(hkdf_expand(prk, unhex(info), int(length)))
        case ["tls13", secret, label, context, length]:
            return opt(tls13_label(unhex(secret), unhex(label), unhex(context), int(length)))
        case ["concatkdf", z, info, length]:
            if int(length) == 0:
                return "error"
            kdf = ConcatKDFHash(hashes.SHA256(), int(length), unhex(info))
            return tohex(kdf.derive(unhex(z)))
        case ["pbkdf2", password, salt, count, length]:
            if int(count) < 1 or int(length) < 1:
                return "error"
            return tohex(
                hashlib.pbkdf2_hmac("sha256", unhex(password), unhex(salt), int(count), int(length))
            )
        case ["pbkdf2_tail", password, salt, length]:
            out = hashlib.pbkdf2_hmac("sha256", unhex(password), unhex(salt), 1, int(length))
            return out[-64:].hex()
        case ["concatkdf_tail", z, info, length]:
            kdf = ConcatKDFHash(hashes.SHA256(), int(length), unhex(info))
            return kdf.derive(unhex(z))[-64:].hex()
        case ["scrypt", password, salt, n, r, p, length]:
            return opt(scrypt(unhex(password), unhex(salt), int(n), int(r), int(p), int(length)))
        case ["salsa208", block]:
            # RFC 7914 section 3 defines the core on 64 bytes.
            return salsa208(unhex(block)).hex() if len(unhex(block)) == 64 else "error"
        case ["blockmix", data, r]:
            # Section 4: `2 r` blocks of 64 bytes.
            if int(r) < 1 or len(unhex(data)) != 128 * int(r):
                return "error"
            return blockmix(unhex(data), int(r)).hex()
        case ["romix", data, n, r]:
            # Sections 2 and 5: `N` is a power of two above 1 and below `2^(128 r / 8)`.
            n, r = int(n), int(r)
            if r < 1 or len(unhex(data)) != 128 * r or n < 2 or n & (n - 1) or n >= 2 ** (16 * r):
                return "error"
            return romix(unhex(data), n, r).hex()
        case ["aes", key, block]:
            return aes_ecb(unhex(key), unhex(block)).hex()
        case ["aesinv", key, block]:
            return aes_ecb(unhex(key), unhex(block), decrypt=True).hex()
        case ["ctr", key, m, counter, data]:
            return tohex(aes_ctr(unhex(key), int(m), unhex(counter), unhex(data)))
        case ["gcm_enc", key, t, iv, p, aad]:
            out = gcm_encrypt(unhex(key), int(t), unhex(iv), unhex(p), unhex(aad))
            return "error" if out is None else tohex(out[0]) + " " + tohex(out[1])
        case ["gcm_dec", key, t, iv, c, aad, tag]:
            return opt(gcm_decrypt(unhex(key), int(t), unhex(iv), unhex(c), unhex(aad), unhex(tag)))
        case ["chacha", key, counter, nonce, data]:
            return tohex(chacha_stream(unhex(key), int(counter), unhex(nonce), unhex(data)))
        case ["poly1305", key, message]:
            return poly1305.Poly1305.generate_tag(unhex(key), unhex(message)).hex()
        case ["aead_enc", key, nonce, aad, p]:
            out = ChaCha20Poly1305(unhex(key)).encrypt(unhex(nonce), unhex(p), unhex(aad))
            return tohex(out[:-16]) + " " + out[-16:].hex()
        case ["aead_dec", key, nonce, aad, c, tag]:
            return opt(aead_decrypt(unhex(key), unhex(nonce), unhex(aad), unhex(c), unhex(tag)))
        case ["x25519", k, u]:
            return x25519(unhex(k), unhex(u)).hex()
        case ["rfc_seed", q, x, h1]:
            k, v = rfc6979_seed(int(q), int(x), unhex(h1))
            return k.hex() + " " + v.hex()
        case ["rfc_next", k, v]:
            return hmac256(unhex(k), unhex(v)).hex()
        case ["rfc_reject", k, v]:
            k = hmac256(unhex(k), unhex(v) + b"\x00")
            return k.hex() + " " + hmac256(k, unhex(v)).hex()
        case ["ethash_sizes", block]:
            cache = ethash_size(int(block), 2**24, 2**17, 64)
            return f"{cache} {ethash_size(int(block), 2**30, 2**23, 128)}"
        case ["ethash_epochs", first, count]:
            # The sizes of consecutive epochs, as `cache:dataset` separated by spaces.
            epochs = range(int(first), int(first) + int(count))
            return " ".join(
                f"{ethash_size(30000 * e, 2**24, 2**17, 64)}:"
                f"{ethash_size(30000 * e, 2**30, 2**23, 128)}"
                for e in epochs
            )
        case ["ethash_seed", block]:
            return ethash_seed(int(block)).hex()
        case ["ethash_cache", n, seed]:
            return tohex(b"".join(unwords(i) for i in mkcache(int(n), unhex(seed))))
        case ["ethash_cache_hash", n, seed]:
            cache = mkcache(int(n), unhex(seed))
            return keccak256(b"".join(unwords(i) for i in cache)).hex()
        case ["ethash_item", n, seed, i]:
            return unwords(dataset_item(mkcache(int(n), unhex(seed)), int(i))).hex()
        case ["ethash_pow", n, seed, size, header, nonce]:
            cache = mkcache(int(n), unhex(seed))
            digest, result = hashimoto(cache, int(size), unhex(header), unhex(nonce))
            return digest.hex() + " " + result.hex()
        case ["ks", mutation, kdf, cost, r, p, dklen, salt, iv, password, tried, secret]:
            store, expected, (memory, work) = ks_make(
                mutation, kdf, int(cost), int(r), int(p), int(dklen), unhex(salt),
                unhex(iv), unhex(password).decode(), unhex(tried).decode(),
                unhex(secret),
            )  # fmt: skip
            return f"{store.hex()} {opt(expected)} {memory} {work}"
    return hashes_aes.answer(w) or "error unknown command"


def selftest():
    """The transcriptions agree with a library before they judge EthLib."""
    for size in (0, 1, 127, 128, 129, 300):
        data = bytes(range(256)) * 2
        assert blake2b(data[:size]) == hashlib.blake2b(data[:size]).digest()
    assert scrypt_steps(b"pw", b"salt", 16, 2, 2, 40) == hashlib.scrypt(
        b"pw", salt=b"salt", n=16, r=2, p=2, dklen=40
    )
    # RFC 7748 section 5.2, the first vector.
    assert x25519(
        bytes.fromhex("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"),
        bytes.fromhex("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"),
    ) == bytes.fromhex("c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")
    # The Ethash specification's sizes of epoch 0.
    assert ethash_size(0, 2**24, 2**17, 64) == 16776896
    assert ethash_size(0, 2**30, 2**23, 128) == 1073739904


selftest()
for line in sys.stdin:
    try:
        print(answer(line.rstrip("\n").split("\t")) or "-", flush=True)
    except Exception as error:  # A reference that crashes must not hang the driver.
        print(f"error crash {type(error).__name__} {error}", flush=True)

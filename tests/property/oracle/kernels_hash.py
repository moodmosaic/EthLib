"""Hash internals written from the standards: one step, any state, any parameter."""

# sha_compress <8 words> <block>         One block of FIPS 180-4, section 6.2.2, on any state.
# sha_schedule <block>                   The 64 words of the message schedule.
# sha_hash <data>                        SHA-256, by hashlib.
# rmd_compress <5 words> <block>         One block of RIPEMD-160 on any chaining value.
# keccak_f <25 lanes>                    Keccak-f[1600] on any state.
# keccak_round <ir> <25 lanes>           One round.
# keccak_step <name> <25 lanes>          theta, rho, pi or chi.
# keccak_absorb <rate> <data>            The state after the sponge absorbs at any rate.
# keccak_pad <rate> <len>                pad10*1 for a message of whole bytes.
# crc <generator> <data>                 A reflected 32-bit CRC with any generator.
# hmac, hkdf_expand, hkdf, pbkdf2, concat, scrypt: the key derivations, see `answer`.

import hashlib
import hmac as hmac_module
import struct

import kernels_tables as tables

MASK32 = 0xFFFFFFFF
MASK64 = (1 << 64) - 1


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return data.hex() if data else "-"


def rotr32(x, n):
    return ((x >> n) | (x << (32 - n))) & MASK32


def rotl32(x, n):
    return ((x << n) | (x >> (32 - n))) & MASK32


def sha_schedule(block):
    # FIPS 180-4, section 6.2.2, step 1.
    w = list(struct.unpack(">16I", block))
    for t in range(16, 64):
        s0 = rotr32(w[t - 15], 7) ^ rotr32(w[t - 15], 18) ^ (w[t - 15] >> 3)
        s1 = rotr32(w[t - 2], 17) ^ rotr32(w[t - 2], 19) ^ (w[t - 2] >> 10)
        w.append((s1 + w[t - 7] + s0 + w[t - 16]) & MASK32)
    return w


SHA_K = tables.sha256_k()


def sha_compress(state, block):
    # FIPS 180-4, section 6.2.2, steps 2 to 4.
    w = sha_schedule(block)
    a, b, c, d, e, f, g, h = state
    for t in range(64):
        t1 = h + (rotr32(e, 6) ^ rotr32(e, 11) ^ rotr32(e, 25)) + ((e & f) ^ (~e & g))
        t1 = (t1 + SHA_K[t] + w[t]) & MASK32
        t2 = (rotr32(a, 2) ^ rotr32(a, 13) ^ rotr32(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))
        h, g, f, e, d, c, b, a = g, f, e, (d + t1) & MASK32, c, b, a, (t1 + t2) & MASK32
    return [(x + y) & MASK32 for x, y in zip(state, [a, b, c, d, e, f, g, h], strict=True)]


def sha256(data):
    # The whole hash by the steps above, to check them against hashlib.
    padded = data + b"\x80" + bytes((55 - len(data)) % 64) + struct.pack(">Q", 8 * len(data))
    state = tables.sha256_iv()
    for i in range(0, len(padded), 64):
        state = sha_compress(state, padded[i : i + 64])
    return struct.pack(">8I", *state)


RMD_R, RMD_RP = tables.ripemd_orders()
RMD_S, RMD_SP = tables.ripemd_shifts(RMD_R), tables.ripemd_shifts(RMD_RP)
RMD_K, RMD_KP = tables.TABLES["ripemd_k"](), tables.TABLES["ripemd_kp"]()


def rmd_f(j, x, y, z):
    if j < 16:
        return x ^ y ^ z
    if j < 32:
        return (x & y) | (~x & z)
    if j < 48:
        return (x | ~y) ^ z
    if j < 64:
        return (x & z) | (y & ~z)
    return x ^ (y | ~z)


def rmd_compress(h, block):
    # The pseudo-code of the authors: two lines of eighty steps, then the mix.
    x = struct.unpack("<16I", block)
    a, b, c, d, e = h
    ap, bp, cp, dp, ep = h
    for j in range(80):
        t = rotl32((a + rmd_f(j, b, c, d) + x[RMD_R[j]] + RMD_K[j // 16]) & MASK32, RMD_S[j]) + e
        a, e, d, c, b = e, d, rotl32(c, 10), b, t & MASK32
        t = rotl32(
            (ap + rmd_f(79 - j, bp, cp, dp) + x[RMD_RP[j]] + RMD_KP[j // 16]) & MASK32, RMD_SP[j]
        )
        ap, ep, dp, cp, bp = ep, dp, rotl32(cp, 10), bp, (t + ep) & MASK32
    t = (h[1] + c + dp) & MASK32
    return [
        t,
        (h[2] + d + ep) & MASK32,
        (h[3] + e + ap) & MASK32,
        (h[4] + a + bp) & MASK32,
        (h[0] + b + cp) & MASK32,
    ]


def ripemd160(data):
    padded = data + b"\x80" + bytes((55 - len(data)) % 64) + struct.pack("<Q", 8 * len(data))
    state = tables.TABLES["ripemd_iv"]()
    for i in range(0, len(padded), 64):
        state = rmd_compress(state, padded[i : i + 64])
    return struct.pack("<5I", *state)


def rotl64(x, n):
    return ((x << n) | (x >> (64 - n))) & MASK64 if n else x


KECCAK_RC = tables.keccak_rc()
KECCAK_RHO = tables.keccak_rho()


def theta(a):
    c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
    d = [c[(x - 1) % 5] ^ rotl64(c[(x + 1) % 5], 1) for x in range(5)]
    return [a[i] ^ d[i % 5] for i in range(25)]


def rho(a):
    return [rotl64(a[i], KECCAK_RHO[i]) for i in range(25)]


def pi(a):
    # A'[x, y] = A[(x + 3 y) mod 5, x].
    return [a[(x + 3 * y) % 5 + 5 * x] for y in range(5) for x in range(5)]


def chi(a):
    return [
        a[x + 5 * y] ^ (~a[(x + 1) % 5 + 5 * y] & a[(x + 2) % 5 + 5 * y] & MASK64)
        for y in range(5)
        for x in range(5)
    ]


STEPS = {"theta": theta, "rho": rho, "pi": pi, "chi": chi}


def keccak_round(ir, a):
    a = chi(pi(rho(theta(a))))
    a[0] ^= KECCAK_RC[ir]
    return a


def keccak_f(a):
    for ir in range(24):
        a = keccak_round(ir, a)
    return a


def keccak_pad(rate, length):
    # FIPS 202, Algorithm 9, on whole bytes: the first bit, zeros, the last bit.
    k = rate - length % rate
    pad = bytearray(k)
    pad[0] |= 0x01
    pad[k - 1] |= 0x80
    return bytes(pad)


def xor_block(state, block):
    # S ^ (P_i || 0^c): all 25 lanes, the block padded with zeros to 200 bytes.
    return [s ^ lane for s, lane in zip(state, struct.unpack("<25Q", block), strict=True)]


def keccak_absorb(rate, data):
    # FIPS 202, Algorithm 8, steps 1 to 6, for a rate of whole lanes.
    padded = data + keccak_pad(rate, len(data))
    state = [0] * 25
    for start in range(0, len(padded), rate):
        block = padded[start : start + rate].ljust(200, b"\0")
        state = keccak_f(xor_block(state, block))
    return state


def keccak(rate, data, size):
    # The sponge with one squeeze, to check the steps above against hashlib.
    return struct.pack("<25Q", *keccak_absorb(rate, data))[:size]


def sha3_256(data):
    # SHA3-256 appends the bits 01 before the padding: the byte 0x06, then the final bit.
    rate = 136
    padded = bytearray(data + b"\x06" + bytes(rate - 1 - len(data) % rate))
    padded[-1] |= 0x80
    state = [0] * 25
    for start in range(0, len(padded), rate):
        block = bytes(padded[start : start + rate]).ljust(200, b"\0")
        state = keccak_f(xor_block(state, block))
    return struct.pack("<25Q", *state)[:32]


def crc(generator, data):
    # A 32-bit CRC: bytes enter least significant bit first, from all ones, complemented.
    # The generator is held without its x^32 term, the coefficient of x^31 in bit 31.
    r = MASK32
    for byte in data:
        for i in range(8):
            bit = (byte >> i) & 1
            top = (r >> 31) & 1
            r = (r << 1) & MASK32
            if top ^ bit:
                r ^= generator
    r ^= MASK32
    # The digest holds the highest power of each byte at its least significant bit.
    out = bytes(int(f"{(r >> shift) & 0xFF:08b}"[::-1], 2) for shift in (24, 16, 8, 0))
    return out


def reflect32(x):
    return int(f"{x:032b}"[::-1], 2)


def check():
    for size in (0, 1, 55, 56, 63, 64, 65, 119, 120, 200):
        data = bytes(range(256))[:size]
        assert sha256(data) == hashlib.sha256(data).digest(), "SHA-256"
        assert sha3_256(data) == hashlib.sha3_256(data).digest(), "Keccak-f"
        from Crypto.Hash import RIPEMD160, keccak as pykeccak

        assert ripemd160(data) == RIPEMD160.new(data).digest(), "RIPEMD-160"
        for bits, rate in ((224, 144), (256, 136), (384, 104), (512, 72)):
            want = pykeccak.new(digest_bits=bits, data=data).digest()
            assert keccak(rate, data, bits // 8) == want, "Keccak sponge"
        import zlib

        import crc32c

        assert crc(0x04C11DB7, data) == struct.pack("<I", zlib.crc32(data)), "CRC-32"
        assert crc(0x1EDC6F41, data) == struct.pack("<I", crc32c.crc32c(data)), "CRC-32C"


check()


def hkdf_expand(prk, info, length):
    # RFC 5869, section 2.3.
    if len(prk) < 32:
        return "error keyTooShort"
    if length > 255 * 32:
        return "error outputTooLong"
    out, t, i = b"", b"", 1
    while len(out) < length:
        t = hmac_module.new(prk, t + info + bytes([i]), "sha256").digest()
        out += t
        i += 1
    return tohex(out[:length])


def concat(z, info, length):
    # SP 800-56C Rev. 2, section 4.1, with SHA-256.
    if length == 0:
        return "error emptyOutput"
    out, counter = b"", 1
    while len(out) < length:
        out += hashlib.sha256(struct.pack(">I", counter) + z + info).digest()
        counter += 1
    return tohex(out[:length])


def scrypt(password, salt, n, r, p, length):
    # The rules of RFC 7914, section 2, then hashlib.
    if r == 0:
        return "error invalidBlockSize"
    if n < 2 or n & (n - 1) or n >= 2 ** (16 * r):
        return "error invalidCost"
    if p == 0 or p > (2**32 - 1) * 32 // (128 * r):
        return "error invalidParallelization"
    if length == 0:
        return "error emptyOutput"
    if length > (2**32 - 1) * 32:
        return "error outputTooLong"
    return tohex(hashlib.scrypt(password, salt=salt, n=n, r=r, p=p, dklen=length, maxmem=2**30))


def lanes(words):
    return [int(word) for word in words]


def answer(words):
    match words:
        case ["sha_compress", *state, block]:
            return " ".join(str(x) for x in sha_compress(lanes(state), unhex(block)))
        case ["sha_schedule", block]:
            return " ".join(str(x) for x in sha_schedule(unhex(block)))
        case ["sha_hash", data]:
            return hashlib.sha256(unhex(data)).hexdigest()
        case ["rmd_compress", *state, block]:
            return " ".join(str(x) for x in rmd_compress(lanes(state), unhex(block)))
        case ["keccak_f", *state]:
            return " ".join(str(x) for x in keccak_f(lanes(state)))
        case ["keccak_round", ir, *state]:
            return " ".join(str(x) for x in keccak_round(int(ir), lanes(state)))
        case ["keccak_step", name, *state]:
            return " ".join(str(x) for x in STEPS[name](lanes(state)))
        case ["keccak_absorb", rate, data]:
            return " ".join(str(x) for x in keccak_absorb(int(rate), unhex(data)))
        case ["keccak_pad", rate, length]:
            return tohex(keccak_pad(int(rate), int(length)))
        case ["crc", generator, data]:
            return crc(int(generator), unhex(data)).hex()
        case ["hmac", key, data]:
            return hmac_module.new(unhex(key), unhex(data), "sha256").hexdigest()
        case ["hkdf_expand", prk, info, length]:
            return hkdf_expand(unhex(prk), unhex(info), int(length))
        case ["hkdf", salt, ikm, info, length]:
            prk = hmac_module.new(unhex(salt), unhex(ikm), "sha256").digest()
            return hkdf_expand(prk, unhex(info), int(length))
        case ["pbkdf2", password, salt, iterations, length]:
            if int(iterations) == 0:
                return "error zeroIterations"
            if int(length) == 0:
                return "error emptyOutput"
            return hashlib.pbkdf2_hmac(
                "sha256", unhex(password), unhex(salt), int(iterations), int(length)
            ).hex()
        case ["concat", z, info, length]:
            return concat(unhex(z), unhex(info), int(length))
        case ["scrypt", password, salt, n, r, p, length]:
            return scrypt(unhex(password), unhex(salt), int(n), int(r), int(p), int(length))
    return None

"""Constant tables, each computed from the definition in its standard."""

# table <name>      The entries of a table, in order, in decimal.
# aesmul <a>        The 256 products of `a` in GF(2^8) of FIPS 197.
# setup <part>      The points of the KZG trusted setup, in hexadecimal.
# The names of the tables are the keys of `TABLES` below.

import hashlib
import json
import os
from math import isqrt

MASK64 = (1 << 64) - 1


def primes(count):
    found = []
    n = 2
    while len(found) < count:
        if all(n % p for p in found):
            found.append(n)
        n += 1
    return found


def icbrt(n):
    # The integer cube root, by bisection.
    lo, hi = 0, 1 << (n.bit_length() // 3 + 2)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**3 <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def sha256_k():
    # FIPS 180-4, section 4.2.2: the first 32 bits of the fractional parts of the cube roots.
    return [icbrt(p << 96) & 0xFFFFFFFF for p in primes(64)]


def sha256_iv():
    # FIPS 180-4, section 5.3.3: the same of the square roots of the first 8 primes.
    return [isqrt(p << 64) & 0xFFFFFFFF for p in primes(8)]


def blake2b_iv():
    # RFC 7693, section 2.6: floor(2^64 * frac(sqrt(p))), the initial value of SHA-512.
    return [isqrt(p << 128) & MASK64 for p in primes(8)]


# RFC 7693, section 2.7.  `check_blake2b` below runs BLAKE2b with it against hashlib.
BLAKE2B_SIGMA = [
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
    return ((x >> n) | (x << (64 - n))) & MASK64


def blake2b_f(rounds, h, m, t, last):
    # RFC 7693, section 3.2.
    v = h + blake2b_iv()
    v[12] ^= t & MASK64
    v[13] ^= t >> 64
    if last:
        v[14] ^= MASK64

    def g(a, b, c, d, x, y):
        v[a] = (v[a] + v[b] + x) & MASK64
        v[d] = rotr64(v[d] ^ v[a], 32)
        v[c] = (v[c] + v[d]) & MASK64
        v[b] = rotr64(v[b] ^ v[c], 24)
        v[a] = (v[a] + v[b] + y) & MASK64
        v[d] = rotr64(v[d] ^ v[a], 16)
        v[c] = (v[c] + v[d]) & MASK64
        v[b] = rotr64(v[b] ^ v[c], 63)

    for i in range(rounds):
        s = BLAKE2B_SIGMA[i % 10]
        g(0, 4, 8, 12, m[s[0]], m[s[1]])
        g(1, 5, 9, 13, m[s[2]], m[s[3]])
        g(2, 6, 10, 14, m[s[4]], m[s[5]])
        g(3, 7, 11, 15, m[s[6]], m[s[7]])
        g(0, 5, 10, 15, m[s[8]], m[s[9]])
        g(1, 6, 11, 12, m[s[10]], m[s[11]])
        g(2, 7, 8, 13, m[s[12]], m[s[13]])
        g(3, 4, 9, 14, m[s[14]], m[s[15]])
    return [h[i] ^ v[i] ^ v[i + 8] for i in range(8)]


def blake2b(data):
    # RFC 7693, section 3.3, with a digest of 64 bytes and no key.
    h = blake2b_iv()
    h[0] ^= 0x01010040
    blocks = [data[i : i + 128] for i in range(0, len(data), 128)] or [b""]
    for count, block in enumerate(blocks):
        last = count == len(blocks) - 1
        t = len(data) if last else 128 * (count + 1)
        block = block.ljust(128, b"\0")
        m = [int.from_bytes(block[8 * i : 8 * i + 8], "little") for i in range(16)]
        h = blake2b_f(12, h, m, t, last)
    return b"".join(x.to_bytes(8, "little") for x in h)


def check_blake2b():
    for size in (0, 1, 127, 128, 129, 300):
        data = bytes(range(256)) * 2
        assert blake2b(data[:size]) == hashlib.blake2b(data[:size]).digest(), "BLAKE2b"


# RIPEMD-160, Dobbertin, Bosselaers and Preneel, section 3 and Table 2.
RHO = [7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8]
# The rotation of message word `X_i` in each of the five rounds, for both lines.
RIPEMD_SHIFTS = [
    [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8],
    [12, 13, 11, 15, 6, 9, 9, 7, 12, 15, 11, 13, 7, 8, 7, 7],
    [13, 15, 14, 11, 7, 7, 6, 8, 13, 14, 13, 12, 5, 5, 6, 9],
    [14, 11, 12, 14, 8, 6, 5, 5, 15, 12, 15, 14, 9, 9, 8, 6],
    [15, 12, 13, 13, 9, 5, 8, 6, 14, 11, 12, 11, 8, 6, 5, 5],
]


def ripemd_orders():
    # The left line reads the words in the orders id, rho, rho^2, rho^3, rho^4.
    # The right line reads them in the orders pi, rho pi, ..., with pi(i) = 9 i + 5 mod 16.
    left, right = [], []
    order = list(range(16))
    other = [(9 * i + 5) % 16 for i in range(16)]
    for _ in range(5):
        left += order
        right += other
        order = [RHO[i] for i in order]
        other = [RHO[i] for i in other]
    return left, right


def ripemd_shifts(order):
    return [RIPEMD_SHIFTS[j // 16][order[j]] for j in range(80)]


def keccak_rc_bit(t):
    # FIPS 202, Algorithm 5.
    if t % 255 == 0:
        return 1
    r = [1, 0, 0, 0, 0, 0, 0, 0]
    for _ in range(t % 255):
        r = [0] + r
        r[0] ^= r[8]
        r[4] ^= r[8]
        r[5] ^= r[8]
        r[6] ^= r[8]
        r = r[:8]
    return r[0]


def keccak_rc():
    # FIPS 202, Algorithm 6: bit 2^j - 1 of the constant of round i is rc(j + 7 i).
    out = []
    for i in range(24):
        rc = 0
        for j in range(7):
            rc |= keccak_rc_bit(j + 7 * i) << (2**j - 1)
        out.append(rc)
    return out


def keccak_rho():
    # FIPS 202, Algorithm 2, with lane (x, y) at index x + 5 y.
    out = [0] * 25
    x, y = 1, 0
    for t in range(24):
        out[x + 5 * y] = (t + 1) * (t + 2) // 2 % 64
        x, y = y, (2 * x + 3 * y) % 5
    return out


def xtime(b):
    b <<= 1
    return (b ^ 0x11B) & 0xFF if b & 0x100 else b


def gf_mul(a, b):
    # The product in GF(2^8) modulo x^8 + x^4 + x^3 + x + 1, FIPS 197, section 4.2.
    out = 0
    while b:
        if b & 1:
            out ^= a
        a = xtime(a)
        b >>= 1
    return out


def aes_sbox():
    # FIPS 197, section 5.1.1: the inverse in the field, then the affine map with {63}.
    out = []
    for b in range(256):
        inverse = next((c for c in range(256) if gf_mul(b, c) == 1), 0)
        s = 0
        for i in range(8):
            bit = (
                (inverse >> i)
                ^ (inverse >> (i + 4) % 8)
                ^ (inverse >> (i + 5) % 8)
                ^ (inverse >> (i + 6) % 8)
                ^ (inverse >> (i + 7) % 8)
                ^ (0x63 >> i)
            ) & 1
            s |= bit << i
        out.append(s)
    return out


def aes_inv_sbox():
    sbox = aes_sbox()
    out = [0] * 256
    for b, s in enumerate(sbox):
        out[s] = b
    return out


def aes_rcon():
    # FIPS 197, section 5.2: Rcon[j] = x^(j - 1), for j from 1.
    out, value = [], 1
    for _ in range(30):
        out.append(value)
        value = xtime(value)
    return out


def setup(part):
    # The trusted setup of the ceremony, as the consensus specifications ship it.
    import eth_consensus_specs

    root = os.path.dirname(os.path.dirname(eth_consensus_specs.__file__))
    path = os.path.join(root, "presets", "mainnet", "trusted_setups", "trusted_setup_4096.json")
    with open(path) as file:
        data = json.load(file)
    return " ".join(point.removeprefix("0x") for point in data[part])


TABLES = {
    "sha256_k": sha256_k,
    "sha256_iv": sha256_iv,
    "blake2b_iv": blake2b_iv,
    "blake2b_sigma": lambda: [x for row in BLAKE2B_SIGMA for x in row],
    "ripemd_k": lambda: [0] + [isqrt(p << 60) for p in (2, 3, 5, 7)],
    "ripemd_kp": lambda: [icbrt(p << 90) for p in (2, 3, 5, 7)] + [0],
    "ripemd_r": lambda: ripemd_orders()[0],
    "ripemd_rp": lambda: ripemd_orders()[1],
    "ripemd_s": lambda: ripemd_shifts(ripemd_orders()[0]),
    "ripemd_sp": lambda: ripemd_shifts(ripemd_orders()[1]),
    "ripemd_iv": lambda: [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0],
    "keccak_rc": keccak_rc,
    "keccak_rho": keccak_rho,
    "aes_sbox": aes_sbox,
    "aes_inv_sbox": aes_inv_sbox,
    "aes_rcon": aes_rcon,
}

check_blake2b()


def answer(words):
    match words:
        case ["table", name]:
            return " ".join(str(x) for x in TABLES[name]())
        case ["aesmul", a]:
            return " ".join(str(gf_mul(int(a), b)) for b in range(256))
        case ["setup", part]:
            return setup(part)
    return None

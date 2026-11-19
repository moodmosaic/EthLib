"""Call data for the precompiles, built from a recipe by reference libraries.

A recipe is a kind, three numbers, a mutation and a cut.  The numbers give a
valid input (points from scalars, a signature from a key), the mutation
breaks one rule of the precompile, and the cut changes the length.  The
driver draws the recipe, so a failure shrinks to small numbers.
"""

import hashlib

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import (
    Prehashed,
    decode_dss_signature,
)
from eth_keys import keys
from py_ecc import bls12_381 as bls, bn128 as bn
from py_ecc.bls.point_compression import compress_G1 as compress_g1_int

SECP_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
SECP_P = 2**256 - 2**32 - 977
P256_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
P256_P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
BLS_MODULUS = bls.curve_order


def compress_g1(point):
    return int(compress_g1_int(point)).to_bytes(48, "big")


def word(n, size=32):
    return (n % 256**size).to_bytes(size, "big")


def sqrt_fp2(curve, a):
    """A square root in Fp2 of a curve whose p is 3 modulo 4, or None."""
    p = curve.field_modulus
    one = curve.FQ2.one()
    a1 = a ** ((p - 3) // 4)
    alpha = a1 * a1 * a
    x0 = a1 * a
    if alpha == -one:
        x = curve.FQ2([0, 1]) * x0
    else:
        x = (one + alpha) ** ((p - 1) // 2) * x0
    return x if x * x == a else None


def off_subgroup_g2(curve, seed):
    """A point of the twist that is outside the subgroup of order r."""
    x = curve.FQ2([seed % 1000 + 1, 1])
    while True:
        y = sqrt_fp2(curve, x * x * x + curve.b2)
        if y is not None:
            point = (x, y)
            if curve.multiply(point, curve.curve_order) is not None:
                return point
        x = x + curve.FQ2.one()


def off_subgroup_g1(seed):
    """A point of BLS12-381 over Fp that is outside the subgroup."""
    p = bls.field_modulus
    x = seed % 1000 + 1
    while True:
        rhs = (x**3 + 4) % p
        y = pow(rhs, (p + 1) // 4, p)
        if y * y % p == rhs:
            point = (bls.FQ(x), bls.FQ(y))
            if bls.multiply(point, bls.curve_order) is not None:
                return point
        x += 1


# Coordinates as lists of integers, so a mutation can leave the field.


def g1_ints(point):
    return [0, 0] if point is None else [int(point[0]), int(point[1])]


def g2_ints(point):
    """The four integers of a G2 point: x real, x imaginary, y real, y imaginary."""
    if point is None:
        return [0, 0, 0, 0]
    return [int(c) for c in point[0].coeffs] + [int(c) for c in point[1].coeffs]


def bn_g1(ints):
    return word(ints[0]) + word(ints[1])


def bn_g2(ints):
    # EIP-197 writes the imaginary part first.
    return word(ints[1]) + word(ints[0]) + word(ints[3]) + word(ints[2])


def bls_g1(ints):
    return word(ints[0], 64) + word(ints[1], 64)


def bls_g2(ints):
    return b"".join(word(c, 64) for c in ints)


def mutate_point(ints, mutation, modulus):
    """Break one rule of a point: 1 not reduced, 2 off the curve, 3 infinity."""
    ints = list(ints)
    if mutation == 1:
        ints[0] += modulus
    elif mutation == 2:
        ints[-1] = (ints[-1] + 1) % modulus
    elif mutation == 3:
        ints = [0] * len(ints)
    elif mutation == 4:
        ints[-1] = modulus
    return ints


def ecrecover(a, b, c, mutation):
    key = keys.PrivateKey(word(a % (SECP_N - 1) + 1))
    digest = word(b)
    signature = key.sign_msg_hash(digest)
    v, r, s = signature.v + 27, signature.r, signature.s
    if mutation == 1:
        v -= 27
    elif mutation == 2:
        v = 29
    elif mutation == 3:
        v += 256 ** (1 + c % 31)
    elif mutation == 4:
        r = 0
    elif mutation == 5:
        r = SECP_N
    elif mutation == 6:
        s = 0
    elif mutation == 7:
        s = SECP_N
    elif mutation == 8:
        s = SECP_N - s
    elif mutation == 9:
        r = c
    elif mutation == 10:
        v = 55 - v
    elif mutation == 11:
        r, s = SECP_N - 1, SECP_N - 1
    elif mutation == 12:
        r = SECP_P - 1 - c % 1000
    elif mutation == 13:
        v = 26
    return digest + word(v) + word(r) + word(s)


def bn_point(k):
    return bn.multiply(bn.G1, k % bn.curve_order) if k % bn.curve_order else None


def bn_add(a, b, c, mutation):
    p, q = g1_ints(bn_point(a)), g1_ints(bn_point(b))
    if mutation == 5:
        q = [p[0], (-p[1]) % bn.field_modulus] if a % bn.curve_order else q
    elif mutation == 6:
        q = p
    elif mutation == 7:
        p = [0, 2]
    elif mutation >= 8:
        q = mutate_point(q, mutation - 7, bn.field_modulus)
    else:
        p = mutate_point(p, mutation, bn.field_modulus)
    return bn_g1(p) + bn_g1(q)


def bn_mul(a, b, c, mutation):
    scalars = [b, 0, 1, bn.curve_order, bn.curve_order + 1, 2**256 - 1, 2]
    scalar = scalars[mutation - 4] if 5 <= mutation <= 10 else b
    p = mutate_point(g1_ints(bn_point(a)), mutation, bn.field_modulus)
    return bn_g1(p) + word(scalar)


def bn_pairing(a, b, c, mutation):
    n = bn.curve_order
    a, b = a % n or 1, b % n or 1
    g1a = g1_ints(bn_point(a))
    g2b = g2_ints(bn.multiply(bn.G2, b))
    last = g1_ints(bn_point(n - a * b % n))
    g2 = g2_ints(bn.G2)
    if mutation == 1:
        last = g1_ints(bn_point(c))
    elif mutation == 2:
        return b""
    elif mutation == 3:
        g2b = g2_ints(off_subgroup_g2(bn, c))
    elif mutation == 4:
        g2b[c % 4] += bn.field_modulus
    elif mutation == 5:
        g1a[1] = (g1a[1] + 1) % bn.field_modulus
    elif mutation == 6:
        g1a, last = [0, 0], [0, 0]
    elif mutation == 7:
        g2b, last = [0, 0, 0, 0], [0, 0]
    elif mutation == 8:
        g2b[3] = (g2b[3] + 1) % bn.field_modulus
    elif mutation == 9:
        g1a[0] += bn.field_modulus
    elif mutation == 10:
        return bn_g1(g1a) + bn_g2(g2b)
    elif mutation == 11:
        g2b[c % 4] = bn.field_modulus
    elif mutation == 12:
        return bn_g1([0, 0]) + bn_g2([0, 0, 0, 0])
    return bn_g1(g1a) + bn_g2(g2b) + bn_g1(last) + bn_g2(g2)


def bls_point1(k):
    k %= bls.curve_order
    return bls.multiply(bls.G1, k) if k else None


def bls_point2(k):
    k %= bls.curve_order
    return bls.multiply(bls.G2, k) if k else None


def bls_mutate(data, mutation, c, size):
    """Break the padding of a field element: a nonzero byte in its top 16."""
    if mutation == 5:
        index = (c % (len(data) // 64)) * 64 + c % 16
        data = data[:index] + b"\x01" + data[index + 1 :]
    return data


def bls_g1add(a, b, c, mutation):
    p, q = g1_ints(bls_point1(a)), g1_ints(bls_point1(b))
    if mutation == 6:
        p = g1_ints(off_subgroup_g1(c))
    elif mutation == 7:
        q = [p[0], (-p[1]) % bls.field_modulus] if p != [0, 0] else q
    elif mutation == 8:
        q = p
    elif mutation == 9:
        p, q = g1_ints(off_subgroup_g1(c)), g1_ints(off_subgroup_g1(c + 1))
    else:
        p = mutate_point(p, mutation, bls.field_modulus)
    return bls_mutate(bls_g1(p) + bls_g1(q), mutation, c, 64)


def bls_g2add(a, b, c, mutation):
    p, q = g2_ints(bls_point2(a)), g2_ints(bls_point2(b))
    if mutation == 6:
        p = g2_ints(off_subgroup_g2(bls, c))
    elif mutation == 7:
        q = p
    elif mutation == 8:
        p[1] += bls.field_modulus
    else:
        p = mutate_point(p, mutation, bls.field_modulus)
    return bls_mutate(bls_g2(p) + bls_g2(q), mutation, c, 64)


def scalar_of(c, mutation):
    scalars = {10: 0, 11: bls.curve_order, 12: 2**256 - 1, 13: 1}
    return scalars.get(mutation, c)


def bls_g1msm(a, b, c, mutation):
    points = [bls_point1(a), bls_point1(b), bls_point1(a + b)][: 1 + c % 3]
    out = b""
    for i, point in enumerate(points):
        ints = g1_ints(point)
        if i == 0:
            if mutation == 6:
                ints = g1_ints(off_subgroup_g1(c))
            else:
                ints = mutate_point(ints, mutation, bls.field_modulus)
        out += bls_g1(ints) + word(scalar_of(c + i * a, mutation))
    if mutation == 14:
        return b""
    return bls_mutate(out, mutation, c, 64)


def bls_g2msm(a, b, c, mutation):
    points = [bls_point2(a), bls_point2(b)][: 1 + c % 2]
    out = b""
    for i, point in enumerate(points):
        ints = g2_ints(point)
        if i == 0:
            if mutation == 6:
                ints = g2_ints(off_subgroup_g2(bls, c))
            else:
                ints = mutate_point(ints, mutation, bls.field_modulus)
        out += bls_g2(ints) + word(scalar_of(c + i * a, mutation))
    if mutation == 14:
        return b""
    return bls_mutate(out, mutation, c, 64)


def bls_pairing(a, b, c, mutation):
    n = bls.curve_order
    a, b = a % n or 1, b % n or 1
    g1a, g2b = g1_ints(bls_point1(a)), g2_ints(bls_point2(b))
    last, g2 = g1_ints(bls_point1(n - a * b % n)), g2_ints(bls.G2)
    if mutation == 1:
        last = g1_ints(bls_point1(c))
    elif mutation == 2:
        return b""
    elif mutation == 3:
        g2b = g2_ints(off_subgroup_g2(bls, c))
    elif mutation == 4:
        g1a = g1_ints(off_subgroup_g1(c))
    elif mutation == 6:
        g1a, last = [0, 0], [0, 0]
    elif mutation == 7:
        g2b, last = [0, 0, 0, 0], [0, 0]
    elif mutation == 8:
        g2b[c % 4] += bls.field_modulus
    elif mutation == 9:
        g1a[0] += bls.field_modulus
    elif mutation == 10:
        return bls_g1(g1a) + bls_g2(g2b)
    elif mutation == 11:
        g1a[1] = (g1a[1] + 1) % bls.field_modulus
    out = bls_g1(g1a) + bls_g2(g2b) + bls_g1(last) + bls_g2(g2)
    return bls_mutate(out, mutation, c, 64)


def bls_mapfp(a, b, c, mutation):
    p = bls.field_modulus
    values = [a % p, 0, 1, p - 1, p, p + 1, 2**381, a % 2**384]
    data = word(values[mutation % len(values)], 64)
    return bls_mutate(data, 5 if mutation == 9 else 0, c, 64)


def bls_mapfp2(a, b, c, mutation):
    p = bls.field_modulus
    values = [a % p, 0, 1, p - 1, p, p + 1, 2**381, a % 2**384]
    data = word(b % p, 64) + word(values[mutation % len(values)], 64)
    if mutation >= 10:
        data = data[64:] + data[:64]
    return bls_mutate(data, 5 if mutation == 9 else 0, c, 64)


def point_evaluation(a, b, c, mutation):
    # A constant polynomial `a`: its commitment is a * G1, its proof is the
    # point at infinity, and it is `a` at every `z`.
    a %= BLS_MODULUS
    commitment = compress_g1(bls_point1_fast(a))
    proof = compress_g1(bls_point1_fast(0))
    z, y = b % BLS_MODULUS, a
    version = 1
    if mutation == 1:
        y = (y + 1) % BLS_MODULUS
    elif mutation == 2:
        z = BLS_MODULUS + c % 1000
    elif mutation == 3:
        y = BLS_MODULUS + a if a < 2**256 - BLS_MODULUS else BLS_MODULUS
    elif mutation == 4:
        version = c % 256
    elif mutation == 5:
        proof = compress_g1(bls_point1_fast(c or 1))
    elif mutation == 6:
        commitment = compress_g1(bls_point1_fast(a + 1))
    elif mutation == 7:
        commitment = bytes([commitment[0] ^ 0x20]) + commitment[1:]
    elif mutation == 8:
        proof = b"\x00" * 48
    elif mutation == 9:
        z = BLS_MODULUS - 1
    hashed = bytes([version]) + hashlib.sha256(commitment).digest()[1:]
    if mutation == 10:
        hashed = hashed[:31] + bytes([hashed[31] ^ 1])
    if mutation == 11:
        commitment = b"\xc0" + b"\x00" * 46 + b"\x01"
    return hashed + word(z) + word(y) + commitment + proof


def bls_point1_fast(k):
    from py_ecc.optimized_bls12_381 import G1, Z1, multiply

    k %= bls.curve_order
    return multiply(G1, k) if k else Z1


def p256(a, b, c, mutation):
    private = ec.derive_private_key(a % (P256_N - 1) + 1, ec.SECP256R1())
    digest = word(b)
    signature = private.sign(digest, ec.ECDSA(Prehashed(hashes.SHA256())))
    r, s = decode_dss_signature(signature)
    numbers = private.public_key().public_numbers()
    x, y = numbers.x, numbers.y
    if mutation == 1:
        r = 0
    elif mutation == 2:
        s = 0
    elif mutation == 3:
        r = P256_N
    elif mutation == 4:
        s = P256_N
    elif mutation == 5:
        s = P256_N - s
    elif mutation == 6:
        x, y = 0, 0
    elif mutation == 7:
        y = (y + 1) % P256_P
    elif mutation == 8:
        x += P256_P if x < 2**256 - P256_P else 0
    elif mutation == 9:
        digest = word(b + 1)
    elif mutation == 10:
        r = (r + P256_N) if r + P256_N < 2**256 else r
    elif mutation == 11:
        y = P256_P - y
    elif mutation == 12:
        r = c
    elif mutation == 13:
        x = P256_P
    return digest + word(r) + word(s) + word(x) + word(y)


KINDS = {
    "ecrecover": ecrecover,
    "bnadd": bn_add,
    "bnmul": bn_mul,
    "bnpairing": bn_pairing,
    "g1add": bls_g1add,
    "g1msm": bls_g1msm,
    "g2add": bls_g2add,
    "g2msm": bls_g2msm,
    "blspairing": bls_pairing,
    "mapfp": bls_mapfp,
    "mapfp2": bls_mapfp2,
    "pointeval": point_evaluation,
    "p256": p256,
}


def make(kind, a, b, c, mutation, cut):
    data = KINDS[kind](int(a), int(b), int(c), int(mutation))
    cut = int(cut)
    if cut == 1:
        data = data[:-1]
    elif cut == 2:
        data = data + b"\x00"
    elif cut == 3:
        data = data[: len(data) // 2]
    elif cut == 4:
        data = data + data[:32]
    elif cut == 5:
        data = data + b"\x01"
    return data

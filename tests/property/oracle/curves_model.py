"""Models written from the source texts, on Python integers."""

# SEC 1 v2 for the group law, ECDSA and recovery, and RFC 6979 section 3.2
# for the nonce.  Nothing here reads EthLib.

import hashlib
import hmac
from dataclasses import dataclass


@dataclass(frozen=True)
class Curve:
    p: int
    a: int
    b: int
    n: int
    g: tuple


K1 = Curve(
    p=2**256 - 2**32 - 977,
    a=0,
    b=7,
    n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
    g=(
        0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
        0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
    ),
)

R1 = Curve(
    p=0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF,
    a=0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC,
    b=0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
    n=0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
    g=(
        0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
        0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
    ),
)

BN = Curve(
    p=21888242871839275222246405745257275088696311157297823662689037894645226208583,
    a=0,
    b=3,
    n=21888242871839275222246405745257275088548364400416034343698204186575808495617,
    g=(1, 2),
)


def on_curve(c, pt):
    if pt is None:
        return True
    x, y = pt
    return (y * y - (x * x * x + c.a * x + c.b)) % c.p == 0


def add(c, p1, p2):
    """SEC 1 v2 section 2.2.1; None is the point at infinity."""
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2:
        if (y1 + y2) % c.p == 0:
            return None
        lam = (3 * x1 * x1 + c.a) * pow(2 * y1, -1, c.p) % c.p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, c.p) % c.p
    x3 = (lam * lam - x1 - x2) % c.p
    return (x3, (lam * (x1 - x3) - y1) % c.p)


def neg(c, pt):
    return None if pt is None else (pt[0], -pt[1] % c.p)


def mul(c, k, pt):
    acc = None
    while k:
        if k & 1:
            acc = add(c, acc, pt)
        pt = add(c, pt, pt)
        k >>= 1
    return acc


def lift_x(c, x, odd):
    """The point with this x and this parity of y, for p = 3 mod 4."""
    if x >= c.p:
        return None
    rhs = (x * x * x + c.a * x + c.b) % c.p
    y = pow(rhs, (c.p + 1) // 4, c.p)
    if y * y % c.p != rhs:
        return None
    return (x, y if (y & 1) == odd else c.p - y)


def verify(c, q, e, r, s):
    """SEC 1 v2 section 4.1.4, with the key validation of section 3.2.2.1."""
    if not (1 <= r < c.n and 1 <= s < c.n):
        return False
    if q is None or not (q[0] < c.p and q[1] < c.p) or not on_curve(c, q):
        return False
    w = pow(s, -1, c.n)
    pt = add(c, mul(c, e * w % c.n, c.g), mul(c, r * w % c.n, q))
    return pt is not None and pt[0] % c.n == r


def recover(c, e, r, s, odd):
    """SEC 1 v2 section 4.1.6 with j = 0: the ids 0 and 1 of Ethereum."""
    if not (1 <= r < c.n and 1 <= s < c.n):
        return None
    big_r = lift_x(c, r, odd)
    if big_r is None:
        return None
    w = pow(r, -1, c.n)
    return add(c, mul(c, s * w % c.n, big_r), mul(c, -e * w % c.n, c.g))


def nonces(q, x, h1):
    """RFC 6979 section 3.2 with HMAC-SHA-256 and qlen = 256: every candidate."""

    def mac(key, data):
        return hmac.new(key, data, hashlib.sha256).digest()

    material = x.to_bytes(32, "big") + (int.from_bytes(h1, "big") % q).to_bytes(32, "big")
    v = b"\x01" * 32
    k = b"\x00" * 32
    k = mac(k, v + b"\x00" + material)
    v = mac(k, v)
    k = mac(k, v + b"\x01" + material)
    v = mac(k, v)
    while True:
        v = mac(k, v)
        yield int.from_bytes(v, "big")
        k = mac(k, v + b"\x00")
        v = mac(k, v)


def sign(c, d, h1, tries=16):
    """SEC 1 v2 section 4.1.3 with the nonce of RFC 6979: (r, s, R)."""
    e = int.from_bytes(h1, "big") % c.n
    gen = nonces(c.n, d, h1)
    for _ in range(tries):
        k = next(gen)
        if not 1 <= k < c.n:
            continue
        big_r = mul(c, k, c.g)
        r = big_r[0] % c.n
        s = pow(k, -1, c.n) * (e + r * d) % c.n
        if r == 0 or s == 0:
            continue
        return r, s, big_r
    return None

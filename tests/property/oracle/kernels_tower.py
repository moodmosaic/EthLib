"""Extension fields and pairings of BLS12-381 and alt_bn128, by py_ecc."""

# An element of Fp12 is its 12 coefficients of 1, w, ..., w^11, joined by commas.
# BLS12-381: w^12 = 2 w^6 - 2, with i = w^6 - 1.  alt_bn128: w^12 = 18 w^6 - 82.
#
# f12 <curve> mul <a> <b>     The product.
# f12 <curve> inv <a>         The inverse, and 0 for 0.
# f12 <curve> pow <a> <e>     The power.
# f12 <curve> frob <a> <n>    The power by p^n.
# f12 <curve> final <a>       The power by (p^12 - 1) / r.
# f12 <curve> easy <a>        The power by (p^6 - 1) (p^2 + 1), in the cyclotomic subgroup.
# blspair <P> <Q>             py_ecc's pairing of P = x,y in G1 and Q = x0,x1,y0,y1 in G2.
# blsmiller <s> <P> <Q>       f_{s,Q}(P) to the power (p^12 - 1) / r, for any s.
# curve <name>                The constants of a curve.
# mulg <curve> <k>            `k G` on secp256k1 (`k1`) or P-256 (`r1`), or `inf`.

from py_ecc import bls12_381 as bls, bn128 as bn, optimized_bls12_381 as obls
from py_ecc.bls12_381 import bls12_381_pairing as pairing
from py_ecc.bn128 import bn128_pairing
from py_ecc.fields import (
    bls12_381_FQ2,
    bls12_381_FQ12,
    optimized_bls12_381_FQ12,
    optimized_bn128_FQ12,
)

FIELDS = {
    "bls": (optimized_bls12_381_FQ12, bls.field_modulus, bls.curve_order),
    "bn": (optimized_bn128_FQ12, bn.field_modulus, bn.curve_order),
}


def element(curve, word):
    return FIELDS[curve][0]([int(x) for x in word.split(",")])


def show(x):
    return ",".join(str(int(c)) for c in x.coeffs)


def f12(curve, op, a, rest):
    field, p, r = FIELDS[curve]
    x = element(curve, a)
    match op, rest:
        case "mul", [b]:
            return show(x * element(curve, b))
        case "inv", []:
            return show(x if x == field.zero() else x.inv())
        case "pow", [e]:
            return show(x ** int(e))
        case "frob", [n]:
            return show(x ** (p ** int(n)))
        case "final", []:
            return show(x ** ((p**12 - 1) // r))
        case "easy", []:
            return show(x ** ((p**6 - 1) * (p**2 + 1)))
    return "error unknown operation"


def g1(word):
    x, y = (int(v) for v in word.split(","))
    return (x, y)


def g2(word):
    x0, x1, y0, y1 = (int(v) for v in word.split(","))
    return ((x0, x1), (y0, y1))


def blspair(p, q):
    x, y = g1(p)
    (x0, x1), (y0, y1) = g2(q)
    point = (obls.FQ(x), obls.FQ(y), obls.FQ(1))
    twisted = (obls.FQ2([x0, x1]), obls.FQ2([y0, y1]), obls.FQ2([1, 0]))
    return show(obls.pairing(twisted, point))


def blsmiller(s, p, q):
    # The Miller function of any s, by the affine lines of py_ecc on the curve over Fp12.
    x, y = g1(p)
    (x0, x1), (y0, y1) = g2(q)
    point = pairing.cast_point_to_fq12((bls.FQ(x), bls.FQ(y)))
    base = bls.twist((bls12_381_FQ2([x0, x1]), bls12_381_FQ2([y0, y1])))
    f = bls12_381_FQ12.one()
    at = base
    for bit in bin(s)[3:]:
        f = f * f * pairing.linefunc(at, at, point)
        at = bls.double(at)
        if bit == "1":
            f = f * pairing.linefunc(at, base, point)
            at = bls.add(at, base)
    fast = optimized_bls12_381_FQ12([int(c) for c in f.coeffs])
    return show(fast ** ((bls.field_modulus**12 - 1) // bls.curve_order))


def curve(name):
    match name:
        case "bls":
            return " ".join(
                str(int(v))
                for v in [
                    bls.field_modulus,
                    bls.curve_order,
                    bls.G1[0],
                    bls.G1[1],
                    *bls.G2[0].coeffs,
                    *bls.G2[1].coeffs,
                    bls.b,
                    *bls.b2.coeffs,
                ]
            )
        case "bn":
            return " ".join(
                str(int(v))
                for v in [
                    bn.field_modulus,
                    bn.curve_order,
                    bn.G1[0],
                    bn.G1[1],
                    *bn.G2[0].coeffs,
                    *bn.G2[1].coeffs,
                    bn.b,
                    *bn.b2.coeffs,
                    bn128_pairing.ate_loop_count,
                    bn128_pairing.log_ate_loop_count,
                ]
            )
        case "k1":
            from py_ecc.secp256k1 import secp256k1 as k1

            return " ".join(str(v) for v in [k1.P, k1.N, k1.A, k1.B, k1.Gx, k1.Gy])
        case "r1":
            from cryptography.hazmat.primitives.asymmetric import ec

            numbers = ec.derive_private_key(1, ec.SECP256R1()).public_key().public_numbers()
            return f"{numbers.x} {numbers.y}"
    return "error unknown curve"


def mulg(name, k):
    if name == "k1":
        from py_ecc.secp256k1 import secp256k1 as k1

        k %= k1.N
        if k == 0:
            return "inf"
        x, y = k1.multiply(k1.G, k)
        return f"{x},{y}"
    from cryptography.hazmat.primitives.asymmetric import ec

    k %= 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
    if k == 0:
        return "inf"
    numbers = ec.derive_private_key(k, ec.SECP256R1()).public_key().public_numbers()
    return f"{numbers.x},{numbers.y}"


def answer(words):
    match words:
        case ["mulg", name, k]:
            return mulg(name, int(k))
        case ["f12", name, op, a, *rest]:
            return f12(name, op, a, rest)
        case ["blspair", p, q]:
            return blspair(p, q)
        case ["blsmiller", s, p, q]:
            return blsmiller(int(s), p, q)
        case ["curve", name]:
            return curve(name)
    return None

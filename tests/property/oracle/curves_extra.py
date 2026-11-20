"""References of the third round: every tag, every branch and every index of the curves."""

# The commands, each a line of words separated by tabs:
#
#     dsts                               the two tags of the proof-of-possession suite
#     h2g2any msg dst                    the hash to `G2` under any tag
#     coresign sk msg dst                `CoreSign` under any tag
#     coreverify pk msg sig dst          `CoreVerify` under any tag
#     coreaggverify pks msgs sig dst     `CoreAggregateVerify` under any tag
#     derivechild parent index           `derive_child_SK` of ERC-2333
#     g2real y                           a point of the twist whose y is the real number y
#     heffg2 x0,x1,y0,y1                 the multiple of a point by `h_eff` of RFC 9380
#     bntwist seed                       a point of the twist of alt_bn128, off its subgroup
#     swuroot curve                      the inputs that send a map to the kernel of its isogeny
#     sphincscodeword digest             the codeword of a digest of leanSPHINCS, or `none`
#     sphincsadrs type layer tree key word2 word3
#     sphincskey layer index             the tree and the leaf of a one-time key
#     xmssaddress tau mu hi lo           an address of leanXMSS

import hashlib

import curves_bls
import curves_sphincs
import curves_xmss
from py_ecc import optimized_bls12_381 as bls, optimized_bn128 as bn
from py_ecc.bls import G2Basic, G2ProofOfPossession as Pop, hash_to_curve as h2c
from py_ecc.bls.g2_primitives import G2_to_signature, signature_to_G2
from py_ecc.bls.point_compression import compress_G2
from py_ecc.optimized_bls12_381 import constants

P = bls.field_modulus
R = bls.curve_order
# `h_eff` of RFC 9380 section 8.8.2, as the RFC prints it.
H_EFF_G2 = int(
    "bc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d"
    "1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551",
    16,
)


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def hash_to_g2(msg, dst):
    """`hash_to_curve` of RFC 9380 section 3 for any tag, with py_ecc's maps."""
    uniform = curves_bls.expand_message_xmd(msg, dst, 256)
    numbers = [int.from_bytes(uniform[i : i + 64], "big") % P for i in range(0, 256, 64)]
    u0, u1 = bls.FQ2(numbers[0:2]), bls.FQ2(numbers[2:4])
    point = h2c.clear_cofactor_G2(bls.add(h2c.map_to_curve_G2(u0), h2c.map_to_curve_G2(u1)))
    if 0 < len(dst) <= 255:
        assert bls.eq(point, h2c.hash_to_G2(msg, dst, hashlib.sha256)), "py_ecc disagrees"
    return point


def short(dst):
    """The tag that py_ecc takes: a long one hashed, as RFC 9380 section 5.3.3 says."""
    if len(dst) > 255:
        return hashlib.sha256(b"H2C-OVERSIZE-DST-" + dst).digest()
    return dst


def core_sign(sk, msg, dst):
    """Section 2.6 of the BLS signature draft: `SK * hash_to_point(message)`."""
    sig = G2_to_signature(bls.multiply(hash_to_g2(msg, dst), sk))
    if dst:
        assert sig == G2Basic._CoreSign(sk, msg, short(dst)), "py_ecc disagrees"
    return bytes(sig).hex()


def core_verify(pk, msg, sig, dst):
    """Section 2.7 of the draft, by py_ecc, and by the pairings when the tag is empty."""
    if dst:
        return curves_bls.guarded(lambda: G2Basic._CoreVerify(pk, msg, sig, short(dst)))

    def run():
        point = signature_to_G2(sig)
        if not curves_bls.subgroup_check(point) or not Pop.KeyValidate(pk):
            return False
        key = curves_bls.pc.decompress_G1(curves_bls.pc.G1Compressed(int.from_bytes(pk, "big")))
        left = bls.pairing(point, bls.G1, final_exponentiate=False)
        right = bls.pairing(hash_to_g2(msg, dst), bls.neg(key), final_exponentiate=False)
        return bls.final_exponentiate(left * right) == bls.FQ12.one()

    return curves_bls.guarded(run)


def cube_root(a):
    """A cube root in `Fp2`, or None: the method of Tonelli and Shanks for the exponent 3."""
    q = P * P
    if a == bls.FQ2.zero():
        return a
    if a ** ((q - 1) // 3) != bls.FQ2.one():
        return None
    s, t = 0, q - 1
    while t % 3 == 0:
        s, t = s + 1, t // 3
    # A generator of the subgroup of order `3^s`, from an element that is no cube.
    g = bls.FQ2([1, 1])
    while g ** ((q - 1) // 3) == bls.FQ2.one():
        g = g + bls.FQ2.one()
    c = g**t
    x = a ** pow(3, -1, t)
    # `x^3 / a` has order `3^(s - 1)` at most: it is `c^(3 k)` for one `k` below it.
    b = x**3 / a
    for k in range(3 ** (s - 1)):
        if c ** (3 * k) == b:
            return x / c**k
    return None


def g2_real(y):
    """The compressed point of the twist with the real `y`, larger or smaller, or `none`."""
    x = cube_root(bls.FQ2([y * y % P, 0]) - bls.b2)
    if x is None:
        return "none"
    point = (x, bls.FQ2([y, 0]), bls.FQ2.one())
    assert bls.is_on_curve(point, bls.b2), "not on the twist"
    z1, z2 = compress_G2(point)
    return (z1.to_bytes(48, "big") + z2.to_bytes(48, "big")).hex()


def poly_mulmod(a, b, modulus, field):
    """The product of two polynomials modulo a monic one, lowest coefficient first."""
    out = [field(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = out[i + j] + x * y
    degree = len(modulus) - 1
    for i in range(len(out) - 1, degree - 1, -1):
        lead = out[i]
        for j in range(degree + 1):
            out[i - degree + j] = out[i - degree + j] - lead * modulus[j]
    return out[:degree] + [field(0)] * (degree - len(out))


def poly_trim(a, zero):
    while a and a[-1] == zero:
        a = a[:-1]
    return a


def poly_gcd(a, b, zero):
    """The monic greatest common divisor of two polynomials."""
    a, b = poly_trim(a, zero), poly_trim(b, zero)
    while b:
        while len(a) >= len(b):
            factor = a[-1] / b[-1]
            shift = len(a) - len(b)
            a = poly_trim(
                [x - factor * b[i - shift] if i >= shift else x for i, x in enumerate(a)][:-1],
                zero,
            )
        a, b = b, a
    return [x / a[-1] for x in a]


def poly_roots(modulus, field, size):
    """The roots, in a field of `size` elements, of a monic polynomial of small degree."""
    zero, one = field(0), field(1)
    degree = len(modulus) - 1
    # `x^size - x` has every element of the field as a root.
    power, base, e = [one] + [zero] * (degree - 1), [zero, one] + [zero] * (degree - 2), size
    while e:
        if e & 1:
            power = poly_mulmod(power, base, modulus, field)
        base = poly_mulmod(base, base, modulus, field)
        e >>= 1
    power[1] = power[1] - one
    split = poly_gcd(modulus, power, zero)
    roots, stack, shift = [], [split], 0
    while stack:
        poly = stack.pop()
        if len(poly) == 1:
            continue
        if len(poly) == 2:
            roots.append(zero - poly[0])
            continue
        # Equal-degree splitting: `(x + shift)^((size - 1) / 2) - 1` holds about half the roots.
        while True:
            shift += 1
            power, base, e = [one], [field(shift), one], (size - 1) // 2
            modulus_here = poly
            power = power + [zero] * (len(poly) - 2)
            base = base + [zero] * (len(poly) - 3) if len(poly) > 2 else base
            while e:
                if e & 1:
                    power = poly_mulmod(power, base, modulus_here, field)
                base = poly_mulmod(base, base, modulus_here, field)
                e >>= 1
            power[0] = power[0] - one
            part = poly_gcd(poly, power, zero)
            if 1 < len(part) < len(poly):
                break
        quotient, rest = [], list(poly)
        while len(rest) >= len(part):
            factor = rest[-1] / part[-1]
            quotient.insert(0, factor)
            at = len(rest) - len(part)
            rest = [x - factor * part[i - at] if i >= at else x for i, x in enumerate(rest)][:-1]
        stack += [part, quotient]
    return roots


def sqrt_fq2(a):
    """A square root in `Fp2`, or None, by the norm."""
    a0, a1 = (int(c) for c in a.coeffs)
    if a1 == 0:
        root = pow(a0, (P + 1) // 4, P)
        if root * root % P == a0:
            return bls.FQ2([root, 0])
        return bls.FQ2([0, pow(-a0 % P, (P + 1) // 4, P)])
    norm = (a0 * a0 + a1 * a1) % P
    s = pow(norm, (P + 1) // 4, P)
    if s * s % P != norm:
        return None
    for sign in (s, -s % P):
        half = (a0 + sign) * pow(2, -1, P) % P
        c = pow(half, (P + 1) // 4, P)
        if c * c % P == half and c != 0:
            return bls.FQ2([c, a1 * pow(2 * c, -1, P) % P])
    return None


def swu_inputs(curve):
    """The `u` whose point of `E'` has a zero denominator of the isogeny, as numbers."""
    if curve == "g1":
        a, b, z = constants.ISO_11_A, constants.ISO_11_B, constants.ISO_11_Z
        dens = constants.ISO_11_MAP_COEFFICIENTS
        field, size = bls.FQ, P

        def root(x):
            value = pow(int(x), (P + 1) // 4, P)
            return bls.FQ(value) if value * value % P == int(x) else None

    else:
        a, b, z = constants.ISO_3_A, constants.ISO_3_B, constants.ISO_3_Z
        dens = constants.ISO_3_MAP_COEFFICIENTS
        field, size, root = (lambda n: bls.FQ2([n, 0])), P * P, sqrt_fq2
    found = []
    for denominator in (dens[1], dens[3]):
        # py_ecc pads a list with zeros; the polynomial is made monic.
        poly = poly_trim([field(0) + c for c in denominator], field(0))
        for x in poly_roots([c / poly[-1] for c in poly], field, size):
            # `x = (-B / A) (1 + 1 / (t^2 + t))` for `t = Z u^2`, or `x = t x1` for the other.
            for second in (False, True):
                for u in swu_preimages(x, a, b, z, field, root, second):
                    if u not in found:
                        found.append(u)
    # A root of a denominator may be the abscissa of no point over the field: py_ecc decides.
    to_curve = h2c.map_to_curve_G1 if curve == "g1" else h2c.map_to_curve_G2
    return [u for u in found if bls.is_inf(to_curve(u))]


def swu_preimages(x, a, b, z, field, root, second):
    """The `u` that the simplified SWU map sends to the abscissa `x`, by `x1` or by `x2`."""
    one, out = field(1), []
    if not second:
        # `1 / (t^2 + t) = -x A / B - 1`.
        target = field(0) - x * a / b - one
        if target == field(0):
            return out
        ts = quadratic_roots(one, one, field(0) - one / target, field, root)
    else:
        # `x = t x1 = (-B / A) (t + 1 / (t + 1))`.
        # So `t^2 + (1 - w) t + (1 - w) = 0`, for `w = -x A / B`.
        w = field(0) - x * a / b
        ts = quadratic_roots(one, one - w, one - w, field, root)
    for t in ts:
        u = root(t / z)
        if u is not None:
            out += [u, field(0) - u]
    return out


def quadratic_roots(a, b, c, field, root):
    """The roots of `a t^2 + b t + c`."""
    disc = root(b * b - field(4) * a * c)
    if disc is None:
        return []
    half = field(1) / (field(2) * a)
    return [(field(0) - b + disc) * half, (field(0) - b - disc) * half]


def bn_twist(seed):
    """A point of the twist of alt_bn128 with `x = seed + k + i`, for the least `k` with one."""
    q = bn.field_modulus
    x = bn.FQ2([seed % q, 1])
    while True:
        rhs = x**3 + bn.b2
        a0, a1 = (int(c) for c in rhs.coeffs)
        norm = (a0 * a0 + a1 * a1) % q
        s = pow(norm, (q + 1) // 4, q)
        if s * s % q == norm:
            for sign in (s, -s % q):
                half = (a0 + sign) * pow(2, -1, q) % q
                c = pow(half, (q + 1) // 4, q)
                if c * c % q == half and c != 0:
                    y = bn.FQ2([c, a1 * pow(2 * c, -1, q) % q])
                    assert y * y == rhs, "not a root"
                    return curves_bls.show2((x, y, bn.FQ2.one()), bn)
        x = x + bn.FQ2.one()


def show(u):
    coeffs = getattr(u, "coeffs", None)
    return str(int(u)) if coeffs is None else ",".join(str(int(c)) for c in coeffs)


def answer(words):
    match words:
        case ["dsts"]:
            return f"{Pop.DST.hex()} {Pop.POP_TAG.hex()}"
        case ["h2g2any", msg, dst]:
            return curves_bls.show2(hash_to_g2(unhex(msg), unhex(dst)))
        case ["coresign", sk, msg, dst]:
            return core_sign(int(sk), unhex(msg), unhex(dst))
        case ["coreverify", pk, msg, sig, dst]:
            return core_verify(unhex(pk), unhex(msg), unhex(sig), unhex(dst))
        case ["coreaggverify", pks, msgs, sig, dst]:
            return curves_bls.guarded(
                lambda: G2Basic._CoreAggregateVerify(
                    curves_bls.items(pks), curves_bls.items(msgs), unhex(sig), short(unhex(dst))
                )
            )
        case ["derivechild", parent, index]:
            return str(curves_bls.derive_child(int(parent), int(index)))
        case ["g2real", y]:
            return g2_real(int(y))
        case ["heffg2", point]:
            return curves_bls.show2(bls.multiply(curves_bls.g2(point), H_EFF_G2))
        case ["bntwist", seed]:
            return bn_twist(int(seed))
        case ["swuroot", curve]:
            return " ".join(show(u) for u in swu_inputs(curve)) or "none"
        case ["sphincscodeword", digest]:
            code = unhex(digest)
            digits = [(code[i // 4] >> (6 - 2 * (i % 4))) & 3 for i in range(64)]
            return "".join(str(d) for d in digits) if sum(digits) == 128 else "none"
        case ["sphincsadrs", kind, layer, tree, key, word2, word3]:
            return curves_sphincs.adrs(
                int(kind), int(layer), int(tree), int(key), int(word2), int(word3)
            ).hex()
        case ["sphincskey", layer, index]:
            below, height, _ = curves_sphincs.LAYERS[int(layer)]
            idx = int(index)
            return f"{idx >> (below + height)} {(idx >> below) % 2**height}"
        case ["xmssaddress", tau, mu, hi, lo]:
            return curves_xmss.address(int(tau), int(mu), int(hi), int(lo)).hex()
    return None

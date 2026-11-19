"""BLS12-381 and alt_bn128 references: py_ecc, arkworks and milagro.

A point of G1 is `x,y` and a point of G2 is `x0,x1,y0,y1`, in decimal; `inf`
is the point at infinity.  A list is its items joined by `;`, or `[]`.
"""

import hashlib
import hmac

import milagro_bls_binding as milagro
import py_arkworks_bls12381 as ark
from py_ecc import optimized_bls12_381 as bls, optimized_bn128 as bn
from py_ecc.bls import G2ProofOfPossession as Pop, hash_to_curve as h2c, point_compression as pc
from py_ecc.bls.g2_primitives import (
    G1_to_pubkey,
    G2_to_signature,
    subgroup_check,
)

P = bls.field_modulus
R = bls.curve_order
G2_INFINITY = b"\xc0" + bytes(95)


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def items(word):
    return [] if word == "[]" else [unhex(item) for item in word.split(";")]


def g1(word, lib=bls):
    if word == "inf":
        return lib.Z1
    x, y = (int(c) for c in word.split(","))
    return (lib.FQ(x), lib.FQ(y), lib.FQ(1))


def g2(word, lib=bls):
    if word == "inf":
        return lib.Z2
    x0, x1, y0, y1 = (int(c) for c in word.split(","))
    return (lib.FQ2([x0, x1]), lib.FQ2([y0, y1]), lib.FQ2.one())


def show1(pt, lib=bls):
    if lib.is_inf(pt):
        return "inf"
    x, y = lib.normalize(pt)
    return f"{int(x)},{int(y)}"


def show2(pt, lib=bls):
    if lib.is_inf(pt):
        return "inf"
    x, y = lib.normalize(pt)
    return ",".join(str(int(c)) for c in (*x.coeffs, *y.coeffs))


def ark_show(pt, size):
    data = bytes(pt.to_xy_bytes_be())
    if pt == type(pt).identity():
        return "inf"
    return ",".join(str(int.from_bytes(data[i : i + 48], "big")) for i in range(0, 2 * size, 48))


def g1_decode(data):
    """Decompression of the Zcash encoding; no subgroup check."""
    try:
        other = show1(pc.decompress_G1(pc.G1Compressed(int.from_bytes(data, "big"))))
    except ValueError:
        other = "error"
    # arkworks reads any bytes under the infinity flag as infinity: py_ecc decides there.
    if data[0] & 0x40:
        return other
    try:
        mine = ark_show(ark.G1Point.from_compressed_bytes_unchecked(data), 48)
    except Exception:
        mine = "error"
    # py_ecc refuses x = 0 as an infinity without its flag: arkworks decides there.
    if int.from_bytes(data, "big") % 2**381 != 0:
        assert mine == other, f"arkworks {mine} and py_ecc {other} disagree"
    return mine


def g2_decode(data):
    z1 = int.from_bytes(data[:48], "big")
    z2 = int.from_bytes(data[48:], "big")
    try:
        other = show2(pc.decompress_G2(pc.G2Compressed((z1, z2))))
    except ValueError:
        other = "error"
    if data[0] & 0x40:
        return other
    try:
        mine = ark_show(ark.G2Point.from_compressed_bytes_unchecked(data), 96)
    except Exception:
        mine = "error"
    if z1 % 2**381 != 0 or z2 != 0:
        assert mine == other, f"arkworks {mine} and py_ecc {other} disagree"
    return mine


def ark1(word):
    if word == "inf":
        return ark.G1Point.identity()
    x, y = (int(c) for c in word.split(","))
    return ark.G1Point.from_xy_bytes_unchecked_be(x.to_bytes(48, "big") + y.to_bytes(48, "big"))


def ark2(word):
    if word == "inf":
        return ark.G2Point.identity()
    return ark.G2Point.from_xy_bytes_unchecked_be(
        b"".join(int(c).to_bytes(48, "big") for c in word.split(","))
    )


def in_subgroup(word, kind):
    if kind == 1:
        mine = ark1(word).is_in_subgroup()
        other = subgroup_check(g1(word))
    else:
        mine = ark2(word).is_in_subgroup()
        other = subgroup_check(g2(word))
    assert mine == other, "arkworks and py_ecc disagree"
    return str(int(mine))


def pairing_check(words):
    """Whether the product of the pairings is one; a pair with infinity gives one."""
    g1s = [ark1(w) for w in words[0::2]]
    g2s = [ark2(w) for w in words[1::2]]
    return str(int(ark.GT.multi_pairing(g1s, g2s) == ark.GT.one()))


def expand_message_xmd(msg, dst, length):
    """RFC 9380 section 5.3.1, with the long tag of section 5.3.3."""
    if length > 65535 or (length + 31) // 32 > 255:
        return None
    if len(dst) > 255:
        dst = hashlib.sha256(b"H2C-OVERSIZE-DST-" + dst).digest()
    dst_prime = dst + bytes([len(dst)])
    b0 = hashlib.sha256(bytes(64) + msg + length.to_bytes(2, "big") + b"\x00" + dst_prime).digest()
    blocks = [hashlib.sha256(b0 + b"\x01" + dst_prime).digest()]
    for i in range(2, (length + 31) // 32 + 1):
        mixed = bytes(a ^ b for a, b in zip(b0, blocks[-1], strict=True))
        blocks.append(hashlib.sha256(mixed + bytes([i]) + dst_prime).digest())
    out = b"".join(blocks)[:length]
    if len(dst) <= 255 and 0 < len(dst):
        assert out == h2c.expand_message_xmd(msg, dst, length, hashlib.sha256)
    return out


def hash_to_g2(msg, dst):
    if len(dst) > 255:
        dst = hashlib.sha256(b"H2C-OVERSIZE-DST-" + dst).digest()
    return show2(h2c.hash_to_G2(msg, dst, hashlib.sha256))


def map_fp(u):
    pt = h2c.clear_cofactor_G1(h2c.map_to_curve_G1(bls.FQ(u)))
    other = ark_show(ark.G1Point.map_from_fp_be(u.to_bytes(48, "big")), 48)
    assert show1(pt) == other, "py_ecc and arkworks disagree"
    return other


def map_fp2(u0, u1):
    pt = h2c.clear_cofactor_G2(h2c.map_to_curve_G2(bls.FQ2([u0, u1])))
    return show2(pt)


def guarded(run):
    """A boolean of a verification that may raise on malformed input."""
    try:
        return str(int(bool(run())))
    except Exception:
        return "0"


def verify(pk, msg, sig):
    mine = guarded(lambda: Pop.Verify(pk, msg, sig))
    other = guarded(lambda: milagro.Verify(pk, msg, sig))
    assert mine == other, f"py_ecc {mine} and milagro {other} disagree"
    return mine


def aggregate(sigs):
    try:
        return bytes(Pop.Aggregate(sigs)).hex()
    except Exception:
        return "error"


def fast_aggregate_verify(pks, msg, sig):
    mine = guarded(lambda: Pop.FastAggregateVerify(pks, msg, sig))
    other = guarded(lambda: milagro.FastAggregateVerify(pks, msg, sig))
    assert mine == other, f"py_ecc {mine} and milagro {other} disagree"
    return mine


def aggregate_verify(pks, msgs, sig):
    mine = guarded(lambda: Pop.AggregateVerify(pks, msgs, sig))
    other = guarded(lambda: milagro.AggregateVerify(pks, msgs, sig))
    assert mine == other, f"py_ecc {mine} and milagro {other} disagree"
    return mine


def eth_aggregate_pubkeys(pks):
    """consensus-specs, altair/bls.md: every key valid, and at least one."""
    if not pks or not all(Pop.KeyValidate(pk) for pk in pks):
        return "error"
    return bytes(Pop._AggregatePKs(pks)).hex()


def eth_fast_aggregate_verify(pks, msg, sig):
    """consensus-specs, altair/bls.md."""
    if not pks and sig == G2_INFINITY:
        return "1"
    return fast_aggregate_verify(pks, msg, sig)


def hkdf_extract(salt, ikm):
    return hmac.new(salt, ikm, hashlib.sha256).digest()


def hkdf_expand(prk, info, length):
    out, block, i = b"", b"", 1
    while len(out) < length:
        block = hmac.new(prk, block + info + bytes([i]), hashlib.sha256).digest()
        out += block
        i += 1
    return out[:length]


def hkdf_mod_r(ikm, key_info=b""):
    """ERC-2333 `HKDF_mod_r`, which is KeyGen of the BLS signature draft, version 4."""
    salt = b"BLS-SIG-KEYGEN-SALT-"
    sk = 0
    while sk == 0:
        salt = hashlib.sha256(salt).digest()
        prk = hkdf_extract(salt, ikm + b"\x00")
        okm = hkdf_expand(prk, key_info + (48).to_bytes(2, "big"), 48)
        sk = int.from_bytes(okm, "big") % R
    return sk


def key_gen(ikm, key_info):
    if len(ikm) < 32:
        return "error"
    sk = hkdf_mod_r(ikm, key_info)
    assert sk == Pop.KeyGen(ikm, key_info), "py_ecc and the model disagree"
    return str(sk)


def lamport_sk(ikm, salt):
    okm = hkdf_expand(hkdf_extract(salt, ikm), b"", 255 * 32)
    return [okm[i : i + 32] for i in range(0, 255 * 32, 32)]


def derive_child(parent, index):
    """ERC-2333 `derive_child_SK`."""
    salt = index.to_bytes(4, "big")
    ikm = parent.to_bytes(32, "big")
    not_ikm = bytes(b ^ 0xFF for b in ikm)
    chunks = lamport_sk(ikm, salt) + lamport_sk(not_ikm, salt)
    pk = hashlib.sha256(b"".join(hashlib.sha256(c).digest() for c in chunks)).digest()
    return hkdf_mod_r(pk)


def derive_path(seed, indices):
    if len(seed) < 32:
        return "error"
    sk = hkdf_mod_r(seed)
    for index in indices:
        sk = derive_child(sk, index)
    return str(sk)


def fq12(value):
    return " ".join(str(int(c)) for c in value.coeffs)


def bn_pairing(p, q):
    """The pairing of alt_bn128, as twelve coefficients of powers of `w`."""
    return fq12(bn.pairing(g2(q, bn), g1(p, bn)))


def bn_pairing_check(words):
    product = bn.FQ12.one()
    for p, q in zip(words[0::2], words[1::2], strict=True):
        if p == "inf" or q == "inf":
            continue
        product *= bn.pairing(g2(q, bn), g1(p, bn), final_exponentiate=False)
    return str(int(bn.final_exponentiate(product) == bn.FQ12.one()))


def answer(words):
    match words:
        case ["g1dec", data]:
            return g1_decode(unhex(data))
        case ["g2dec", data]:
            return g2_decode(unhex(data))
        case ["g1enc", p]:
            return bytes(G1_to_pubkey(g1(p))).hex()
        case ["g2enc", p]:
            return bytes(G2_to_signature(g2(p))).hex()
        case ["g1sub", p]:
            return in_subgroup(p, 1)
        case ["g2sub", p]:
            return in_subgroup(p, 2)
        case ["g1add", p, q]:
            return show1(bls.add(g1(p), g1(q)))
        case ["g1mul", k, p]:
            return show1(bls.multiply(g1(p), int(k)))
        case ["g2add", p, q]:
            return show2(bls.add(g2(p), g2(q)))
        case ["g2mul", k, p]:
            return show2(bls.multiply(g2(p), int(k)))
        case ["keyvalidate", pk]:
            return str(int(Pop.KeyValidate(unhex(pk))))
        case ["blspairing", *pairs]:
            return pairing_check(pairs)
        case ["expand", msg, dst, length]:
            out = expand_message_xmd(unhex(msg), unhex(dst), int(length))
            return "error" if out is None else (out.hex() or "-")
        case ["h2g2", msg, dst]:
            return hash_to_g2(unhex(msg), unhex(dst))
        case ["mapfp", u]:
            return map_fp(int(u))
        case ["mapfp2", u0, u1]:
            return map_fp2(int(u0), int(u1))
        case ["sktopk", sk]:
            return bytes(Pop.SkToPk(int(sk))).hex()
        case ["blssign", sk, msg]:
            sig = Pop.Sign(int(sk), unhex(msg))
            assert sig == milagro.Sign(int(sk).to_bytes(32, "big"), unhex(msg))
            return bytes(sig).hex()
        case ["popprove", sk]:
            return bytes(Pop.PopProve(int(sk))).hex()
        case ["popverify", pk, proof]:
            return guarded(lambda: Pop.PopVerify(unhex(pk), unhex(proof)))
        case ["blsverify", pk, msg, sig]:
            return verify(unhex(pk), unhex(msg), unhex(sig))
        case ["aggregate", sigs]:
            return aggregate(items(sigs))
        case ["fastaggverify", pks, msg, sig]:
            return fast_aggregate_verify(items(pks), unhex(msg), unhex(sig))
        case ["aggverify", pks, msgs, sig]:
            return aggregate_verify(items(pks), items(msgs), unhex(sig))
        case ["ethaggpk", pks]:
            return eth_aggregate_pubkeys(items(pks))
        case ["ethfastaggverify", pks, msg, sig]:
            return eth_fast_aggregate_verify(items(pks), unhex(msg), unhex(sig))
        case ["keygen", ikm, info]:
            return key_gen(unhex(ikm), unhex(info))
        case ["derivepath", seed, *indices]:
            return derive_path(unhex(seed), [int(i) for i in indices])
        case ["bng2add", p, q]:
            return show2(bn.add(g2(p, bn), g2(q, bn)), bn)
        case ["bng2mul", k, p]:
            return show2(bn.multiply(g2(p, bn), int(k)), bn)
        case ["bnpairing", p, q]:
            return bn_pairing(p, q)
        case ["bnpairingcheck", *pairs]:
            return bn_pairing_check(pairs)
    return None

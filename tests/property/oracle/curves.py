"""References for the public-key layer: one command per line, one answer per line."""

# Words are separated by tabs.
# Integers are decimal, bytes are hexadecimal (`-` for none), and a point is `x,y` or `inf`.
# An answer of `error` says the reference refused the input.
# The commands are the cases of `answer` below, and of the modules it asks in turn.

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import coincurve  # noqa: E402
import curves_bls  # noqa: E402
import curves_extra  # noqa: E402
import curves_kzg  # noqa: E402
import curves_model as model  # noqa: E402
import curves_sphincs  # noqa: E402
import curves_xmss  # noqa: E402
from cryptography.exceptions import InvalidSignature  # noqa: E402
from cryptography.hazmat.primitives import hashes  # noqa: E402
from cryptography.hazmat.primitives.asymmetric import ec, utils  # noqa: E402
from curves_model import BN, K1, R1  # noqa: E402
from eth_keys import keys  # noqa: E402

CURVES = {"k1": K1, "r1": R1, "bn": BN}


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return data.hex() if data else "-"


def point(word):
    if word == "inf":
        return None
    x, y = word.split(",")
    return (int(x), int(y))


def show(pt):
    return "inf" if pt is None else f"{pt[0]},{pt[1]}"


def b32(n):
    return n.to_bytes(32, "big")


def k1_sign(d, h1):
    """The low-s signature and recovery bit; libsecp256k1 must agree."""
    if not 1 <= d < K1.n:
        return "error"
    signed = model.sign(K1, d, h1)
    if signed is None or signed[2][0] >= K1.n:
        return "error"
    r, s, big_r = signed
    odd = big_r[1] & 1
    if s > K1.n // 2:
        s, odd = K1.n - s, odd ^ 1
    sig = coincurve.PrivateKey(b32(d)).sign_recoverable(h1, hasher=None)
    assert sig == b32(r) + b32(s) + bytes([odd]), "coincurve and the model disagree"
    return f"{r} {s} {odd}"


def k1_verify(q, h1, r, s):
    e = int.from_bytes(h1, "big")
    ok = model.verify(K1, q, e, r, s)
    # The library verifies low-s signatures only, and takes r and s below n.
    if q is not None and model.on_curve(K1, q) and r < K1.n and 0 < s <= K1.n // 2:
        key = coincurve.PublicKey(b"\x04" + b32(q[0]) + b32(q[1]))
        der = utils.encode_dss_signature(r, s)
        lib = r > 0 and key.verify(der, h1, hasher=None)
        assert lib == ok, "coincurve and the model disagree"
    return str(int(ok))


def k1_recover(h1, r, s, v):
    q = model.recover(K1, int.from_bytes(h1, "big"), r, s, v)
    try:
        if not (r < 2**256 and s < 2**256):
            raise ValueError
        sig = b32(r) + b32(s) + bytes([v])
        lib = coincurve.PublicKey.from_signature_and_message(sig, h1, hasher=None)
        lib = lib.format(compressed=False)[1:]
        eth = keys.Signature(vrs=(v, r, s)).recover_public_key_from_msg_hash(h1)
        assert eth.to_bytes() == lib, "coincurve and eth_keys disagree"
    except AssertionError:
        raise
    except Exception:
        lib = None
    mine = None if q is None else b32(q[0]) + b32(q[1])
    assert lib == mine, "coincurve and the model disagree"
    return "error" if q is None else show(q)


def k1_decode(data):
    """SEC 1 v2 section 2.3.4 for a public key: compressed or uncompressed only."""
    if len(data) not in (33, 65) or data[0] not in (2, 3, 4):
        return "error"
    if (len(data) == 33) != (data[0] in (2, 3)):
        return "error"
    try:
        key = coincurve.PublicKey(data)
    except ValueError:
        return "error"
    x, y = key.point()
    return f"{x},{y}"


def craft(c, u1, u2, x):
    """A valid signature whose R has x >= n, so that r = x - n: key, e, r, s."""
    r = x % (c.p - c.n)
    while True:
        big_r = model.lift_x(c, r + c.n, 0)
        if big_r is not None and r > 0:
            break
        r = (r + 1) % (c.p - c.n)
    u1 = u1 % (c.n - 1) + 1
    u2 = u2 % (c.n - 1) + 1
    q = model.mul(c, pow(u2, -1, c.n), model.add(c, big_r, model.neg(c, model.mul(c, u1, c.g))))
    s = r * pow(u2, -1, c.n) % c.n
    e = u1 * s % c.n
    return f"{show(q)} {e} {r} {s}"


def k1_address(q):
    return keys.PublicKey(b32(q[0]) + b32(q[1])).to_canonical_address().hex()


def r1_verify(q, h1, r, s):
    ok = model.verify(R1, q, int.from_bytes(h1, "big"), r, s)
    lib = False
    try:
        key = ec.EllipticCurvePublicNumbers(q[0], q[1], ec.SECP256R1()).public_key()
        key.verify(utils.encode_dss_signature(r, s), h1, ec.ECDSA(utils.Prehashed(hashes.SHA256())))
        lib = True
    except (InvalidSignature, ValueError, TypeError):
        pass
    assert lib == ok, "cryptography and the model disagree"
    return str(int(ok))


def r1_sign(d, h1):
    if not 1 <= d < R1.n:
        return "error"
    signed = model.sign(R1, d, h1)
    if signed is None:
        return "error"
    r, s, _ = signed
    # The library reduces the hash as RFC 6979 does, so it is a second reference everywhere.
    key = ec.derive_private_key(d, ec.SECP256R1())
    algorithm = ec.ECDSA(utils.Prehashed(hashes.SHA256()), deterministic_signing=True)
    lib = utils.decode_dss_signature(key.sign(h1, algorithm))
    assert lib == (r, s), "cryptography and the model disagree"
    return f"{r} {s}"


def r1_decode(data):
    try:
        key = ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256R1(), data)
    except (ValueError, TypeError):
        return "error"
    if not data or data[0] != 4:
        return "error"
    numbers = key.public_numbers()
    return f"{numbers.x},{numbers.y}"


def answer(words):
    match words:
        case ["add", c, p, q]:
            return show(model.add(CURVES[c], point(p), point(q)))
        case ["mul", c, k, p]:
            return show(model.mul(CURVES[c], int(k), point(p)))
        case ["muladd", c, k, p, l, q]:
            c = CURVES[c]
            return show(
                model.add(c, model.mul(c, int(k), point(p)), model.mul(c, int(l), point(q)))
            )
        case ["nonces", c, x, h1, ops]:
            # One candidate per `n`, after the rejections that the `r`s before it ask for.
            # The order is that of a named curve, or any number of 256 bits.
            order = CURVES[c].n if c in CURVES else int(c)
            gen = model.nonces(order, int(x), unhex(h1))
            return " ".join(str(next(gen)) for op in ops if op == "n") or "-"
        case ["k1sign", d, h1]:
            return k1_sign(int(d), unhex(h1))
        case ["k1verify", q, h1, r, s]:
            return k1_verify(point(q), unhex(h1), int(r), int(s))
        case ["k1recover", h1, r, s, v]:
            return k1_recover(unhex(h1), int(r), int(s), int(v))
        case ["k1decode", data]:
            return k1_decode(unhex(data))
        case ["k1craft", u1, u2, x]:
            return craft(K1, int(u1), int(u2), int(x))
        case ["r1craft", u1, u2, x]:
            return craft(R1, int(u1), int(u2), int(x))
        case ["k1address", q]:
            return k1_address(point(q))
        case ["r1verify", q, h1, r, s]:
            return r1_verify(point(q), unhex(h1), int(r), int(s))
        case ["r1sign", d, h1]:
            return r1_sign(int(d), unhex(h1))
        case ["r1decode", data]:
            return r1_decode(unhex(data))
    return (
        curves_bls.answer(words)
        or curves_kzg.answer(words)
        or curves_xmss.answer(words)
        or curves_sphincs.answer(words)
        or curves_extra.answer(words)
        or "error unknown command"
    )


if __name__ == "__main__":
    for line in sys.stdin:
        try:
            out = answer(line.rstrip("\n").split("\t"))
        except AssertionError as failure:
            out = f"references disagree: {failure}"
        print(out or "-", flush=True)

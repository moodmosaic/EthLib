"""Real BLS for the consensus oracle: signatures by the secret keys of the test validators."""

# `consensus_ops.py` gives validator `n` the public key of the secret key `n + 1`.
# It makes a signature through `signed`.
# This module replaces `signed` while a case asks for real signatures.
#
# A signature that a case wants wrong is wrong in one of several ways, chosen by a counter.
# This is so that a check which only tells a point from garbage does not pass:
#
#     0  bytes that are no point
#     1  a signature by another key
#     2  a signature under another domain
#     3  the point at infinity
#     4  a signature of the object root, without the domain
#
# Key seeds from 900 on are public keys that no secret key has:
#
# - The point at infinity.
# - An x coordinate off the curve.
# - A point outside the subgroup.
# - Bytes without the compression bit.

from eth_consensus_specs.utils import bls

G2_INFINITY = b"\xc0" + bytes(95)
VERIFY = bls.Verify
FAST_AGGREGATE_VERIFY = bls.FastAggregateVerify
SECRET = {}
SIGNED = {}
WRONG = [0]
# `consensus.py` puts the stand-in in place when it is imported.
STATE = {"mode": "standin"}

# A point of the curve outside the subgroup of prime order, compressed.
# Here x = 4 is on the curve `y^2 = x^3 + 4` only if 68 is a square.
# So the encoding is found by search at import.
OFF_CURVE = bytes([0x80]) + bytes(46) + bytes([0x01])


def outside_subgroup():
    """A compressed point of the curve that the subgroup check refuses, by search."""
    from py_ecc.bls.point_compression import decompress_G1
    from py_ecc.bls.typing import G1Compressed
    from py_ecc.optimized_bls12_381 import curve_order, is_inf, multiply

    for x in range(1, 200):
        candidate = (0x80 << 376) | x
        try:
            point = decompress_G1(G1Compressed(candidate))
        except Exception:
            continue
        if not is_inf(multiply(point, curve_order)):
            return candidate.to_bytes(48, "big")
    raise ValueError("no point outside the subgroup found")


BAD_KEYS = {}


def bad_key(seed):
    """A public key that is not valid, by its seed from 900 on."""
    if not BAD_KEYS:
        BAD_KEYS[0] = b"\xc0" + bytes(47)
        BAD_KEYS[1] = OFF_CURVE
        BAD_KEYS[2] = outside_subgroup()
        BAD_KEYS[3] = bytes(48)
    return BAD_KEYS[(seed - 900) % len(BAD_KEYS)]


def use(mode, ops, base, stand_in):
    """Put the signatures of a mode in force: `standin`, `real`, or `off` for the fork choice.

    With `off` the checks of consensus-specs are in place and switched off, as its tests run.
    """
    if mode == STATE["mode"]:
        return
    STATE["mode"] = mode
    bls.bls_active = mode != "off"
    if mode == "standin":
        bls.Verify = base.fake_verify
        bls.FastAggregateVerify = base.fake_fast_aggregate_verify
    else:
        bls.Verify = VERIFY
        bls.FastAggregateVerify = FAST_AGGREGATE_VERIFY
    if mode != "real":
        ops.pubkey = stand_in["pubkey"]
        base.pubkey = stand_in["pubkey"]
        ops.fake_signature = stand_in["fake_signature"]
        base.fake_signature = stand_in["fake_signature"]
        ops.signed = stand_in["signed"]
        ops.sync_participant_keys = stand_in["sync_participant_keys"]
        return
    stand_in_pubkey = stand_in["pubkey"]

    def pubkey(seed):
        if 900 <= seed < 1000:
            return bad_key(seed)
        key = stand_in_pubkey(seed)
        SECRET[bytes(key)] = seed + 1
        return key

    def signature(pubkeys, message):
        """The aggregate signature of the keys over a message; a stranger's key signs garbage."""
        message = bytes(message)
        parts = []
        for key in pubkeys:
            secret = SECRET.get(bytes(key))
            if secret is None:
                return b"\x09" * 96
            if (secret, message) not in SIGNED:
                SIGNED[secret, message] = bls.Sign(secret, message)
            parts.append(SIGNED[secret, message])
        if not parts:
            return G2_INFINITY
        return bytes(bls.Aggregate(parts))

    def signed(spec, keys, message, domain, ok):
        if ok:
            return signature(keys, spec.compute_signing_root(message, domain))
        WRONG[0] += 1
        kind = WRONG[0] % 5
        if kind == 1:
            return signature([pubkey(777)], spec.compute_signing_root(message, domain))
        if kind == 2:
            other = bytes(domain)[:4] + bytes(b ^ 0xFF for b in bytes(domain)[4:])
            return signature(keys, spec.compute_signing_root(message, spec.Domain(other)))
        if kind == 3:
            return G2_INFINITY
        if kind == 4:
            return signature(keys, spec.hash_tree_root(message))
        return b"\x09" * 96

    ops.pubkey = pubkey
    base.pubkey = pubkey
    ops.fake_signature = signature
    base.fake_signature = signature
    ops.signed = signed
    # The secret keys of the members sign, whatever sum of keys the fork then checks against.
    ops.sync_participant_keys = lambda spec, state, bits, keys: keys
    # The keys made before this case have a secret key too.
    for seed, key in list(ops.KEYS.items()):
        SECRET[bytes(key)] = seed + 1

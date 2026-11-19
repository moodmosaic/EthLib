"""A model of leanXMSS, written from the formulas of the specification draft.

    Th(P, A, M) = H_0(P | A | M), with H = Keccak-256 and H_0 its first half.

The model verifies, signs with one one-time key, and computes small subtrees.
Key generation and full signing build 2^16 one-time keys and are left out.
"""

import os
import re

from Crypto.Hash import keccak

HERE = os.path.dirname(os.path.abspath(__file__))
VECTORS = os.path.join(HERE, "../../cryptography/xmss")

V = 58
TARGET_SUM = 106
HEIGHT = 16
PRF, CHAIN, LEAF, NODE, PARAM, RND, MSG = 0, 1, 2, 3, 5, 7, 12


def h(data):
    return keccak.new(digest_bits=256, data=data).digest()


def address(tau, mu, hi, lo):
    """`enc(tau, mu, hi, lo)`: lo in 4 bytes, hi in 3, the type byte, 8 zeros."""
    return lo.to_bytes(4, "little") + hi.to_bytes(3, "little") + bytes([tau + 32 * mu]) + bytes(8)


def hi(layer, a):
    return a + 2**23 * layer


def th(pp, addr, payload):
    return h(pp + addr + payload)[:16]


def digits(digest):
    value = int.from_bytes(digest, "little")
    return [(value >> (2 * i)) & 3 for i in range(64)]


def codeword(digest):
    x = digits(digest)
    if any(x[V:]) or sum(x[:V]) != TARGET_SUM:
        return None
    return x[:V]


def message_digest(pp, layer, e, msg, rho):
    return th(pp, address(MSG, 0, hi(layer, 0), e), msg + rho)


def walk(pp, layer, e, i, start, steps, value):
    for mu in range(start, start + steps):
        value = th(pp, address(CHAIN, mu, hi(layer, 0), e), value + i.to_bytes(16, "little"))
    return value


def leaf_hash(pp, layer, e, ends):
    return th(pp, address(LEAF, 0, hi(layer, 0), e), b"".join(ends))


def ots_leaf(pp, layer, e, msg, rho, y):
    x = codeword(message_digest(pp, layer, e, msg, rho))
    if x is None:
        return None
    return leaf_hash(pp, layer, e, [walk(pp, layer, e, i, x[i], 3 - x[i], y[i]) for i in range(V)])


def node_hash(pp, layer, level, j, left, right):
    return th(pp, address(NODE, 0, hi(layer, level % 17), j % 2**32), left + right)


def fold(pp, layer, e, leaf, path):
    value, index = leaf, e
    for level, sibling in enumerate(path):
        pair = (value, sibling) if index % 2 == 0 else (sibling, value)
        index //= 2
        value = node_hash(pp, layer, level + 1, index, *pair)
    return value


def split_layer(data):
    rho = data[:16]
    y = [data[16 + 16 * i : 32 + 16 * i] for i in range(V)]
    rest = data[16 + 16 * V :]
    return rho, y, [rest[16 * i : 16 * i + 16] for i in range(HEIGHT)]


def layer_root(pp, layer, e, msg, data):
    rho, y, path = split_layer(data)
    leaf = ots_leaf(pp, layer, e, msg, rho, y)
    return None if leaf is None else fold(pp, layer, e, leaf, path)


def verify(pk, msg, sig):
    """`Ver(pk, m, sigma)`: `1`, `0`, or `error` for a wrong length."""
    if len(pk) != 32 or len(msg) != 32 or len(sig) != 2404:
        return "error"
    root, pp = pk[:16], pk[16:]
    index = int.from_bytes(sig[:4], "little")
    bottom = layer_root(pp, 0, index, msg, sig[4:1204])
    if bottom is None:
        return "0"
    top = layer_root(pp, 1, index >> 16, bottom, sig[1204:])
    return str(int(top == root))


class Signer:
    """The derivations from a seed `S_0`."""

    def __init__(self, seed):
        self.s = h(b"leanXMSS" + seed)
        self.pp = h(bytes(16) + address(PARAM, 0, 0, 0) + self.s)[:16]

    def prf(self, addr, suffix=b""):
        return h(self.pp + addr + self.s + suffix)

    def starts(self, layer, e):
        pairs = [self.prf(address(PRF, 0, hi(layer, j), e)) for j in range(V // 2)]
        return [pairs[i // 2][16 * (i % 2) : 16 * (i % 2) + 16] for i in range(V)]

    def public_leaf(self, layer, e):
        ends = [walk(self.pp, layer, e, i, 0, 3, c) for i, c in enumerate(self.starts(layer, e))]
        return leaf_hash(self.pp, layer, e, ends)

    def node(self, layer, level, j):
        if level == 0:
            return self.public_leaf(layer, j)
        left = self.node(layer, level - 1, 2 * j)
        right = self.node(layer, level - 1, 2 * j + 1)
        return node_hash(self.pp, layer, level, j, left, right)

    def ots_sign(self, layer, e, msg, start, fuel):
        """The first randomizer trial from `start` that gives a codeword, and the chain values."""
        base = int.from_bytes(self.prf(address(RND, 0, hi(layer, 0), e), msg)[:16], "little")
        for c in range(start, start + fuel):
            rho = ((base + c) % 2**128).to_bytes(16, "little")
            x = codeword(message_digest(self.pp, layer, e, msg, rho))
            if x is not None:
                starts = self.starts(layer, e)
                y = [walk(self.pp, layer, e, i, 0, x[i], starts[i]) for i in range(V)]
                return c, rho, y
        return None


def vector(name):
    """The public key, the message and the signature of a `verify` vector."""
    with open(os.path.join(VECTORS, "verify", name, "data.yaml")) as source:
        text = source.read()
    fields = [
        re.search(rf"{key}: '0x([0-9a-f]*)'", text)
        for key in ("public_key", "message", "signature")
    ]
    return " ".join(field.group(1) for field in fields)


def vrf_climb(index, secret, path):
    """The root that an opening of the VRF tree leads to, by the bits of the index."""
    value = h(b"PQ_VRF_LEAF" + secret)
    for sibling in path:
        pair = value + sibling if index % 2 == 0 else sibling + value
        value = h(b"PQ_VRF_NODE" + pair)
        index //= 2
    return value


def vrf_verify(root, index, opening):
    """`vrf.Verify` of EIP-8450: the output at the index, or `none`."""
    if len(root) != 32 or len(opening) != 1056 or not 0 <= index < 2**32:
        return "none"
    secret = opening[:32]
    path = [opening[32 + 32 * i : 64 + 32 * i] for i in range(32)]
    if vrf_climb(index, secret, path) != root:
        return "none"
    return h(b"PQ_VRF_OUTPUT" + index.to_bytes(4, "little") + secret).hex()


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def answer(words):
    match words:
        case ["xmssvector", name]:
            return vector(name)
        case ["xmssverify", pk, msg, sig]:
            return verify(unhex(pk), unhex(msg), unhex(sig))
        case ["xmsscodeword", digest]:
            x = codeword(unhex(digest))
            return "none" if x is None else "".join(str(d) for d in x)
        case ["xmssfold", pp, layer, e, leaf, path]:
            path = unhex(path)
            siblings = [path[i : i + 16] for i in range(0, len(path), 16)]
            return fold(unhex(pp), int(layer), int(e), unhex(leaf), siblings).hex()
        case ["xmssotsleaf", pp, layer, e, msg, rho, y]:
            y = unhex(y)
            chains = [y[i : i + 16] for i in range(0, len(y), 16)]
            leaf = ots_leaf(unhex(pp), int(layer), int(e), unhex(msg), unhex(rho), chains)
            return "none" if leaf is None else leaf.hex()
        case ["xmsskey", seed, layer, level, j]:
            signer = Signer(unhex(seed))
            return f"{signer.pp.hex()} {signer.node(int(layer), int(level), int(j)).hex()}"
        case ["xmssots", seed, layer, e, msg]:
            signer = Signer(unhex(seed))
            signed = signer.ots_sign(int(layer), int(e), unhex(msg), 0, 2**32)
            return f"{signed[1].hex()} {b''.join(signed[2]).hex()}"
        case ["vrfroot", index, opening]:
            data = unhex(opening)
            path = [data[32 + 32 * i : 64 + 32 * i] for i in range(32)]
            return vrf_climb(int(index), data[:32], path).hex()
        case ["vrfverify", root, index, opening]:
            return vrf_verify(unhex(root), int(index), unhex(opening))
        case ["vrfsecret", seed, index]:
            secret = h(b"PQ_VRF_SECRET" + unhex(seed) + int(index).to_bytes(4, "little"))
            output = h(b"PQ_VRF_OUTPUT" + int(index).to_bytes(4, "little") + secret)
            return f"{secret.hex()} {output.hex()}"
        case ["vrfmix", output, randomness]:
            return h(b"PQ_VRF_MIX" + unhex(output) + unhex(randomness)).hex()
    return None

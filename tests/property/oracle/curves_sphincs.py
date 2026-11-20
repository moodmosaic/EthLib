"""A model of leanSPHINCS verification, written from FIPS 205 and the scheme's formulas."""

#     Th(PK.seed, ADRS, M) = Trunc_16(Keccak-256(PK.seed | ADRS | M))
#
# An address is eight big-endian 32-bit words.
# They are the layer, the tree (three words), the type, the key pair and two that the type names.

from Crypto.Hash import keccak

WOTS_HASH, WOTS_PK, TREE, FORS_TREE, FORS_ROOTS, WOTS_ENC = 0, 1, 2, 3, 4, 7
LAYERS = [(0, 8, 4240), (8, 8, 5396), (16, 10, 6552)]


def h(data):
    return keccak.new(digest_bits=256, data=data).digest()


def adrs(kind, layer, tree, key_pair, word2, word3):
    words = (layer, kind, key_pair, word2, word3)
    layer, kind, key_pair, word2, word3 = (w % 2**32 for w in words)
    return (
        layer.to_bytes(4, "big")
        + (tree % 2**64).to_bytes(12, "big")
        + b"".join(w.to_bytes(4, "big") for w in (kind, key_pair, word2, word3))
    )


def th(seed, address, payload):
    return h(seed + address + payload)[:16]


def climb(node, index, path, parent):
    """Fold a path from the leaf up; `parent(z, j, left, right)` hashes node `j` at height `z`."""
    for z, sibling in enumerate(path, start=1):
        pair = (node, sibling) if index % 2 == 0 else (sibling, node)
        index //= 2
        node = parent(z, index, *pair)
    return node


def chunks(data, size):
    return [data[i : i + size] for i in range(0, len(data), size)]


def verify(pk, msg, sig):
    """`slh_verify_internal` with WOTS+C: `1`, `0`, or `error` for a wrong length."""
    if len(pk) != 32 or len(msg) != 32 or len(sig) != 7740:
        return "error"
    seed, root = pk[:16], pk[16:]
    z = sig[:16] + seed + root + msg
    digest = (h(z + bytes(4)) + h(z + b"\x00\x00\x00\x01"))[:34]
    md = int.from_bytes(digest[:30], "big")
    picks = [(md >> (10 * (23 - k))) & 1023 for k in range(24)]
    idx = (int.from_bytes(digest[30:33], "big") % 2**18) * 256 + digest[33]
    tree, leaf = idx >> 8, idx & 255
    roots = []
    for kappa, opening in enumerate(chunks(sig[16:4240], 176)):
        s = picks[kappa]
        node = th(seed, adrs(FORS_TREE, 0, tree, leaf, 0, kappa * 1024 + s), opening[:16])

        def parent(height, j, left, right, kappa=kappa):
            where = adrs(FORS_TREE, 0, tree, leaf, height, kappa * 2 ** (10 - height) + j)
            return th(seed, where, left + right)

        roots.append(climb(node, s, chunks(opening[16:], 16), parent))
    message = th(seed, adrs(FORS_ROOTS, 0, tree, leaf, 0, 0), b"".join(roots))
    for layer, (below, height, offset) in enumerate(LAYERS):
        tree, leaf = idx >> (below + height), (idx >> below) % 2**height
        part = sig[offset : offset + 4 + 16 * (64 + height)]
        code = th(seed, adrs(WOTS_ENC, layer, tree, leaf, 0, 0), message + part[:4])
        digits = [(code[i // 4] >> (6 - 2 * (i % 4))) & 3 for i in range(64)]
        if sum(digits) != 128:
            return "0"
        ends = []
        for i, value in enumerate(chunks(part[4:1028], 16)):
            for mu in range(digits[i], 3):
                value = th(seed, adrs(WOTS_HASH, layer, tree, leaf, i, mu), value)
            ends.append(value)
        node = th(seed, adrs(WOTS_PK, layer, tree, leaf, 0, 0), b"".join(ends))

        def parent(height, j, left, right, layer=layer, tree=tree):
            return th(seed, adrs(TREE, layer, tree, 0, height, j), left + right)

        message = climb(node, leaf, chunks(part[1028:], 16), parent)
    return str(int(message == root))


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def answer(words):
    match words:
        case ["sphincsverify", pk, msg, sig]:
            return verify(unhex(pk), unhex(msg), unhex(sig))
    return None

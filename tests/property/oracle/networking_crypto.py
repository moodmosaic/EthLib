"""References that need secp256k1, Keccak or AES: ENR, discv4, discv5, RLPx, libp2p."""

# enr_make <sk> <seq> <k:v,...>   A signed "v4" record of EIP-778, RLP bytes.
# enr_read <hex>                  seq, node ID and whether the signature verifies.
# discv4_make <sk> <type> <data>  A discv4 packet around RLP data.
# discv4_read <hex>               sender, hash, type and the fields of its type.
# libp2p_verify <key> <msg> <sig> Whether libsecp256k1 takes the DER signature.
# libp2p_sign <sk> <msg>          The DER signature, RFC 6979, low s.

import coincurve
from Crypto.Hash import keccak
from networking_util import tohex, unhex

import rlp


class MalformedError(Exception):
    pass


def keccak256(data):
    return keccak.new(digest_bits=256, data=data).digest()


def scalar(value):
    """A canonical RLP integer: no leading zero byte."""
    if not isinstance(value, bytes) or value[:1] == b"\x00":
        raise MalformedError("not a scalar")
    return int.from_bytes(value, "big")


def sign64(sk, digest):
    """r || s, deterministic by RFC 6979, with a low s."""
    key = coincurve.PrivateKey(sk)
    return key.sign_recoverable(digest, hasher=None)


def enr_make(sk, seq, pairs):
    sk = unhex(sk)
    public = coincurve.PrivateKey(sk).public_key.format(compressed=True)
    entries = {b"id": b"v4", b"secp256k1": public}
    for pair in pairs.split(","):
        if pair:
            key, value = pair.split(":")
            entries[unhex(key)] = unhex(value)
    content = [int(seq)]
    for key in sorted(entries):
        content += [key, entries[key]]
    signature = sign64(sk, keccak256(rlp.encode(content)))[:64]
    record = rlp.encode([signature] + content)
    if len(record) > 300:
        raise MalformedError("too large")
    return tohex(record)


def enr_read(word):
    """A record as EIP-778 defines it, with the "v4" scheme."""
    data = unhex(word)
    if len(data) > 300:
        raise MalformedError("too large")
    items = rlp.decode(data, strict=True)
    if not isinstance(items, list) or len(items) < 2 or len(items) % 2 != 0:
        raise MalformedError("not a record")
    signature, seq = items[0], scalar(items[1])
    if not isinstance(signature, bytes) or seq >= 2**64:
        raise MalformedError("signature or seq")
    keys = items[2::2]
    if any(not isinstance(k, bytes) for k in keys):
        raise MalformedError("key")
    if any(a >= b for a, b in zip(keys, keys[1:], strict=False)):
        raise MalformedError("keys not sorted and unique")
    entries = dict(zip(keys, items[3::2], strict=False))
    if b"id" not in entries:
        raise MalformedError("no id")
    node_id, verified = "-", False
    key = entries.get(b"secp256k1")
    if entries[b"id"] == b"v4" and isinstance(key, bytes) and len(key) == 33:
        try:
            public = coincurve.PublicKey(key)
        except ValueError:
            public = None
        if public is not None:
            node_id = keccak256(public.format(compressed=False)[1:]).hex()
            digest = keccak256(rlp.encode(items[1:]))
            verified = len(signature) == 64 and verify64(public, digest, signature)
    return f"{seq} {node_id} {int(verified)}"


N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def verify64(public, digest, signature):
    """ECDSA verification of r || s, with a high s accepted as the EIP sets no rule."""
    r = int.from_bytes(signature[:32], "big")
    s = int.from_bytes(signature[32:], "big")
    if not (0 < r < N and 0 < s < N):
        return False
    if s > N // 2:
        s = N - s
    compact = r.to_bytes(32, "big") + s.to_bytes(32, "big")
    der = coincurve.ecdsa.cdata_to_der(coincurve.ecdsa.deserialize_compact(compact))
    return public.verify(der, digest, hasher=None)


def discv4_make(sk, kind, data):
    signed = bytes([int(kind)]) + unhex(data)
    body = sign64(unhex(sk), keccak256(signed)) + signed
    return tohex(keccak256(body) + body)


def endpoint(item):
    if not isinstance(item, list) or len(item) != 3 or not isinstance(item[0], bytes):
        raise MalformedError("endpoint")
    ports = [scalar(item[1]), scalar(item[2])]
    if max(ports) >= 2**16:
        raise MalformedError("port")
    return [item[0]] + ports


def sized(item, size):
    if not isinstance(item, bytes) or len(item) != size:
        raise MalformedError("size")
    return item


def optional_seq(items):
    if not items:
        return []
    seq = scalar(items[0])
    if seq >= 2**64:
        raise MalformedError("seq")
    return [seq]


def discv4_fields(kind, items):
    """The fields that the packet type defines; further items are ignored (EIP-8)."""
    need = {1: 4, 2: 3, 3: 2, 4: 2, 5: 1, 6: 2}[kind]
    if not isinstance(items, list) or len(items) < need:
        raise MalformedError("fields")
    if kind == 1:
        return [scalar(items[0]), endpoint(items[1]), endpoint(items[2]),
                scalar(items[3])] + optional_seq(items[4:])  # fmt: skip
    if kind == 2:
        return [endpoint(items[0]), sized(items[1], 32),
                scalar(items[2])] + optional_seq(items[3:])  # fmt: skip
    if kind == 3:
        return [sized(items[0], 64), scalar(items[1])]
    if kind == 4:
        if not isinstance(items[0], list):
            raise MalformedError("nodes")
        nodes = []
        for node in items[0]:
            if not isinstance(node, list) or len(node) != 4:
                raise MalformedError("node")
            nodes.append(endpoint(node[:3]) + [sized(node[3], 64)])
        return [nodes, scalar(items[1])]
    if kind == 5:
        return [scalar(items[0])]
    return [sized(items[0], 32), items[1]]


def discv4_read(word):
    data = unhex(word)
    if len(data) > 1280 or len(data) < 98:
        raise MalformedError("size")
    if keccak256(data[32:]) != data[:32]:
        raise MalformedError("hash")
    signature, kind, body = data[32:97], data[97], data[98:]
    if signature[64] > 1:
        raise MalformedError("recovery id")
    public = coincurve.PublicKey.from_signature_and_message(
        signature, keccak256(data[97:]), hasher=None
    )
    if not 1 <= kind <= 6:
        raise MalformedError("type")
    # EIP-8: the bytes after the first RLP item are ignored.
    fields = discv4_fields(kind, rlp.decode(body, strict=False))
    sender = public.format(compressed=False)[1:].hex()
    return f"{sender} {data[:32].hex()} {kind} {rlp.encode(fields).hex()}"


def libp2p_verify(key, message, signature):
    key = unhex(key)
    if len(key) != 37 or key[:4] != bytes([0x08, 0x02, 0x12, 0x21]):
        return "0"
    try:
        public = coincurve.PublicKey(key[4:])
        return str(int(public.verify(unhex(signature), unhex(message))))
    except ValueError:
        return "0"


def libp2p_sign(sk, message):
    return tohex(coincurve.PrivateKey(unhex(sk)).sign(unhex(message)))


HANDLERS = {
    "enr_make": enr_make,
    "enr_read": enr_read,
    "discv4_make": discv4_make,
    "discv4_read": discv4_read,
    "libp2p_verify": libp2p_verify,
    "libp2p_sign": libp2p_sign,
}


def noise_xx(s_i, e_i, s_r, e_r, prologue, p1, p2, p3, text):
    """A whole Noise XX handshake by the noiseprotocol package, then one transport message."""
    from noise.connection import Keypair, NoiseConnection

    sides = []
    for initiator, static, ephemeral in ((True, s_i, e_i), (False, s_r, e_r)):
        c = NoiseConnection.from_name(b"Noise_XX_25519_ChaChaPoly_SHA256")
        c.set_as_initiator() if initiator else c.set_as_responder()
        c.set_prologue(unhex(prologue))
        c.set_keypair_from_private_bytes(Keypair.STATIC, unhex(static))
        c.set_keypair_from_private_bytes(Keypair.EPHEMERAL, unhex(ephemeral))
        c.start_handshake()
        sides.append(c)
    a, b = sides
    m1 = a.write_message(unhex(p1))
    assert bytes(b.read_message(m1)) == unhex(p1)
    m2 = b.write_message(unhex(p2))
    assert bytes(a.read_message(m2)) == unhex(p2)
    m3 = a.write_message(unhex(p3))
    assert bytes(b.read_message(m3)) == unhex(p3)
    first = a.encrypt(unhex(text))
    back = b.encrypt(unhex(text))
    return " ".join(tohex(x) for x in (m1, m2, m3, first, back))


HANDLERS["noise_xx"] = noise_xx

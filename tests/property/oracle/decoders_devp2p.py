"""References for the decoders driver: devp2p, RLPx, discv5, discv4, ENR entries, Noise."""

# An RLP item is written as text: hexadecimal bytes, `-` for none, `[a,b]` for a list.
#
# p2p_frame <snappy> <id item> <body item> <tail>   Frame data: an ID, then the message.
# p2p_dec <snappy> <frame data>         The message of the "p2p" capability, as text.
# p2p_reason <n>                        The name of a reason of Disconnect, or none.
# p2p_negotiate <ours> <theirs> <lens>  The shared capabilities with their first IDs.
# p2p_route <ours> <theirs> <lens> <id> The capability of an ID and the ID within it.
# p2p_receive <phase> <ours> <theirs> <lens> <snappy> <frame>
#                                       What a frame carries in a phase of a session.
# snappy_declare <length> <tail>        A Snappy block that declares a length.
# snappy_zeros <n>                      A Snappy block of that many zero bytes, by cramjam.
# rlpx_auth_make <static a> <eph a> <nonce a> <pub b> <r> <iv> <padding> <tweak>
#                                       An auth packet, with one thing changed before it is sealed.
# rlpx_auth_read <sk> <packet>          What the recipient reads of an auth packet.
# rlpx_ack_read <sk> <packet>           What the initiator reads of an ack packet.
# rlpx_ack_make <pub> <r> <iv> <body item> <padding> <size delta>   An ack packet.
# rlpx_ack_old <pub> <r> <iv> <eph pub> <nonce>     The ack of before EIP-8.
# rlpx_secrets <static a> <eph a> <nonce a> <static b> <eph b> <nonce b> <auth> <ack>
#                                       The secrets of a session and both first MACs.
# d5_whoareyou <dest> <iv> <nonce> <id nonce> <enr seq>   The packet and its challenge data.
# d5_write <dest> <iv> <flag> <nonce> <authdata> <message>   A packet of any header fields.
# d5_read <dest> <packet>               flag, nonce, authdata, message and challenge data.
# d5_seal <key> <src> <dest> <iv> <nonce> <plaintext>     An ordinary message packet.
# d5_open <key> <dest> <packet>         Its source and its plaintext.
# d5_idsign <sk> <challenge> <eph pub> <id b>      The ID signature of node A.
# d5_accept <sk b> <challenge> <id a> <id b> <pub a> <eph pub> <sig>
#                                       The session keys of node B, if the handshake holds.
# enr_make <sk> <seq> <scheme> <pairs> <tweak>      A node record, with one thing changed.
# enr_signed_by <record> <sender>       Whether the record is a "v4" record of the sender.
# enr_entries <count> <fork> <pairs>    The consensus entries of a record at a fork.
# enr_keys <fork>                       The consensus keys that exist at a fork.
# enr_eth <item>                        The fork identifier of an "eth" entry.
# enr_eth_make <hash> <next>            The RLP bytes of an "eth" entry.
# noise_make <key> <sig> <exts> <variant>           A handshake payload, in one of its forms.
# noise_exts <exts>                     The bytes of extensions.
# noise_expect <sk> <static>            The identity key and the signature of a static key.
# noise_payload <bytes>                 The fields of a payload, by the protobuf package.
# noise_outer <bytes>                   The key and the signature, with extensions left closed.
# noise_ext <bytes>                     Extensions in the canonical bytes of the package.
# noise_verify <key> <static> <sig>     Whether the identity key signed the static key.
# noise_libp2p <s i> <e i> <s r> <e r> <m1> <m2> <m3>     The payloads of a handshake.
# noise_frame <bytes>                   A message behind its 16-bit length.
# noise_unframe <bytes>                 The message of exactly one frame.

import hashlib
import hmac
import warnings

import coincurve
import cramjam
from Crypto.Hash import keccak
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from decoders_util import tohex, unhex
from google.protobuf import descriptor_pb2, descriptor_pool, message_factory
from remerkleable.basic import uint64
from remerkleable.bitfields import Bitvector
from remerkleable.byte_arrays import Bytes4
from remerkleable.complex import Container

import rlp


class MalformedError(Exception):
    pass


def keccak256(data):
    return keccak.new(digest_bits=256, data=data).digest()


# RLP items as text.


def parse_item(text):
    """The item of a text: bytes in hexadecimal, or a list in brackets."""
    item, rest = parse_item_at(text)
    if rest:
        raise MalformedError("text after an item")
    return item


def parse_item_at(text):
    if text.startswith("["):
        items, rest = [], text[1:]
        while not rest.startswith("]"):
            item, rest = parse_item_at(rest)
            items.append(item)
            if rest.startswith(","):
                rest = rest[1:]
        return items, rest[1:]
    end = len(text)
    for mark in ",]":
        at = text.find(mark)
        if at != -1:
            end = min(end, at)
    return unhex(text[:end]), text[end:]


def show_item(item):
    if isinstance(item, list):
        return "[" + ",".join(show_item(x) for x in item) + "]"
    return tohex(item)


def scalar(item):
    """A canonical RLP integer: a byte string with no leading zero byte."""
    if not isinstance(item, bytes) or item[:1] == b"\x00":
        raise MalformedError("not a scalar")
    return int.from_bytes(item, "big")


def blob(item):
    if not isinstance(item, bytes):
        raise MalformedError("not a byte string")
    return item


def sized(item, size):
    if len(blob(item)) != size:
        raise MalformedError("size")
    return item


def members(item):
    if not isinstance(item, list):
        raise MalformedError("not a list")
    return item


# Snappy, written from format_description.txt.


def snappy_block(data):
    """The bytes of a raw Snappy block, with the preamble read as the C++ reference reads it."""
    declared, rest = snappy_preamble(data)
    out, pos = bytearray(), 0
    while pos < len(rest):
        tag = rest[pos]
        pos += 1
        if tag & 3 == 0:
            length = tag >> 2
            if length >= 60:
                extra = length - 59
                if pos + extra > len(rest):
                    raise MalformedError("literal length")
                length = int.from_bytes(rest[pos : pos + extra], "little")
                pos += extra
            length += 1
            if pos + length > len(rest):
                raise MalformedError("literal")
            out += rest[pos : pos + length]
            pos += length
        else:
            if tag & 3 == 1:
                length, width = 4 + ((tag >> 2) & 7), 1
            else:
                length, width = 1 + (tag >> 2), 2 if tag & 3 == 2 else 4
            if pos + width > len(rest):
                raise MalformedError("copy")
            offset = int.from_bytes(rest[pos : pos + width], "little")
            if tag & 3 == 1:
                offset |= (tag >> 5) << 8
            pos += width
            if offset == 0 or offset > len(out):
                raise MalformedError("offset")
            for _ in range(length):
                out.append(out[-offset])
        if len(out) > declared:
            raise MalformedError("past the declared length")
    if len(out) != declared:
        raise MalformedError("short of the declared length")
    return bytes(out)


def snappy_preamble(data):
    declared, shift, pos = 0, 0, 0
    while True:
        if pos >= len(data):
            raise MalformedError("preamble truncated")
        if pos >= 5:
            raise MalformedError("preamble too long")
        byte = data[pos]
        pos += 1
        declared |= (byte & 0x7F) << shift
        shift += 7
        if byte < 0x80:
            break
    if declared > 2**32 - 1:
        raise MalformedError("preamble too large")
    return declared, data[pos:]


def varint(n):
    out = bytearray()
    while n >= 0x80:
        out.append(n & 0x7F | 0x80)
        n >>= 7
    out.append(n)
    return bytes(out)


def snappy_declare(length, tail):
    return tohex(varint(int(length)) + unhex(tail))


def snappy_zeros(n):
    return tohex(bytes(cramjam.snappy.compress_raw(bytes(int(n)))))


# The "p2p" capability, from rlpx.md, "Capability Messaging".

MAX_MESSAGE_SIZE = 16 * 1024 * 1024

REASONS = {
    0x00: "requested",
    0x01: "tcpError",
    0x02: "breachOfProtocol",
    0x03: "uselessPeer",
    0x04: "tooManyPeers",
    0x05: "alreadyConnected",
    0x06: "incompatibleVersion",
    0x07: "nullIdentity",
    0x08: "clientQuitting",
    0x09: "unexpectedIdentity",
    0x0A: "sameIdentity",
    0x0B: "pingTimeout",
    0x10: "other",
}


def p2p_frame(snappy, ident, body, tail):
    data = rlp.encode(parse_item(body))
    if snappy == "1":
        data = bytes(cramjam.snappy.compress_raw(data))
    return tohex(rlp.encode(parse_item(ident)) + data + unhex(tail))


def first_item(data):
    """The first RLP item of the data, and the bytes after it."""
    if not data:
        raise MalformedError("empty")
    item, _, end = rlp.codec.consume_item(data, 0)
    # The package checks the canonical form only in `decode`, so the prefix goes through it.
    return rlp.decode(data[:end], strict=True), data[end:]


def p2p_split(data):
    ident, rest = first_item(data)
    return scalar(ident), rest


def p2p_data(compressed, rest):
    if not compressed:
        return rest
    declared, _ = snappy_preamble(rest)
    if declared > MAX_MESSAGE_SIZE:
        raise MalformedError("too large")
    return snappy_block(rest)


def p2p_message(ident, item):
    if ident == 0:
        fields = members(item)
        if len(fields) < 5:
            raise MalformedError("hello fields")
        caps = []
        for cap in members(fields[2]):
            if len(members(cap)) != 2:
                raise MalformedError("capability")
            caps.append(f"{tohex(blob(cap[0]))}/{scalar(cap[1])}")
        return "|".join(
            [
                "hello",
                str(scalar(fields[0])),
                tohex(blob(fields[1])),
                ";".join(caps) or "-",
                str(scalar(fields[3])),
                tohex(sized(fields[4], 64)),
            ]
        )
    if ident == 1:
        fields = members(item)
        if len(fields) > 1:
            raise MalformedError("disconnect fields")
        return "disconnect|" + (str(scalar(fields[0])) if fields else "none")
    if ident in (2, 3):
        if item != []:
            raise MalformedError("not the empty list")
        return "ping" if ident == 2 else "pong"
    raise MalformedError("unknown id")


def p2p_dec(snappy, word):
    ident, rest = p2p_split(unhex(word))
    data = p2p_data(snappy == "1" and ident != 0, rest)
    return p2p_message(ident, rlp.decode(data, strict=True))


def p2p_reason(n):
    return REASONS.get(int(n), "none")


def parse_caps(word):
    if word == "-":
        return []
    return [(unhex(c.split("/")[0]), int(c.split("/")[1])) for c in word.split(";")]


def cap_length(lens, cap):
    """The number of IDs of a capability: an entry of the table, chosen by its name and version."""
    return lens[(sum(cap[0]) + cap[1]) % len(lens)]


def shared_caps(ours, theirs):
    """The shared capabilities, from "Message ID-based Multiplexing"."""
    best = {}
    for name, version in set(ours) & set(theirs):
        best[name] = max(version, best.get(name, 0))
    return sorted(best.items())


def offsets(ours, theirs, lens):
    out, at = [], 0x10
    for cap in shared_caps(parse_caps(ours), parse_caps(theirs)):
        out.append((cap, at))
        at += cap_length(lens, cap)
    return out


def p2p_negotiate(ours, theirs, lens):
    lens = [int(x) for x in lens.split(",")]
    return ";".join(f"{tohex(c[0])}/{c[1]}@{at}" for c, at in offsets(ours, theirs, lens)) or "-"


def p2p_route(ours, theirs, lens, ident):
    lens, ident = [int(x) for x in lens.split(",")], int(ident)
    for cap, at in offsets(ours, theirs, lens):
        if at <= ident < at + cap_length(lens, cap):
            return f"{tohex(cap[0])}/{cap[1]}/{ident - at}"
    return "none"


def p2p_receive(phase, ours, theirs, lens, snappy, frame):
    """What one frame carries, from the section on the "p2p" capability of rlpx.md."""
    if phase == "closed":
        raise MalformedError("closed")
    ident, rest = p2p_split(unhex(frame))
    if phase == "await":
        # Only Hello and Disconnect pass before the Hello, and no Hello has set compression.
        if ident > 1:
            raise MalformedError("before hello")
        return p2p_message(ident, rlp.decode(rest, strict=True))
    if ident == 0:
        raise MalformedError("second hello")
    if ident < 0x10:
        return p2p_message(ident, rlp.decode(p2p_data(snappy == "1", rest), strict=True))
    routed = p2p_route(ours, theirs, lens, str(ident))
    if routed == "none":
        raise MalformedError("unknown id")
    data = p2p_data(snappy == "1", rest)
    if len(data) > MAX_MESSAGE_SIZE:
        raise MalformedError("too large")
    return f"cap|{routed}|{tohex(data)}"


# ECIES and the handshake of RLPx, from rlpx.md.


def aes_ctr(key, iv, data):
    enc = Cipher(algorithms.AES(key), modes.CTR(iv)).encryptor()
    return enc.update(data) + enc.finalize()


def concat_kdf(secret, length):
    out, counter = b"", 1
    while len(out) < length:
        out += hashlib.sha256(counter.to_bytes(4, "big") + secret).digest()
        counter += 1
    return out[:length]


def agree(sk, public):
    """The x coordinate of the product of a private key and a public key."""
    return public.multiply(sk).format(compressed=True)[1:]


def ecies_keys(secret):
    keys = concat_kdf(secret, 32)
    return keys[:16], hashlib.sha256(keys[16:]).digest()


def ecies_encrypt(public64, r, iv, shared, message):
    enc_key, mac_key = ecies_keys(agree(r, coincurve.PublicKey(b"\x04" + public64)))
    c = aes_ctr(enc_key, iv, message)
    d = hmac.new(mac_key, iv + c + shared, hashlib.sha256).digest()
    return coincurve.PrivateKey(r).public_key.format(compressed=False) + iv + c + d


def ecies_decrypt(sk, shared, data):
    if len(data) < 65 + 16 + 32 or data[0] != 4:
        raise MalformedError("ciphertext")
    enc_key, mac_key = ecies_keys(agree(sk, coincurve.PublicKey(data[:65])))
    iv, c, d = data[65:81], data[81:-32], data[-32:]
    if hmac.new(mac_key, iv + c + shared, hashlib.sha256).digest() != d:
        raise MalformedError("tag")
    return aes_ctr(enc_key, iv, c)


def rlpx_open(sk, packet):
    if len(packet) < 2 or int.from_bytes(packet[:2], "big") != len(packet) - 2:
        raise MalformedError("size")
    return ecies_decrypt(sk, packet[:2], packet[2:])


def rlpx_seal(public, r, iv, plain, delta=0):
    size = (len(plain) + 113 + delta) % 65536
    prefix = size.to_bytes(2, "big")
    return prefix + ecies_encrypt(public, r, iv, prefix, plain)


def rlpx_auth_make(static_a, eph_a, nonce_a, pub_b, r, iv, padding, tweak):
    """An auth packet of rlpx.md, whose body has one thing changed when the tweak names one."""
    static_a, eph_a, nonce_a, pub_b, r, iv, padding = map(
        unhex, (static_a, eph_a, nonce_a, pub_b, r, iv, padding)
    )
    token = xor(agree(static_a, coincurve.PublicKey(b"\x04" + pub_b)), nonce_a)
    sig = coincurve.PrivateKey(eph_a).sign_recoverable(token, hasher=None)
    public = coincurve.PrivateKey(static_a).public_key.format(compressed=False)[1:]
    body = [sig, public, nonce_a, b"\x04"]
    if tweak == "extra":
        body += [b"\x01", [b"\x02", []]]
    elif tweak == "fewer":
        body = body[:3]
    elif tweak == "versionlist":
        body[3] = []
    elif tweak.startswith("version"):
        body[3] = unhex(tweak[7:])
    elif tweak == "recid":
        body[0] = sig[:64] + bytes([sig[64] + 2])
    elif tweak == "otherid":
        body[0] = sig[:64] + bytes([sig[64] ^ 1])
    elif tweak == "sigflip":
        body[0] = sig[:5] + bytes([sig[5] ^ 0x10]) + sig[6:]
    elif tweak == "highs":
        s = N - int.from_bytes(sig[32:64], "big")
        body[0] = sig[:32] + s.to_bytes(32, "big") + bytes([sig[64] ^ 1])
    elif tweak == "zeros":
        body[0] = sig[:32] + bytes(32) + sig[64:]
    elif tweak == "sigshort":
        body[0] = sig[:64]
    elif tweak == "nonceshort":
        body[2] = nonce_a[:31]
    elif tweak == "noncelong":
        body[2] = nonce_a + b"\x00"
    elif tweak == "offcurve":
        body[1] = public[:63] + bytes([public[63] ^ 1])
    elif tweak == "otherkey":
        body[1] = coincurve.PrivateKey(eph_a).public_key.format(compressed=False)[1:]
    elif tweak == "keyshort":
        body[1] = public[:63]
    elif tweak == "bytes":
        return tohex(rlpx_seal(pub_b, r, iv, rlp.encode(b"".join(body)) + padding))
    delta = {"sizeup": 1, "sizedown": -1}.get(tweak, 0)
    return tohex(rlpx_seal(pub_b, r, iv, rlp.encode(body) + padding, delta))


def rlpx_auth_read(sk, packet):
    """The recipient's reading of auth: static key, nonce, version, ephemeral key."""
    sk = unhex(sk)
    items, _ = first_item(rlpx_open(sk, unhex(packet)))
    if len(members(items)) < 4:
        raise MalformedError("fields")
    signature, public, nonce = sized(items[0], 65), sized(items[1], 64), sized(items[2], 32)
    version = scalar(items[3])
    if signature[64] > 1:
        raise MalformedError("recovery id")
    token = xor(agree(sk, coincurve.PublicKey(b"\x04" + public)), nonce)
    eph = coincurve.PublicKey.from_signature_and_message(signature, token, hasher=None)
    return f"{public.hex()} {nonce.hex()} {version} {eph.format(compressed=False)[1:].hex()}"


def rlpx_ack_read(sk, packet):
    body = rlpx_open(unhex(sk), unhex(packet))
    # EIP-8: the bytes after the list are padding.
    items, _ = first_item(body)
    if len(members(items)) < 3:
        raise MalformedError("fields")
    public, nonce = sized(items[0], 64), sized(items[1], 32)
    coincurve.PublicKey(b"\x04" + public)
    return f"{public.hex()} {nonce.hex()} {scalar(items[2])}"


def rlpx_ack_make(public, r, iv, body, padding, delta):
    plain = rlp.encode(parse_item(body)) + unhex(padding)
    return tohex(rlpx_seal(unhex(public), unhex(r), unhex(iv), plain, int(delta)))


def rlpx_ack_old(public, r, iv, eph, nonce):
    plain = unhex(eph) + unhex(nonce) + b"\x00"
    return tohex(ecies_encrypt(unhex(public), unhex(r), unhex(iv), b"", plain))


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b, strict=True))


def rlpx_secrets(static_a, eph_a, nonce_a, static_b, eph_b, nonce_b, auth, ack):
    """The secrets of rlpx.md from the private keys, with what the packets must hold."""
    static_a, eph_a, nonce_a, static_b, eph_b, nonce_b, auth, ack = map(
        unhex, (static_a, eph_a, nonce_a, static_b, eph_b, nonce_b, auth, ack)
    )
    public = lambda sk: coincurve.PrivateKey(sk).public_key  # noqa: E731
    # The packets hold what each side sent: read them as the other side does.
    fields, _ = first_item(rlpx_open(static_b, auth))
    token = xor(agree(static_b, public(static_a)), nonce_a)
    signer = coincurve.PublicKey.from_signature_and_message(fields[0], token, hasher=None)
    if signer.format() != public(eph_a).format() or fields[2] != nonce_a:
        raise MalformedError("auth is not the initiator's")
    if fields[1] != public(static_a).format(compressed=False)[1:]:
        raise MalformedError("auth names another static key")
    fields, _ = first_item(rlpx_open(static_a, ack))
    if fields[0] != public(eph_b).format(compressed=False)[1:] or fields[1] != nonce_b:
        raise MalformedError("ack is not the recipient's")
    ephemeral = agree(eph_a, public(eph_b))
    shared = keccak256(ephemeral + keccak256(nonce_b + nonce_a))
    aes_secret = keccak256(ephemeral + shared)
    mac_secret = keccak256(ephemeral + aes_secret)
    initiator_egress = keccak256(xor(mac_secret, nonce_b) + auth)[:16]
    recipient_egress = keccak256(xor(mac_secret, nonce_a) + ack)[:16]
    return " ".join(x.hex() for x in (aes_secret, mac_secret, initiator_egress, recipient_egress))


# discv5, from discv5-wire.md.


def d5_mask(dest, iv, data):
    return aes_ctr(dest[:16], iv, data)


def d5_header(flag, nonce, authdata):
    return b"discv5\x00\x01" + bytes([flag]) + nonce + len(authdata).to_bytes(2, "big") + authdata


def d5_packet(dest, iv, header, message):
    packet = iv + d5_mask(dest, iv, header) + message
    if len(packet) > 1280:
        raise MalformedError("too large")
    return packet


def d5_whoareyou(dest, iv, nonce, id_nonce, enr_seq):
    dest, iv, nonce, id_nonce = map(unhex, (dest, iv, nonce, id_nonce))
    header = d5_header(1, nonce, id_nonce + int(enr_seq).to_bytes(8, "big"))
    return f"{d5_packet(dest, iv, header, b'').hex()} {(iv + header).hex()}"


def d5_write(dest, iv, flag, nonce, authdata, message):
    dest, iv, nonce, authdata, message = map(unhex, (dest, iv, nonce, authdata, message))
    header = d5_header(int(flag), nonce, authdata)
    return tohex(iv + d5_mask(dest, iv, header) + message)


def d5_parse(dest, packet):
    """The fields of a packet: flag, nonce, authdata, message and the IV with the header."""
    if not 63 <= len(packet) <= 1280:
        raise MalformedError("size")
    iv = packet[:16]
    plain = d5_mask(dest, iv, packet[16:])
    if plain[:8] != b"discv5\x00\x01":
        raise MalformedError("protocol id")
    flag, nonce = plain[8], plain[9:21]
    size = int.from_bytes(plain[21:23], "big")
    if 23 + size > len(plain):
        raise MalformedError("authdata size")
    authdata, message = plain[23 : 23 + size], packet[16 + 23 + size :]
    if flag == 0:
        ok = size == 32
    elif flag == 1:
        ok = size == 24 and not message
    elif flag == 2:
        ok = size >= 34 and 34 + authdata[32] + authdata[33] <= size
    else:
        ok = False
    if not ok:
        raise MalformedError("authdata")
    return flag, nonce, authdata, message, iv + plain[: 23 + size]


def d5_read(dest, packet):
    flag, nonce, authdata, message, challenge = d5_parse(unhex(dest), unhex(packet))
    return f"{flag} {nonce.hex()} {authdata.hex()} {tohex(message)} {challenge.hex()}"


def d5_seal_raw(key, src, dest, iv, nonce, plaintext):
    header = d5_header(0, nonce, src)
    return d5_packet(dest, iv, header, AESGCM(key).encrypt(nonce, plaintext, iv + header))


def d5_seal(key, src, dest, iv, nonce, plaintext):
    return tohex(d5_seal_raw(*map(unhex, (key, src, dest, iv, nonce, plaintext))))


def d5_open_raw(key, dest, packet):
    flag, nonce, authdata, message, ad = d5_parse(dest, packet)
    if flag != 0:
        raise MalformedError("not an ordinary message")
    return authdata, AESGCM(key).decrypt(nonce, message, ad)


def d5_open(key, dest, packet):
    src, plaintext = d5_open_raw(unhex(key), unhex(dest), unhex(packet))
    return f"{src.hex()} {tohex(plaintext)}"


def d5_id_digest(challenge, eph, id_b):
    return hashlib.sha256(b"discovery v5 identity proof" + challenge + eph + id_b).digest()


def d5_idsign(sk, challenge, eph, id_b):
    digest = d5_id_digest(unhex(challenge), unhex(eph), unhex(id_b))
    return coincurve.PrivateKey(unhex(sk)).sign_recoverable(digest, hasher=None)[:64].hex()


def d5_accept(sk_b, challenge, id_a, id_b, pub_a, eph, sig):
    """Step 4 of the handshake, from discv5-theory.md, for the "v4" identity scheme."""
    sk_b, challenge, id_a, id_b, pub_a, eph, sig = map(
        unhex, (sk_b, challenge, id_a, id_b, pub_a, eph, sig)
    )
    digest = d5_id_digest(challenge, eph, id_b)
    if len(sig) != 64 or not verify64(coincurve.PublicKey(pub_a), digest, sig):
        raise MalformedError("id signature")
    if len(eph) != 33:
        raise MalformedError("ephemeral key size")
    secret = coincurve.PublicKey(eph).multiply(sk_b).format(compressed=True)
    info = b"discovery v5 key agreement" + id_a + id_b
    keys = HKDF(algorithm=hashes.SHA256(), length=32, salt=challenge, info=info).derive(secret)
    return f"{keys[:16].hex()} {keys[16:].hex()}"


def d5_self_check():
    """The packets of discv5-wire-test-vectors.md, so the model is the specification's."""
    h = bytes.fromhex
    src = h("aaaa8419e9f49d0083561b48287df592939a8d19947d8c0ef88f2a4856a69fbb")
    dest = h("bbbb9d047f0488c0b5a93c1c3f2d8bafc7c8ff337024a55434a0d0555de64db9")
    ping = h(
        "00000000000000000000000000000000088b3d4342774649325f313964a39e55"
        "ea96c005ad52be8c7560413a7008f16c9e6d2f43bbea8814a546b7409ce783d3"
        "4c4f53245d08dab84102ed931f66d1492acb308fa1c6715b9d139b81acbdcc"
    )
    plaintext = b"\x01" + rlp.encode([h("00000001"), 2])
    assert d5_open_raw(bytes(16), dest, ping) == (src, plaintext)
    assert d5_seal_raw(bytes(16), src, dest, bytes(16), b"\xff" * 12, plaintext) == ping
    keys = d5_accept(
        "66fb62bfbd66b9177a138c1e5cddbe4f7c30c343e94e68df8769459cb1cde628",
        "000000000000000000000000000000006469736376350001010102030405060708090a0b0c"
        "00180102030405060708090a0b0c0d0e0f100000000000000001",
        src.hex(),
        dest.hex(),
        "0313d14211e0287b2361a1615890a9b5212080546d0a257ae4cff96cf534992cb9",
        "039a003ba6517b473fa0cd74aefe99dadfdb34627f90fec6362df85803908f53a5",
        d5_idsign(
            "eef77acb6c6a6eebc5b363a475ac583ec7eccdb42b6481424c60f59aa326547f",
            "000000000000000000000000000000006469736376350001010102030405060708090a0b0c"
            "00180102030405060708090a0b0c0d0e0f100000000000000001",
            "039a003ba6517b473fa0cd74aefe99dadfdb34627f90fec6362df85803908f53a5",
            dest.hex(),
        ),
    )
    # The read key of the Ping handshake packet of the vectors.
    assert keys.startswith("4f9fac6de7567d1e3b1241dffe90f662 ")
    made = d5_whoareyou(
        dest.hex(),
        bytes(16).hex(),
        "0102030405060708090a0b0c",
        "0102030405060708090a0b0c0d0e0f10",
        "0",
    )
    assert made == (
        "00000000000000000000000000000000088b3d434277464933a1ccc59f5967ad"
        "1d6035f15e528627dde75cd68292f9e6c27d6b66c8100a873fcbaed4e16b8d "
        "000000000000000000000000000000006469736376350001010102030405060708090a0b0c"
        "00180102030405060708090a0b0c0d0e0f100000000000000000"
    )


# Node records, from EIP-778, and their entries.

N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def enr_make(sk, seq, scheme, pairs, tweak):
    """A record signed by the key, with one thing changed after or before it is signed."""
    sk = unhex(sk)
    entries = {b"id": unhex(scheme)}
    if tweak != "nokey":
        entries[b"secp256k1"] = coincurve.PrivateKey(sk).public_key.format(compressed=True)
    for pair in pairs.split(";"):
        if pair != "-":
            key, value = pair.split("=")
            entries[unhex(key)] = parse_item(value)
    content = [int(seq)]
    for key in sorted(entries):
        content += [key, entries[key]]
    signature = coincurve.PrivateKey(sk).sign_recoverable(
        keccak256(rlp.encode(content)), hasher=None
    )
    signature = signature[:64]
    if tweak == "flip":
        signature = signature[:40] + bytes([signature[40] ^ 1]) + signature[41:]
    elif tweak == "high":
        s = N - int.from_bytes(signature[32:], "big")
        signature = signature[:32] + s.to_bytes(32, "big")
    elif tweak == "short":
        signature = signature[:63]
    elif tweak == "seq":
        content[0] += 1
    return tohex(rlp.encode([signature] + content))


def verify64(public, digest, signature):
    """ECDSA verification of r || s; a high s is accepted, since EIP-778 sets no rule."""
    r = int.from_bytes(signature[:32], "big")
    s = int.from_bytes(signature[32:], "big")
    if not (0 < r < N and 0 < s < N):
        return False
    s = min(s, N - s)
    compact = r.to_bytes(32, "big") + s.to_bytes(32, "big")
    der = coincurve.ecdsa.cdata_to_der(coincurve.ecdsa.deserialize_compact(compact))
    return public.verify(der, digest, hasher=None)


def enr_signed_by(record, sender):
    """Whether the bytes are a valid "v4" record whose key is the sender's key."""
    try:
        return str(int(enr_signed_by_raw(unhex(record), unhex(sender))))
    except (MalformedError, rlp.exceptions.DecodingError, ValueError):
        return "0"


def enr_signed_by_raw(data, sender):
    if len(data) > 300:
        return False
    items = members(rlp.decode(data, strict=True))
    if len(items) < 2 or len(items) % 2 != 0:
        return False
    signature = blob(items[0])
    if scalar(items[1]) >= 2**64:
        return False
    keys = [blob(k) for k in items[2::2]]
    if any(a >= b for a, b in zip(keys, keys[1:], strict=False)):
        return False
    entries = dict(zip(keys, items[3::2], strict=True))
    if entries.get(b"id") != b"v4" or len(blob(entries.get(b"secp256k1", []))) != 33:
        return False
    public = coincurve.PublicKey(entries[b"secp256k1"])
    if public.format(compressed=False)[1:] != sender:
        return False
    return len(signature) == 64 and verify64(public, keccak256(rlp.encode(items[1:])), signature)


# The order of the upgrades on mainnet, with the consensus forks named as EthLib names them.
FORKS = [
    "frontier", "homestead", "daoFork", "tangerineWhistle", "spuriousDragon", "byzantium",
    "constantinople", "petersburg", "istanbul", "muirGlacier", "phase0", "berlin", "london",
    "altair", "arrowGlacier", "grayGlacier", "bellatrix", "paris", "shapella", "dencun",
    "pectra", "fusaka", "bpo1", "bpo2", "bpo3", "bpo4", "bpo5", "glamsterdam", "hegota",
]  # fmt: skip


def at_or_after(fork, first):
    return FORKS.index(fork) >= FORKS.index(first)


class ENRForkID(Container):
    fork_digest: Bytes4
    next_fork_version: Bytes4
    next_fork_epoch: uint64


def bitvector(value, count):
    """The bits of an SSZ bitvector: one byte per eight bits, and no bit set past the length."""
    if len(value) != (count + 7) // 8:
        raise MalformedError("bitvector size")
    bits = [(value[i // 8] >> (i % 8)) & 1 for i in range(len(value) * 8)]
    if any(bits[count:]):
        raise MalformedError("bitvector padding")
    out = "".join(str(b) for b in bits[:count])
    # The package must read the same bits.
    assert out == "".join(str(int(b)) for b in Bitvector[count].decode_bytes(value))
    return out


def enr_entries(count, fork, pairs):
    """The entries as the p2p-interface texts of phase0, altair and fulu define them."""
    count, entries = int(count), {}
    for pair in pairs.split(";"):
        if pair != "-":
            key, value = pair.split("=")
            # The first pair of a key is the one a reader finds.
            entries.setdefault(unhex(key), parse_item(value))

    def get(key):
        return blob(entries[key]) if key in entries else None

    eth2 = get(b"eth2")
    if eth2 is None or len(eth2) != 16:
        raise MalformedError("eth2")
    fork_id = ENRForkID.decode_bytes(eth2)
    assert bytes(fork_id.fork_digest) == eth2[:4]
    assert int(fork_id.next_fork_epoch) == int.from_bytes(eth2[8:], "little")
    out = [f"eth2={eth2[:4].hex()}/{eth2[4:8].hex()}/{int.from_bytes(eth2[8:], 'little')}"]
    attnets = get(b"attnets")
    out.append("attnets=" + ("none" if attnets is None else bitvector(attnets, count)))
    syncnets = get(b"syncnets") if at_or_after(fork, "altair") else None
    out.append("syncnets=" + ("none" if syncnets is None else bitvector(syncnets, 4)))
    if at_or_after(fork, "fusaka"):
        cgc, nfd = get(b"cgc"), get(b"nfd")
        if cgc is None or nfd is None or len(nfd) != 4 or scalar(cgc) >= 2**64:
            raise MalformedError("cgc or nfd")
        out += [f"cgc={scalar(cgc)}", f"nfd={nfd.hex()}"]
    else:
        out += ["cgc=none", "nfd=none"]
    return " ".join(out)


def enr_keys(fork):
    keys = ["eth2", "attnets"] if at_or_after(fork, "phase0") else []
    keys += ["syncnets"] if at_or_after(fork, "altair") else []
    keys += ["cgc", "nfd"] if at_or_after(fork, "fusaka") else []
    return ",".join(keys) or "-"


def enr_eth(word):
    """The fork identifier of `[[forkHash, forkNext], ...]`, from enr-entries/eth.md."""
    outer = members(parse_item(word))
    if not outer or len(members(outer[0])) != 2:
        raise MalformedError("eth entry")
    fork_hash, fork_next = sized(outer[0][0], 4), scalar(outer[0][1])
    if fork_next >= 2**64:
        raise MalformedError("fork next")
    return f"{fork_hash.hex()} {fork_next}"


def enr_eth_make(fork_hash, fork_next):
    return tohex(rlp.encode([[unhex(fork_hash), int(fork_next)]]))


# The handshake payload of noise-libp2p, with the schema of its specification.

NOISE_PROTO = """
message NoiseExtensions {
    repeated bytes webtransport_certhashes = 1;
    repeated string stream_muxers = 2;
}

message NoiseHandshakePayload {
  optional bytes identity_key = 1;
  optional bytes identity_sig = 2;
  optional NoiseExtensions extensions = 4;
}
"""


# The same payload with its extensions as bytes: what a reader sees that does not open them.
OPAQUE_PROTO = """
message OpaquePayload {
  optional bytes identity_key = 1;
  optional bytes identity_sig = 2;
  optional bytes extensions = 4;
}
"""


def proto_classes(name, text):
    """The classes of a schema, built from its descriptor at run time."""
    file = descriptor_pb2.FileDescriptorProto(name=name, syntax="proto2")
    optional, repeated = 1, 3
    types = {"bytes": 12, "string": 9}
    current = None
    for line in text.splitlines():
        words = line.replace(";", "").split()
        if words[:1] == ["message"]:
            current = file.message_type.add(name=words[1])
        elif len(words) == 5:
            field = current.field.add(name=words[2], number=int(words[4]))
            field.label = repeated if words[0] == "repeated" else optional
            field.type = types.get(words[1], 11)
            if words[1] not in types:
                field.type_name = "." + words[1]
    built = descriptor_pool.DescriptorPool().Add(file)
    return [message_factory.GetMessageClass(m) for m in built.message_types_by_name.values()]


NoiseExtensions, NoiseHandshakePayload = proto_classes("noise.proto", NOISE_PROTO)
(OpaquePayload,) = proto_classes("opaque.proto", OPAQUE_PROTO)


def parse_exts(word):
    """Extensions from text: `c` and bytes for a certificate hash, `m` and bytes for a muxer."""
    exts = NoiseExtensions()
    for part in word.split(","):
        if part.startswith("c"):
            exts.webtransport_certhashes.append(unhex(part[1:]))
        elif part.startswith("m"):
            exts.stream_muxers.append(unhex(part[1:]).decode("utf-8"))
    return exts


def noise_exts(word):
    return tohex(parse_exts(word).SerializeToString(deterministic=True))


def noise_expect(sk, static):
    """The identity key and the signature of a static key, by libsecp256k1."""
    key = coincurve.PrivateKey(unhex(sk))
    proto = bytes([0x08, 0x02, 0x12, 0x21]) + key.public_key.format(compressed=True)
    return f"{proto.hex()} {key.sign(b'noise-libp2p-static-key:' + unhex(static)).hex()}"


def pb_varint(data, pos):
    """A varint of the encoding guide: at most ten bytes, and a value below 2^64."""
    value = 0
    for count in range(10):
        if pos >= len(data):
            raise MalformedError("varint truncated")
        byte = data[pos]
        pos += 1
        value |= (byte & 0x7F) << (7 * count)
        if byte < 0x80:
            if value >= 2**64:
                raise MalformedError("varint overflow")
            return value, pos
    raise MalformedError("varint too long")


def pb_walk(data, pos, group):
    """The position after the records of a message, or after the end key of a group.

    The rules are those of the encoding guide.
    A field number is from 1 to 2^29 - 1, and a wire type from 0 to 5.
    A value fits the input, and a group ends with its own field number.
    """
    while pos < len(data):
        key, pos = pb_varint(data, pos)
        field, wire = key >> 3, key & 7
        if not 1 <= field <= 2**29 - 1:
            raise MalformedError("field number")
        if wire == 0:
            _, pos = pb_varint(data, pos)
        elif wire == 1:
            pos += 8
        elif wire == 2:
            size, pos = pb_varint(data, pos)
            pos += size
        elif wire == 3:
            pos = pb_walk(data, pos, field)
        elif wire == 4:
            if field != group:
                raise MalformedError("group end")
            return pos
        elif wire == 5:
            pos += 4
        else:
            raise MalformedError("wire type")
        if pos > len(data):
            raise MalformedError("value truncated")
    if group is not None:
        raise MalformedError("group not closed")
    return pos


def noise_outer(word):
    """The key and the signature by the package, if the bytes also keep the wire rules.

    The package skips an unknown group without checking the field numbers inside it.
    """
    data = unhex(word)
    payload = OpaquePayload()
    try:
        payload.ParseFromString(data)
    except Exception:
        payload = None
    try:
        pb_walk(data, 0, None)
    except MalformedError:
        if payload is not None:
            return "error only by the wire rules"
        raise
    if payload is None:
        raise MalformedError("only the package refuses")
    return f"{tohex(payload.identity_key)} {tohex(payload.identity_sig)}"


def record(field, wire, value):
    return varint(field << 3 | wire) + value


def noise_make(key, sig, exts, variant):
    """A payload in one of the forms that the protobuf encoding allows for the same message."""
    key, sig = unhex(key), unhex(sig)
    payload = NoiseHandshakePayload(identity_key=key, identity_sig=sig)
    if exts != "none":
        payload.extensions.CopyFrom(parse_exts(exts))
    plain = payload.SerializeToString(deterministic=True)
    lenrec = lambda field, value: record(field, 2, varint(len(value)) + value)  # noqa: E731
    k, s = lenrec(1, key), lenrec(2, sig)
    parts = [] if exts == "none" else [parse_exts(p).SerializeToString() for p in exts.split(",")]
    split = b"".join(lenrec(4, p) for p in parts)
    forms = {
        "plain": plain,
        "reversed": split + s + k,
        "twice": lenrec(1, b"\x01\x02") + lenrec(2, b"") + k + s + split,
        "split": k + split + s,
        "unknown": record(3, 0, varint(7)) + k + record(9, 2, b"\x01\x00") + s + split,
        "wiretype": k + s + split + record(1, 0, varint(5)) + record(2, 5, bytes(4)),
        "group": k + record(7, 3, record(1, 0, b"\x01") + record(7, 4, b"")) + s + split,
        # A group that holds a key with the field number 0, which the encoding forbids.
        "groupzero": k + record(7, 3, b"\x00\x01" + record(7, 4, b"")) + s + split,
    }
    return tohex(forms[variant])


def noise_payload(word):
    payload = NoiseHandshakePayload()
    payload.ParseFromString(unhex(word))
    ext = "none"
    if payload.HasField("extensions"):
        ext = tohex(payload.extensions.SerializeToString(deterministic=True))
    return f"{tohex(payload.identity_key)} {tohex(payload.identity_sig)} {ext}"


def noise_ext(word):
    exts = NoiseExtensions()
    exts.ParseFromString(unhex(word))
    return tohex(exts.SerializeToString(deterministic=True))


def noise_verify_raw(key, static, sig):
    """The rule of the peer ID specification for a secp256k1 key: ECDSA over SHA-256, in DER."""
    if len(key) != 37 or key[:4] != bytes([0x08, 0x02, 0x12, 0x21]):
        return False
    try:
        public = coincurve.PublicKey(key[4:])
        return public.verify(sig, b"noise-libp2p-static-key:" + static)
    except ValueError:
        return False


def noise_verify(key, static, sig):
    return str(int(noise_verify_raw(unhex(key), unhex(static), unhex(sig))))


def x25519_public(secret):
    key = X25519PrivateKey.from_private_bytes(secret)
    return key.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)


def noise_libp2p(s_i, e_i, s_r, e_r, m1, m2, m3):
    """The payloads of messages 2 and 3 of an XX handshake, read by the noiseprotocol package."""
    from noise.connection import Keypair, NoiseConnection

    s_i, e_i, s_r, e_r, m1, m2, m3 = map(unhex, (s_i, e_i, s_r, e_r, m1, m2, m3))
    sides = []
    for initiator, static, ephemeral in ((True, s_i, e_i), (False, s_r, e_r)):
        c = NoiseConnection.from_name(b"Noise_XX_25519_ChaChaPoly_SHA256")
        c.set_as_initiator() if initiator else c.set_as_responder()
        c.set_keypair_from_private_bytes(Keypair.STATIC, static)
        c.set_keypair_from_private_bytes(Keypair.EPHEMERAL, ephemeral)
        # The package warns that a fixed ephemeral key is for tests only, which this is.
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            c.start_handshake()
        sides.append(c)
    a, b = sides
    if bytes(a.write_message(b"")) != m1 or bytes(b.read_message(m1)) != b"":
        raise MalformedError("message 1")
    second = bytes(a.read_message(m2))
    if bytes(b.write_message(second)) != m2:
        raise MalformedError("message 2")
    third = bytes(b.read_message(m3))
    out = []
    for payload, static in ((second, s_r), (third, s_i)):
        parsed = NoiseHandshakePayload()
        parsed.ParseFromString(payload)
        signed = noise_verify_raw(parsed.identity_key, x25519_public(static), parsed.identity_sig)
        ext = "none"
        if parsed.HasField("extensions"):
            ext = tohex(parsed.extensions.SerializeToString(deterministic=True))
        out += [tohex(parsed.identity_key), str(int(signed)), ext]
    return " ".join(out)


def noise_frame(word):
    message = unhex(word)
    if len(message) > 65535:
        raise MalformedError("too long")
    return tohex(len(message).to_bytes(2, "big") + message)


def noise_unframe(word):
    data = unhex(word)
    if len(data) < 2 or int.from_bytes(data[:2], "big") != len(data) - 2:
        raise MalformedError("frame")
    return tohex(data[2:])


HANDLERS = {
    "p2p_frame": p2p_frame,
    "p2p_dec": p2p_dec,
    "p2p_reason": p2p_reason,
    "p2p_negotiate": p2p_negotiate,
    "p2p_route": p2p_route,
    "p2p_receive": p2p_receive,
    "snappy_declare": snappy_declare,
    "snappy_zeros": snappy_zeros,
    "rlpx_auth_make": rlpx_auth_make,
    "rlpx_auth_read": rlpx_auth_read,
    "rlpx_ack_read": rlpx_ack_read,
    "rlpx_ack_make": rlpx_ack_make,
    "rlpx_ack_old": rlpx_ack_old,
    "rlpx_secrets": rlpx_secrets,
    "d5_whoareyou": d5_whoareyou,
    "d5_write": d5_write,
    "d5_read": d5_read,
    "d5_seal": d5_seal,
    "d5_open": d5_open,
    "d5_idsign": d5_idsign,
    "d5_accept": d5_accept,
    "enr_make": enr_make,
    "enr_signed_by": enr_signed_by,
    "enr_entries": enr_entries,
    "enr_keys": enr_keys,
    "enr_eth": enr_eth,
    "enr_eth_make": enr_eth_make,
    "noise_make": noise_make,
    "noise_exts": noise_exts,
    "noise_expect": noise_expect,
    "noise_payload": noise_payload,
    "noise_outer": noise_outer,
    "noise_ext": noise_ext,
    "noise_verify": noise_verify,
    "noise_libp2p": noise_libp2p,
    "noise_frame": noise_frame,
    "noise_unframe": noise_unframe,
}

# The vectors need the functions above, so they run last.
d5_self_check()

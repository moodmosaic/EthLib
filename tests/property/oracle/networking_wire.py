"""discv5 and RLPx references, written from discv5-wire.md, discv5-theory.md and rlpx.md.

discv5_read <dest> <packet>             flag, nonce, authdata and message of a packet.
discv5_write <dest> <iv> <flag> <nonce> <authdata> <message>   A masked packet.
discv5_keys <eph sk> <dest pub> <challenge> <id a> <id b>      secret and session keys.
discv5_idsign <sk> <challenge> <eph pub> <id b>                The ID signature.
discv5_idverify <pub> <challenge> <eph pub> <id b> <sig>       Whether it verifies.
discv5_gcm <key> <nonce> <pt> <ad>      The encrypted message with its tag.
discv5_msg <plaintext>                  A message, as its type and its fields.
discv5_distance <a> <b>                 The logarithmic distance.
ecies_enc <pub> <r> <iv> <shared> <m>   An ECIES ciphertext of rlpx.md.
ecies_dec <sk> <shared> <ciphertext>    Its message.
rlpx_session <initiator> <eph> <inonce> <rnonce> <auth> <ack> <frames,...>
                                        The secrets and the frames of one side.
rlpx_auth <sk> <packet>                 What the recipient reads of an auth packet.
"""

import hashlib
import hmac

import coincurve
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from networking_crypto import MalformedError, keccak256, scalar, sign64, sized, verify64
from networking_util import tohex, unhex

import rlp


def aes_ctr(key, iv, data):
    enc = Cipher(algorithms.AES(key), modes.CTR(iv)).encryptor()
    return enc.update(data) + enc.finalize()


def aes_block(key, block):
    enc = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
    return enc.update(block) + enc.finalize()


def hkdf(salt, ikm, info, length):
    prk = hmac.new(salt, ikm, hashlib.sha256).digest()
    out, block, counter = b"", b"", 1
    while len(out) < length:
        block = hmac.new(prk, block + info + bytes([counter]), hashlib.sha256).digest()
        out += block
        counter += 1
    return out[:length]


# discv5.


def discv5_write_raw(dest, iv, flag, nonce, authdata, message):
    header = b"discv5" + b"\x00\x01" + bytes([flag]) + nonce
    header += len(authdata).to_bytes(2, "big") + authdata
    return iv + aes_ctr(dest[:16], iv, header) + message


def discv5_write(dest, iv, flag, nonce, authdata, message):
    return tohex(
        discv5_write_raw(
            unhex(dest), unhex(iv), int(flag), unhex(nonce), unhex(authdata), unhex(message)
        )
    )


def discv5_read(dest, packet):
    dest, packet = unhex(dest), unhex(packet)
    if not 63 <= len(packet) <= 1280:
        raise MalformedError("size")
    iv = packet[:16]
    plain = aes_ctr(dest[:16], iv, packet[16:])
    if plain[:8] != b"discv5\x00\x01":
        raise MalformedError("protocol id")
    flag, nonce = plain[8], plain[9:21]
    size = int.from_bytes(plain[21:23], "big")
    if 23 + size > len(plain):
        raise MalformedError("authdata size")
    authdata = plain[23 : 23 + size]
    message = packet[16 + 23 + size :]
    if flag == 0:
        ok = size == 32
    elif flag == 1:
        # The message of a WHOAREYOU packet is always empty.
        ok = size == 24 and not message
    elif flag == 2:
        ok = size >= 34 and 34 + authdata[32] + authdata[33] <= size
    else:
        raise MalformedError("flag")
    if not ok:
        raise MalformedError("authdata")
    return f"{flag} {nonce.hex()} {authdata.hex()} {tohex(message)}"


def ecdh_compressed(sk, public):
    return coincurve.PublicKey(public).multiply(sk).format(compressed=True)


def discv5_keys_raw(eph, dest_pub, challenge, id_a, id_b):
    secret = ecdh_compressed(eph, dest_pub)
    info = b"discovery v5 key agreement" + id_a + id_b
    keys = hkdf(challenge, secret, info, 32)
    return secret, keys[:16], keys[16:]


def discv5_keys(eph, dest_pub, challenge, id_a, id_b):
    out = discv5_keys_raw(*map(unhex, (eph, dest_pub, challenge, id_a, id_b)))
    return " ".join(x.hex() for x in out)


def id_digest(challenge, eph_pub, id_b):
    return hashlib.sha256(b"discovery v5 identity proof" + challenge + eph_pub + id_b).digest()


def discv5_idsign_raw(sk, challenge, eph_pub, id_b):
    return sign64(sk, id_digest(challenge, eph_pub, id_b))[:64]


def discv5_idsign(sk, challenge, eph_pub, id_b):
    return discv5_idsign_raw(*map(unhex, (sk, challenge, eph_pub, id_b))).hex()


def discv5_idverify(public, challenge, eph_pub, id_b, signature):
    signature = unhex(signature)
    if len(signature) != 64:
        return "0"
    digest = id_digest(unhex(challenge), unhex(eph_pub), unhex(id_b))
    return str(int(verify64(coincurve.PublicKey(unhex(public)), digest, signature)))


def discv5_gcm(key, nonce, plaintext, ad):
    return tohex(AESGCM(unhex(key)).encrypt(unhex(nonce), unhex(plaintext), unhex(ad)))


def u64(item):
    value = scalar(item)
    if value >= 2**64:
        raise MalformedError("uint64")
    return value


def blob(item):
    if not isinstance(item, bytes):
        raise MalformedError("bytes")
    return item


def distances(item, low):
    if not isinstance(item, list):
        raise MalformedError("distances")
    out = [scalar(d) for d in item]
    if any(not low <= d <= 256 for d in out):
        raise MalformedError("distance")
    return out


def records(item):
    if not isinstance(item, list):
        raise MalformedError("records")
    return item


def discv5_msg(word):
    data = unhex(word)
    if not data:
        raise MalformedError("empty")
    kind = data[0]
    counts = {1: 2, 2: 4, 3: 2, 4: 3, 5: 3, 6: 2, 7: 5, 8: 4, 9: 3, 10: 3}
    if kind not in counts:
        raise MalformedError("type")
    f = rlp.decode(data[1:], strict=True)
    if not isinstance(f, list) or len(f) != counts[kind]:
        raise MalformedError("fields")
    if len(blob(f[0])) > 8:
        raise MalformedError("request id")
    if kind == 1:
        out = [f[0], u64(f[1])]
    elif kind == 2:
        port = scalar(f[3])
        if len(blob(f[2])) not in (4, 16) or port >= 2**16:
            raise MalformedError("pong")
        out = [f[0], u64(f[1]), f[2], port]
    elif kind == 3:
        out = [f[0], distances(f[1], 0)]
    elif kind in (4, 10):
        out = [f[0], u64(f[1]), records(f[2])]
    elif kind == 5:
        out = [f[0], blob(f[1]), blob(f[2])]
    elif kind == 6:
        out = [f[0], blob(f[1])]
    elif kind == 7:
        out = [f[0], sized(f[1], 32), f[2], blob(f[3]), distances(f[4], 1)]
    elif kind == 8:
        out = [f[0], u64(f[1]), blob(f[2]), u64(f[3])]
    else:
        out = [f[0], sized(f[1], 32), distances(f[2], 1)]
    return f"{kind} {rlp.encode(out).hex()}"


def discv5_distance(a, b):
    return str((int(a, 16) ^ int(b, 16)).bit_length())


def self_check():
    """The vectors of discv5-wire-test-vectors.md, so the model is the specification's."""
    h = bytes.fromhex
    id_a = h("aaaa8419e9f49d0083561b48287df592939a8d19947d8c0ef88f2a4856a69fbb")
    id_b = h("bbbb9d047f0488c0b5a93c1c3f2d8bafc7c8ff337024a55434a0d0555de64db9")
    challenge = h(
        "000000000000000000000000000000006469736376350001010102030405060708090a0b0c"
        "00180102030405060708090a0b0c0d0e0f100000000000000000"
    )
    key = h("fb757dc581730490a1d7a00deea65e9b1936924caaea8f44d476014856b68736")
    _, initiator, recipient = discv5_keys_raw(
        key,
        h("0317931e6e0840220642f230037d285d122bc59063221ef3226b1f403ddc69ca91"),
        challenge,
        id_a,
        id_b,
    )
    assert initiator.hex() == "dccc82d81bd610f4f76d3ebe97a40571"
    assert recipient.hex() == "ac74bb8773749920b0d3a8881c173ec5"
    eph = h("039961e4c2356d61bedb83052c115d311acb3a96f5777296dcf297351130266231")
    assert discv5_idsign_raw(key, challenge, eph, id_b).hex() == (
        "94852a1e2318c4e5e9d422c98eaf19d1d90d876b29cd06ca7cb7546d0fff7b48"
        "4fe86c09a064fe72bdbef73ba8e9c34df0cd2b53e9d65528c2c7f336d5dfc6e6"
    )
    whoareyou = (
        "00000000000000000000000000000000088b3d434277464933a1ccc59f5967ad"
        "1d6035f15e528627dde75cd68292f9e6c27d6b66c8100a873fcbaed4e16b8d"
    )
    made = discv5_write_raw(
        id_b,
        bytes(16),
        1,
        h("0102030405060708090a0b0c"),
        h("0102030405060708090a0b0c0d0e0f10") + bytes(8),
        b"",
    )
    assert made.hex() == whoareyou
    assert discv5_read(id_b.hex(), whoareyou).startswith("1 0102030405060708090a0b0c ")


self_check()

# RLPx.


def concat_kdf(secret, length):
    out, counter = b"", 1
    while len(out) < length:
        out += hashlib.sha256(counter.to_bytes(4, "big") + secret).digest()
        counter += 1
    return out[:length]


def public65(public64):
    return coincurve.PublicKey(b"\x04" + public64)


def ecdh_x(sk, public):
    return public.multiply(sk).format(compressed=True)[1:]


def ecies_keys(secret):
    keys = concat_kdf(secret, 32)
    return keys[:16], hashlib.sha256(keys[16:]).digest()


def ecies_enc_raw(public64, r, iv, shared, message):
    enc_key, mac_key = ecies_keys(ecdh_x(r, public65(public64)))
    c = aes_ctr(enc_key, iv, message)
    d = hmac.new(mac_key, iv + c + shared, hashlib.sha256).digest()
    return coincurve.PrivateKey(r).public_key.format(compressed=False) + iv + c + d


def ecies_dec_raw(sk, shared, data):
    if len(data) < 65 + 16 + 32:
        raise MalformedError("short")
    if data[0] != 4:
        raise MalformedError("not an uncompressed key")
    enc_key, mac_key = ecies_keys(ecdh_x(sk, coincurve.PublicKey(data[:65])))
    iv, c, d = data[65:81], data[81:-32], data[-32:]
    if hmac.new(mac_key, iv + c + shared, hashlib.sha256).digest() != d:
        raise MalformedError("tag")
    return aes_ctr(enc_key, iv, c)


def ecies_enc(public64, r, iv, shared, message):
    return tohex(ecies_enc_raw(*map(unhex, (public64, r, iv, shared, message))))


def ecies_dec(sk, shared, data):
    return tohex(ecies_dec_raw(unhex(sk), unhex(shared), unhex(data)))


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b, strict=False))


class Mac:
    """One direction's MAC: a running Keccak-256 state."""

    def __init__(self, secret, seed):
        self.secret = secret
        self.data = seed

    def update(self, data):
        self.data += data

    def digest(self):
        return keccak256(self.data)[:16]

    def header(self, ciphertext):
        self.update(xor(aes_block(self.secret, self.digest()), ciphertext))
        return self.digest()

    def frame(self, ciphertext):
        self.update(ciphertext)
        seed = self.digest()
        self.update(xor(aes_block(self.secret, seed), seed))
        return self.digest()


def rlpx_session(initiator, eph, inonce, rnonce, auth, ack, frames):
    eph, inonce, rnonce, auth, ack = map(unhex, (eph, inonce, rnonce, auth, ack))
    shared = keccak256(eph + keccak256(rnonce + inonce))
    aes_secret = keccak256(eph + shared)
    mac_secret = keccak256(eph + aes_secret)
    if initiator == "1":
        egress = Mac(mac_secret, xor(mac_secret, rnonce) + auth)
    else:
        egress = Mac(mac_secret, xor(mac_secret, inonce) + ack)
    stream = Cipher(algorithms.AES(aes_secret), modes.CTR(bytes(16))).encryptor()
    out = b""
    for word in frames.split(","):
        data = unhex(word)
        header = len(data).to_bytes(3, "big") + bytes([0xC2, 0x80, 0x80]) + bytes(10)
        header_ct = stream.update(header)
        out += header_ct + egress.header(header_ct)
        frame_ct = stream.update(data + bytes(-len(data) % 16))
        out += frame_ct + egress.frame(frame_ct)
    return f"{aes_secret.hex()} {mac_secret.hex()} {tohex(out)}"


def rlpx_auth(sk, packet):
    """The recipient's reading of auth: static key, nonce, version, ephemeral key."""
    sk, packet = unhex(sk), unhex(packet)
    if len(packet) < 2 or int.from_bytes(packet[:2], "big") != len(packet) - 2:
        raise MalformedError("size")
    body = ecies_dec_raw(sk, packet[:2], packet[2:])
    items = rlp.decode(body, strict=False)
    if not isinstance(items, list) or len(items) < 4:
        raise MalformedError("fields")
    signature, public, nonce = sized(items[0], 65), sized(items[1], 64), sized(items[2], 32)
    version = scalar(items[3])
    token = xor(ecdh_x(sk, public65(public)), nonce)
    if signature[64] > 1:
        raise MalformedError("recovery id")
    eph = coincurve.PublicKey.from_signature_and_message(signature, token, hasher=None)
    return f"{public.hex()} {nonce.hex()} {version} {eph.format(compressed=False)[1:].hex()}"


HANDLERS = {
    "discv5_read": discv5_read,
    "discv5_write": discv5_write,
    "discv5_keys": discv5_keys,
    "discv5_idsign": discv5_idsign,
    "discv5_idverify": discv5_idverify,
    "discv5_gcm": discv5_gcm,
    "discv5_msg": discv5_msg,
    "discv5_distance": discv5_distance,
    "ecies_enc": ecies_enc,
    "ecies_dec": ecies_dec,
    "rlpx_session": rlpx_session,
    "rlpx_auth": rlpx_auth,
}

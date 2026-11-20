"""References for the decoders driver: the TLS 1.3 handshake as QUIC carries it."""

# tls_message <hash length> <hex>   One handshake message by a reader written from RFC 8446
#                                   section 4, and the bytes after it.
# tls_payload <form> <type> <hex>   The payload of one extension, RFC 8446 section 4.2.
# tls_schedule <shared> <hello> <server>   The secrets of RFC 8446 section 7.1, by HMAC and
#                                   the HKDF of `cryptography`.
# tls_finished <secret> <transcript>       The verify data of section 4.4.4.
# tls_transcript <message>...       The transcript hash of section 4.4.1, with its retry rule.
# tls_verify_input <server> <digest>       The content that CertificateVerify signs.
# tls_share <group> <secret>        The key share of a private key, by `cryptography`.
# tls_shared <group> <secret> <peer>       The shared secret of section 7.4.
# tls_schedule_of <shared> <n> <m> <message>...   The traffic secrets and both Finished values
#                                   of a handshake, from its messages in order.
# tls_sign_check <secret> <content> <signature>   Whether `cryptography` verifies the signature
#                                   under the public key of the secret.
# tls_sign <secret> <content>       The public key of a secret as SPKI, and a signature.
# tls_allowed <message> <type>      Whether a message may carry an extension type, by the table
#                                   of RFC 8446 section 4.2.
# tls_peer                          A new libp2p certificate: its number, the certificate, its
#                                   signing key, its peer ID, and the time now.
# tls_new <role> <peer> <suites> <groups> <params>   An aioquic TLS context with that
#                                   certificate; a client answers with its ClientHello.
# tls_feed <context> <level> <hex>  The messages that the context sends after one message.
# tls_secrets <context>             Its four traffic secrets, and whether it has finished.

import datetime
import hashlib
import hmac
import ssl
import struct
import time

import coincurve
from aioquic import tls
from aioquic.buffer import Buffer
from cryptography import x509
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, x25519
from cryptography.hazmat.primitives.kdf.hkdf import HKDFExpand
from cryptography.x509.oid import NameOID
from decoders_util import tohex, unhex


class RefusedError(Exception):
    """The bytes are not what the text accepts."""


def x(data):
    return "x" + bytes(data).hex()


# The presentation language, RFC 8446 section 3.


class Reader:
    def __init__(self, data):
        self.data = data
        self.pos = 0

    def take(self, count):
        if self.pos + count > len(self.data):
            raise RefusedError("a field ends early")
        self.pos += count
        return self.data[self.pos - count : self.pos]

    def uint(self, width):
        return int.from_bytes(self.take(width), "big")

    def vector(self, width, low, high):
        """A vector of `low` to `high` bytes behind a length of `width` bytes, section 3.4."""
        size = self.uint(width)
        if not low <= size <= high:
            raise RefusedError("a vector outside its bounds")
        return self.take(size)

    def end(self):
        if self.pos != len(self.data):
            raise RefusedError("bytes after the last field")


def items(data, read):
    """The entries of a vector, which must fill it."""
    reader, out = Reader(data), []
    while reader.pos < len(data):
        out.append(read(reader))
    return out


def extensions(reader, low):
    """An extension block, section 4.2: no type twice."""

    def one(r):
        kind = r.uint(2)
        return kind, r.vector(2, 0, 65535)

    block = items(reader.vector(2, low, 65535), one)
    kinds = [kind for kind, _ in block]
    if len(set(kinds)) != len(kinds):
        raise RefusedError("an extension type twice")
    return "[" + ",".join(f"{kind}={x(data)}" for kind, data in block) + "]"


def certificate_entry(reader):
    data = reader.vector(3, 1, 2**24 - 1)
    return f"{x(data)}/{extensions(reader, 0)}"


def read_body(kind, body, hash_length):
    """The body of a message by its type, sections 4.1.2 to 4.4.4."""
    r = Reader(body)
    if kind == 1:
        if r.uint(2) != 0x0303:
            raise RefusedError("legacy_version")
        random, session = r.take(32), r.vector(1, 0, 32)
        suites = items(r.vector(2, 2, 65534), lambda s: str(s.uint(2)))
        if r.take(2) != b"\x01\x00":
            raise RefusedError("legacy_compression_methods")
        text = f"ch:{x(random)}:{x(session)}:[{','.join(suites)}]:{extensions(r, 8)}"
    elif kind == 2:
        if r.uint(2) != 0x0303:
            raise RefusedError("legacy_version")
        random, session, suite = r.take(32), r.vector(1, 0, 32), r.uint(2)
        if r.uint(1) != 0:
            raise RefusedError("legacy_compression_method")
        text = f"sh:{x(random)}:{x(session)}:{suite}:{extensions(r, 6)}"
    elif kind == 8:
        text = f"ee:{extensions(r, 0)}"
    elif kind == 13:
        context = r.vector(1, 0, 255)
        text = f"cr:{x(context)}:{extensions(r, 2)}"
    elif kind == 11:
        context = r.vector(1, 0, 255)
        entries = items(r.vector(3, 0, 2**24 - 1), certificate_entry)
        text = f"ct:{x(context)}:[{','.join(entries)}]"
    elif kind == 15:
        algorithm = r.uint(2)
        text = f"cv:{algorithm}:{x(r.vector(2, 0, 65535))}"
    elif kind == 20:
        text = f"fin:{x(r.take(hash_length))}"
    else:
        raise RefusedError("a handshake type that the codec does not read")
    r.end()
    return text


def tls_message(hash_length, data):
    data = unhex(data)
    # The envelope, section 4: a type, a length of three bytes, the body.
    if len(data) < 4:
        return "error:truncated"
    size = int.from_bytes(data[1:4], "big")
    if len(data) < 4 + size:
        return "error:truncated"
    try:
        text = read_body(data[0], data[4 : 4 + size], int(hash_length))
    except RefusedError:
        return "error"
    return f"{text} {tohex(data[4 + size :])}"


def u16s(reader, width, low, high):
    values = items(reader.vector(width, low, high), lambda r: str(r.uint(2)))
    return "[" + ",".join(values) + "]"


def key_share(reader):
    group = reader.uint(2)
    return f"{group}={x(reader.vector(2, 1, 65535))}"


# The extension type of each form, and its reader.
FORMS = {
    "supportedVersions": (43, lambda r: "sv:" + u16s(r, 1, 2, 254)),
    "selectedVersion": (43, lambda r: f"selv:{r.uint(2)}"),
    "supportedGroups": (10, lambda r: "sg:" + u16s(r, 2, 2, 65535)),
    "signatureAlgorithms": (13, lambda r: "sa:" + u16s(r, 2, 2, 65534)),
    "clientKeyShare": (
        51,
        lambda r: "cks:[" + ",".join(items(r.vector(2, 0, 65535), key_share)) + "]",
    ),
    "serverKeyShare": (51, lambda r: "sks:" + key_share(r)),
    "retryKeyShare": (51, lambda r: f"rks:{r.uint(2)}"),
    "alpn": (
        16,
        lambda r: (
            "alpn:["
            + ",".join(items(r.vector(2, 2, 65535), lambda n: x(n.vector(1, 1, 255))))
            + "]"
        ),
    ),
    "quicTransportParameters": (57, lambda r: "qtp:" + x(r.take(len(r.data)))),
}


def tls_payload(form, kind, data):
    expected, read = FORMS[form]
    if int(kind) != expected:
        return "error"
    reader = Reader(unhex(data))
    try:
        text = read(reader)
        reader.end()
    except RefusedError:
        return "error"
    return text


# The key schedule, RFC 8446 section 7.1, for SHA-256.


def extract(salt, key):
    return hmac.new(salt, key, hashlib.sha256).digest()


def expand_label(secret, label, context, length):
    """HKDF-Expand-Label, with the HkdfLabel structure of section 7.1."""
    full = b"tls13 " + label
    info = struct.pack(">H", length) + bytes([len(full)]) + full + bytes([len(context)]) + context
    return HKDFExpand(hashes.SHA256(), length, info).derive(secret)


def derive(secret, label, messages):
    return expand_label(secret, label, hashlib.sha256(messages).digest(), 32)


def schedule(shared, hello, server):
    zeros = bytes(32)
    early = extract(zeros, zeros)
    handshake = extract(derive(early, b"derived", b""), shared)
    master = extract(derive(handshake, b"derived", b""), zeros)
    return [
        early,
        handshake,
        master,
        derive(handshake, b"c hs traffic", hello),
        derive(handshake, b"s hs traffic", hello),
        derive(master, b"c ap traffic", server),
        derive(master, b"s ap traffic", server),
    ]


def tls_schedule(shared, hello, server):
    return " ".join(s.hex() for s in schedule(unhex(shared), unhex(hello), unhex(server)))


def tls_schedule_of(shared, hello_count, server_count, *messages):
    """The secrets and both Finished values of a handshake, from its messages in order.

    The first `hello_count` messages end with ServerHello.
    The first `server_count` messages end with the Finished of the server.
    The last message is the Finished of the client.
    """
    messages = [unhex(m) for m in messages]
    hello = transcript_bytes(messages[: int(hello_count)])
    server = transcript_bytes(messages[: int(server_count)])
    secrets = schedule(unhex(shared), hello, server)
    finished = [
        finished_of(secrets[4], transcript_bytes(messages[: int(server_count) - 1])),
        finished_of(secrets[3], transcript_bytes(messages[:-1])),
    ]
    return " ".join(s.hex() for s in secrets[3:] + finished)


def finished_of(secret, transcript):
    key = expand_label(secret, b"finished", b"", 32)
    return hmac.new(key, hashlib.sha256(transcript).digest(), hashlib.sha256).digest()


def tls_finished(secret, transcript):
    key = expand_label(unhex(secret), b"finished", b"", 32)
    digest = hashlib.sha256(unhex(transcript)).digest()
    return hmac.new(key, digest, hashlib.sha256).hexdigest()


# The random of a ServerHello that is a HelloRetryRequest, section 4.1.3.
RETRY_RANDOM = hashlib.sha256(b"HelloRetryRequest").digest()


def is_retry(message):
    return message[0] == 2 and message[6:38] == RETRY_RANDOM


def transcript_bytes(messages):
    """The bytes that the transcript hash covers, section 4.4.1.

    A HelloRetryRequest must follow one ClientHello, once; the hello gives way to its hash.
    """
    out, retried = b"", False
    for position, message in enumerate(messages):
        if tls_message("32", message.hex()).split(" ")[-1] != "-":
            raise RefusedError("not one complete message")
        if is_retry(message):
            if retried or position != 1 or messages[0][0] != 1:
                raise RefusedError("a retry out of place")
            out = b"\xfe\x00\x00\x20" + hashlib.sha256(out).digest()
            retried = True
        out += message
    return out


def tls_transcript(*messages):
    try:
        return hashlib.sha256(transcript_bytes([unhex(m) for m in messages])).hexdigest()
    except RefusedError:
        return "error"


def tls_verify_input(server, digest):
    role = b"server" if server == "1" else b"client"
    return tohex(b" " * 64 + b"TLS 1.3, " + role + b" CertificateVerify\x00" + unhex(digest))


# The groups and the signature, sections 4.2.8.2, 7.4 and 4.4.3.


def p256_key(secret):
    return ec.derive_private_key(int.from_bytes(secret, "big"), ec.SECP256R1())


def tls_share(group, secret):
    secret = unhex(secret)
    if group == "29":
        key = x25519.X25519PrivateKey.from_private_bytes(secret).public_key()
        return key.public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw).hex()
    point = p256_key(secret).public_key()
    return point.public_bytes(
        serialization.Encoding.X962, serialization.PublicFormat.UncompressedPoint
    ).hex()


def tls_shared(group, secret, peer):
    secret, peer = unhex(secret), unhex(peer)
    if group == "29":
        if len(peer) != 32:
            return "error"
        key = x25519.X25519PrivateKey.from_private_bytes(secret)
        try:
            return key.exchange(x25519.X25519PublicKey.from_public_bytes(peer)).hex()
        except ValueError:
            # The all-zero output of a point of small order, RFC 7748 section 6.1.
            return "error"
    if len(peer) != 65 or peer[0] != 4:
        return "error"
    try:
        point = ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256R1(), peer)
    except ValueError:
        return "error"
    return p256_key(secret).exchange(ec.ECDH(), point).hex()


def tls_sign_check(secret, content, signature):
    key = p256_key(unhex(secret)).public_key()
    try:
        key.verify(unhex(signature), unhex(content), ec.ECDSA(hashes.SHA256()))
    except Exception:
        return "0"
    return "1"


def tls_sign(secret, content):
    key = p256_key(unhex(secret))
    spki = key.public_key().public_bytes(
        serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo
    )
    return f"{spki.hex()} {key.sign(unhex(content), ec.ECDSA(hashes.SHA256())).hex()}"


# RFC 8446 section 4.2: the messages in which each extension may appear, by its name there.
# The numbers are those of the ExtensionType enumeration of the same section.
# quic_transport_parameters (57) is from RFC 9001 section 8.2.
PLACEMENT = {
    0: "CH, EE",  # server_name
    1: "CH, EE",  # max_fragment_length
    5: "CH, CR, CT",  # status_request
    10: "CH, EE",  # supported_groups
    13: "CH, CR",  # signature_algorithms
    14: "CH, EE",  # use_srtp
    15: "CH, EE",  # heartbeat
    16: "CH, EE",  # application_layer_protocol_negotiation
    18: "CH, CR, CT",  # signed_certificate_timestamp
    19: "CH, EE",  # client_certificate_type
    20: "CH, EE",  # server_certificate_type
    21: "CH",  # padding
    41: "CH, SH",  # pre_shared_key
    42: "CH, EE, NST",  # early_data
    43: "CH, SH, HRR",  # supported_versions
    44: "CH, HRR",  # cookie
    45: "CH",  # psk_key_exchange_modes
    47: "CH, CR",  # certificate_authorities
    48: "CR",  # oid_filters
    49: "CH",  # post_handshake_auth
    50: "CH, CR",  # signature_algorithms_cert
    51: "CH, SH, HRR",  # key_share
    57: "CH, EE",  # quic_transport_parameters
}


def tls_allowed(message, kind):
    """An extension that the table does not list is not judged here, so it may appear."""
    listed = PLACEMENT.get(int(kind))
    return "1" if listed is None or message in listed.split(", ") else "0"


# A libp2p certificate, and an aioquic context that holds one.

PEERS = []
CONTEXTS = []


def der(tag, content):
    size = len(content)
    head = bytes([size]) if size < 128 else bytes([0x81, size])
    return bytes([tag]) + head + content


def tls_peer():
    """A certificate as libp2p TLS asks: a P-256 key, and the host key signed into an extension."""
    key = ec.generate_private_key(ec.SECP256R1())
    host = coincurve.PrivateKey()
    spki = key.public_key().public_bytes(
        serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo
    )
    # The public key message of the peer ID specification: a secp256k1 key, compressed.
    public = b"\x08\x02\x12\x21" + host.public_key.format(compressed=True)
    signature = host.sign(b"libp2p-tls-handshake:" + spki)
    signed_key = der(0x30, der(4, public) + der(4, signature))
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, "libp2p")])
    now = int(time.time())
    certificate = (
        x509.CertificateBuilder()
        .subject_name(name)
        .issuer_name(name)
        .public_key(key.public_key())
        .serial_number(x509.random_serial_number())
        .not_valid_before(datetime.datetime.fromtimestamp(now - 3600, tz=datetime.UTC))
        .not_valid_after(datetime.datetime.fromtimestamp(now + 86400, tz=datetime.UTC))
        .add_extension(
            x509.UnrecognizedExtension(x509.ObjectIdentifier("1.3.6.1.4.1.53594.1.1"), signed_key),
            critical=True,
        )
        .sign(key, hashes.SHA256())
    )
    PEERS.append((certificate, key))
    secret = key.private_numbers().private_value.to_bytes(32, "big")
    encoded = certificate.public_bytes(serialization.Encoding.DER)
    # A key message of 42 bytes at most is its own peer ID, behind the identity multihash.
    peer_id = bytes([0, len(public)]) + public
    return f"{len(PEERS) - 1} {encoded.hex()} {secret.hex()} {peer_id.hex()} {now}"


LEVELS = {"i": tls.Epoch.INITIAL, "h": tls.Epoch.HANDSHAKE, "a": tls.Epoch.ONE_RTT}


def split(level, data):
    """The handshake messages of a flight, each behind the letter of its level."""
    out, pos = [], 0
    while pos < len(data):
        size = 4 + int.from_bytes(data[pos + 1 : pos + 4], "big")
        out.append(f"{level}:{data[pos : pos + size].hex()}")
        pos += size
    return out


def drive(context, data):
    buffers = {epoch: Buffer(capacity=16384) for epoch in LEVELS.values()}
    context.handle_message(data, buffers)
    out = []
    for level, epoch in LEVELS.items():
        out += split(level, buffers[epoch].data)
    return " ".join(out) or "-"


def tls_new(role, peer, suites, groups, params):
    certificate, key = PEERS[int(peer)]
    context = tls.Context(
        is_client=role == "client",
        alpn_protocols=["libp2p"],
        cipher_suites=[tls.CipherSuite(int(s)) for s in suites.split(",")],
        # The certificate of a libp2p peer is self-signed, and the peer ID authenticates it.
        verify_mode=ssl.CERT_NONE,
    )
    context.certificate = certificate
    context.certificate_private_key = key
    context._supported_groups = [tls.Group(int(g)) for g in groups.split(",")]
    context._request_client_certificate = True
    context.handshake_extensions = [(57, unhex(params))]
    secrets = {}
    context.update_traffic_key_cb = lambda direction, epoch, suite, secret: secrets.update(
        {(direction, epoch): secret}
    )
    CONTEXTS.append((context, secrets))
    number = len(CONTEXTS) - 1
    if role == "client":
        return f"{number} {drive(context, b'')}"
    return str(number)


def tls_feed(context, level, data):
    del level
    return drive(CONTEXTS[int(context)][0], unhex(data))


def tls_secrets(context):
    """The traffic secrets in the order client, server, for the handshake and for 1-RTT."""
    context, secrets = CONTEXTS[int(context)]
    sends = tls.Direction.ENCRYPT if context._is_client else tls.Direction.DECRYPT
    takes = tls.Direction.DECRYPT if context._is_client else tls.Direction.ENCRYPT
    order = [
        (sends, tls.Epoch.HANDSHAKE),
        (takes, tls.Epoch.HANDSHAKE),
        (sends, tls.Epoch.ONE_RTT),
        (takes, tls.Epoch.ONE_RTT),
    ]
    done = context.state in (tls.State.CLIENT_POST_HANDSHAKE, tls.State.SERVER_POST_HANDSHAKE)
    peer = context._peer_certificate
    seen = peer.public_bytes(serialization.Encoding.DER).hex() if peer else "-"
    words = [secrets[key].hex() if key in secrets else "-" for key in order]
    return " ".join([*words, "1" if done else "0", seen])


# RFC 8448, section 3: the handshake secret of the simple 1-RTT handshake.
VECTOR_SHARED = "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"
VECTOR_HANDSHAKE = "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"
assert schedule(bytes.fromhex(VECTOR_SHARED), b"", b"")[1].hex() == VECTOR_HANDSHAKE

HANDLERS = {
    "tls_message": tls_message,
    "tls_payload": tls_payload,
    "tls_schedule": tls_schedule,
    "tls_finished": tls_finished,
    "tls_transcript": tls_transcript,
    "tls_verify_input": tls_verify_input,
    "tls_share": tls_share,
    "tls_shared": tls_shared,
    "tls_schedule_of": tls_schedule_of,
    "tls_sign_check": tls_sign_check,
    "tls_sign": tls_sign,
    "tls_allowed": tls_allowed,
    "tls_peer": tls_peer,
    "tls_new": tls_new,
    "tls_feed": tls_feed,
    "tls_secrets": tls_secrets,
}

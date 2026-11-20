"""References for the decoders driver: libp2p TLS certificates, multistream, yamux, mplex."""

# cert_build <15 words>     A certificate from a description: its DER, then its facts.
# cert_facts <der>          The facts of any bytes, read as RFC 5280 and libp2p TLS say.
# sig_der <r> <s>           The DER signature of two scalars, by `cryptography`.
# sig_scalars <der>         The scalars of a strict DER signature, or error.
# p256_verify <spki> <message> <signature>   1 or 0, by OpenSSL.
# yamux <bytes>             The frame at the start, from the yamux text, and what is left.
# mplex <bytes>             The frame at the start, from the mplex text, and what is left.
# mss <bytes>               The multistream-select message at the start, and what is left.
# x509_time <tag> <text>   The seconds from 1970 of a UTCTime or a GeneralizedTime.
# p256_sign <key> <message>   The key as a SubjectPublicKeyInfo, and a signature.
#
# The facts of a certificate are words `name=value`:
#   rfc      `ok`, or the rule of RFC 5280 or X.690 that the bytes break.
#   subset   `-`, or what RFC 5280 allows and EthLib documents that it does not read:
#            `value-tag`, `validity-inverted` or `compressed-point`.
#   crypt    `ok` or `error`: whether `cryptography` reads the bytes.
#   nb, na   The validity, in seconds from 1970.
#   uid      Two bits: the issuer and the subject unique identifiers are present.
#   alg      1 when the signature is ecdsa-with-SHA256 without parameters under a P-256 key.
#   selfsig  1 when the signature verifies under the key of the certificate.
#   ext      `ok`, `missing`, `critical`, `twice` or `malformed`: the libp2p extension.
#   host     `k256`, `p256`, `unsupported` or `badkey`: the host key.
#   canon    1 when the host key is the deterministic protobuf of the peer ID text.
#   hostsig  1 when the host key signed `libp2p-tls-handshake:` and the certificate key.
#   peer     The peer ID of the host key, `-` without one.

import datetime
import hashlib
import struct
import warnings

from cryptography import x509
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, ed25519, rsa, utils
from decoders_util import tohex, unhex

LIBP2P_OID = "1.3.6.1.4.1.53594.1.1"
ECDSA_SHA256 = "1.2.840.10045.4.3.2"
ECDSA_SHA384 = "1.2.840.10045.4.3.3"
ED25519_OID = "1.3.101.112"
EC_PUBLIC_KEY = "1.2.840.10045.2.1"
PRIME256V1 = "1.2.840.10045.3.1.7"
PREFIX = b"libp2p-tls-handshake:"
K256_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
P256_ORDER = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
EPOCH = datetime.datetime(1970, 1, 1)

# One RSA key for every RSA host: generating one per case would take most of the run.
RSA_KEY = rsa.generate_private_key(public_exponent=65537, key_size=2048)


class RefusedError(Exception):
    """The bytes break a rule, named by the first argument."""


# DER, written: X.690 sections 8.1 and 10.1.


def tlv(tag, content):
    size = len(content)
    if size < 128:
        return bytes([tag, size]) + content
    octets = size.to_bytes((size.bit_length() + 7) // 8, "big")
    return bytes([tag, 0x80 | len(octets)]) + octets + content


def oid_content(dotted):
    parts = [int(part) for part in dotted.split(".")]
    out = bytes([parts[0] * 40 + parts[1]])
    for part in parts[2:]:
        chunk = [part & 0x7F]
        part >>= 7
        while part:
            chunk.append(0x80 | (part & 0x7F))
            part >>= 7
        out += bytes(reversed(chunk))
    return out


def oid(dotted):
    return tlv(6, oid_content(dotted))


# DER, read: one value of a low tag number with a definite length in its shortest form.


def der_read(data):
    if len(data) < 2:
        raise RefusedError("der-truncated")
    tag, first = data[0], data[1]
    if tag & 0x1F == 0x1F or tag == 0:
        raise RefusedError("der-tag")
    if first < 128:
        size, header = first, 2
    else:
        count = first - 128
        if count == 0 or count == 127 or len(data) < 2 + count:
            raise RefusedError("der-length")
        size = int.from_bytes(data[2 : 2 + count], "big")
        if data[2] == 0 or size < 128:
            raise RefusedError("der-length")
        header = 2 + count
    if len(data) < header + size:
        raise RefusedError("der-truncated")
    end = header + size
    return (tag, data[header:end], data[:end]), data[end:]


def der_children(content):
    out = []
    while content:
        value, content = der_read(content)
        out.append(value)
    return out


def der_exact(tag, data, rule):
    value, rest = der_read(data)
    if value[0] != tag or rest:
        raise RefusedError(rule)
    return value


def der_fields(tag, value, rule):
    if value[0] != tag:
        raise RefusedError(rule)
    return der_children(value[1])


def der_integer(value, rule):
    tag, content, _ = value
    if tag != 2 or not content:
        raise RefusedError(rule)
    if len(content) > 1 and (
        (content[0] == 0 and content[1] < 128) or (content[0] == 255 and content[1] >= 128)
    ):
        raise RefusedError(rule)
    return int.from_bytes(content, "big", signed=True)


def der_oid(value, rule):
    tag, content, _ = value
    if tag != 6 or not content or content[-1] >= 128:
        raise RefusedError(rule)
    start = True
    for byte in content:
        if start and byte == 0x80:
            raise RefusedError(rule)
        start = byte < 128
    return content


def der_bits(content, rule):
    # X.690 section 11.2: the unused bits are zero, and at most seven.
    if not content or content[0] > 7:
        raise RefusedError(rule)
    if len(content) == 1 and content[0] != 0:
        raise RefusedError(rule)
    if len(content) > 1 and content[-1] & ((1 << content[0]) - 1):
        raise RefusedError(rule)


def der_octet_aligned(value, rule):
    # A signature and a key are octets, so their BIT STRING has no unused bit.
    tag, content, _ = value
    if tag != 3 or not content or content[0] != 0:
        raise RefusedError(rule)
    return content[1:]


# The certificate of RFC 5280 section 4.1, read with no leniency.

PRINTABLE = set(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789 '()+,-./:=?")
# The tags of a value that EthLib's reader of a name knows, from the docstring of its validator.
KNOWN_VALUE_TAGS = {1, 2, 3, 4, 5, 6, 12, 19, 22, 28, 30, 48, 49}


def scalar(code):
    return code <= 0x10FFFF and not 0xD800 <= code <= 0xDFFF


def check_value(value, facts):
    # The content of a value of any type: X.690 sections 8.2 to 8.23, as far as they go here.
    #
    # A value of a tag outside EthLib's documented subset is taken whole, and noted.
    tag, content, _ = value
    ok = True
    if tag not in KNOWN_VALUE_TAGS:
        facts["subset"] = "value-tag"
    elif tag == 1:
        ok = content in (b"\x00", b"\xff")
    elif tag == 2:
        der_integer(value, "value")
    elif tag == 3:
        der_bits(content, "value")
    elif tag == 5:
        ok = not content
    elif tag == 6:
        der_oid(value, "value")
    elif tag == 12:
        try:
            content.decode("utf-8")
        except UnicodeDecodeError:
            ok = False
    elif tag == 19:
        ok = all(byte in PRINTABLE for byte in content)
    elif tag == 22:
        ok = all(byte < 128 for byte in content)
    elif tag in (28, 30):
        width = 4 if tag == 28 else 2
        ok = len(content) % width == 0 and all(
            scalar(int.from_bytes(content[i : i + width], "big"))
            for i in range(0, len(content), width)
        )
    elif tag in (48, 49):
        values = der_children(content)
        if tag == 49 and [v[2] for v in values] != sorted(v[2] for v in values):
            ok = False
        for inner in values:
            check_value(inner, facts)
    if not ok:
        raise RefusedError("value")


def read_algorithm(value, rule, facts):
    # RFC 5280 section 4.1.1.2: an object identifier, and parameters of any type or none.
    fields = der_fields(0x30, value, rule)
    if len(fields) not in (1, 2):
        raise RefusedError(rule)
    if len(fields) == 2:
        check_value(fields[1], facts)
    return der_oid(fields[0], rule), (fields[1] if len(fields) == 2 else None)


def read_name(value, facts):
    for rdn in der_fields(0x30, value, "name"):
        attributes = der_fields(0x31, rdn, "name")
        if not attributes:
            raise RefusedError("name-empty-set")
        # X.690 section 11.6: the values of a SET OF are in the order of their encodings.
        if [a[2] for a in attributes] != sorted(a[2] for a in attributes):
            raise RefusedError("name-set-order")
        for attribute in attributes:
            fields = der_fields(0x30, attribute, "name")
            if len(fields) != 2:
                raise RefusedError("name")
            der_oid(fields[0], "name")
            check_value(fields[1], facts)


def read_time(value):
    # RFC 5280 sections 4.1.2.5.1 and 4.1.2.5.2: YYMMDDHHMMSSZ and YYYYMMDDHHMMSSZ.
    tag, content, _ = value
    if tag not in (0x17, 0x18):
        raise RefusedError("time-tag")
    digits = 2 if tag == 0x17 else 4
    if len(content) != digits + 11 or content[-1:] != b"Z":
        raise RefusedError("time-form")
    if not all(48 <= byte <= 57 for byte in content[:-1]):
        raise RefusedError("time-form")
    text = content.decode("ascii")
    year = int(text[:digits])
    if digits == 2:
        year += 2000 if year < 50 else 1900
    rest = text[digits:]
    month, day, hour, minute, second = (int(rest[i : i + 2]) for i in range(0, 10, 2))
    try:
        moment = datetime.datetime(year, month, day, hour, minute, second)
    except ValueError:
        raise RefusedError("time-value") from None
    return (moment - EPOCH) // datetime.timedelta(seconds=1)


def read_extension(value):
    fields = der_fields(0x30, value, "extension")
    if len(fields) == 2:
        critical = False
    elif len(fields) == 3:
        # X.690 section 11.5: a value equal to its default is not written.
        if fields[1][0] != 1 or fields[1][1] != b"\xff":
            raise RefusedError("extension-critical")
        critical = True
    else:
        raise RefusedError("extension")
    if fields[-1][0] != 4:
        raise RefusedError("extension")
    return der_oid(fields[0], "extension"), critical, fields[-1][1]


def read_certificate(der):
    facts = {"subset": "-"}
    outer = der_exact(0x30, der, "certificate")
    parts = der_children(outer[1])
    if len(parts) != 3:
        raise RefusedError("certificate")
    tbs, algorithm, signature = parts
    facts["sigalg"] = read_algorithm(algorithm, "algorithm", facts)
    facts["signature"] = der_octet_aligned(signature, "bits")
    fields = der_fields(0x30, tbs, "tbs")
    version = 0
    if fields and fields[0][0] == 0xA0:
        version = der_integer(der_exact(2, fields[0][1], "version"), "version")
        # A version of 0 is the default, so DER does not write it; RFC 5280 knows 1 and 2.
        if version not in (1, 2):
            raise RefusedError("version")
        fields = fields[1:]
    if len(fields) < 6:
        raise RefusedError("tbs")
    serial, inner, issuer, validity, subject, spki = fields[:6]
    der_integer(serial, "serial")
    read_algorithm(inner, "algorithm", facts)
    if inner[2] != algorithm[2]:
        # RFC 5280 section 4.1.1.2: the two fields hold the same algorithm identifier.
        raise RefusedError("algorithm-mismatch")
    read_name(issuer, facts)
    read_name(subject, facts)
    times = der_fields(0x30, validity, "validity")
    if len(times) != 2:
        raise RefusedError("validity")
    facts["nb"], facts["na"] = read_time(times[0]), read_time(times[1])
    key_fields = der_fields(0x30, spki, "spki")
    if len(key_fields) != 2:
        raise RefusedError("spki")
    facts["keyalg"] = read_algorithm(key_fields[0], "spki", facts)
    facts["key"] = der_octet_aligned(key_fields[1], "bits")
    tail = fields[6:]
    facts["uid"] = ""
    for tag in (0x81, 0x82):
        present = bool(tail) and tail[0][0] == tag
        if present:
            if version < 1:
                raise RefusedError("unique-id-version")
            der_bits(tail[0][1], "unique-id")
            tail = tail[1:]
        facts["uid"] += "1" if present else "0"
    extensions = []
    if tail:
        if len(tail) != 1 or tail[0][0] != 0xA3:
            raise RefusedError("tbs")
        if version != 2:
            raise RefusedError("extensions-version")
        sequence = der_exact(0x30, tail[0][1], "extensions")
        extensions = [read_extension(item) for item in der_children(sequence[1])]
        if not extensions:
            raise RefusedError("extensions-empty")
        # RFC 5280 section 4.2: no extension occurs twice.
        if len({name for name, _, _ in extensions}) != len(extensions):
            raise RefusedError("extension-twice")
    facts.update(tbs=tbs[2], spki=spki[2], extensions=extensions)
    if facts["na"] < facts["nb"] and facts["subset"] == "-":
        facts["subset"] = "validity-inverted"
    return facts


# The public key of the peer ID text: `PublicKey { KeyType Type = 1; bytes Data = 2; }`.


def uvarint(data):
    # A protobuf varint of at most ten bytes, minimal or not.
    value = 0
    for i, byte in enumerate(data[:10]):
        value |= (byte & 0x7F) << (7 * i)
        if byte < 128:
            return value, data[i + 1 :]
    raise RefusedError("key-varint")


def read_public_key(data):
    kind, body, rest = None, None, data
    while rest:
        key, rest = uvarint(rest)
        if key == 0x08:
            kind, rest = uvarint(rest)
        elif key == 0x12:
            size, rest = uvarint(rest)
            if len(rest) < size:
                raise RefusedError("key-truncated")
            body, rest = rest[:size], rest[size:]
        else:
            raise RefusedError("key-field")
    if kind is None or body is None:
        raise RefusedError("key-missing")
    canonical = bytes([0x08, kind, 0x12]) + varint(len(body)) + body if kind < 128 else b""
    return kind, body, data == canonical


def varint(value):
    out = b""
    while value >= 128:
        out += bytes([value & 0x7F | 0x80])
        value >>= 7
    return out + bytes([value])


def strict_scalars(signature, order):
    # RFC 3279 section 2.2.3 in DER: the one encoding of two positive integers below the order.
    r, s = utils.decode_dss_signature(signature)
    if utils.encode_dss_signature(r, s) != signature or not (0 < r < order and 0 < s < order):
        raise ValueError("not a strict signature")
    return r, s


def ecdsa_verifies(public, message, signature, order, low_s):
    try:
        _, s = strict_scalars(signature, order)
        if low_s and s > order // 2:
            return False
        public.verify(signature, message, ec.ECDSA(hashes.SHA256()))
        return True
    except (ValueError, InvalidSignature):
        return False


def peer_id(key):
    # Peer IDs: the identity multihash of a key of at most 42 bytes, else its SHA-256 multihash.
    if len(key) <= 42:
        return bytes([0x00, len(key)]) + key
    return b"\x12\x20" + hashlib.sha256(key).digest()


def host_facts(facts):
    # The libp2p TLS text, "Peer Authentication" and "libp2p Public Key Extension".
    out = {"ext": "ok", "host": "badkey", "canon": "0", "hostsig": "0", "peer": "-"}
    libp2p = oid_content(LIBP2P_OID)
    mine = [e for e in facts["extensions"] if e[0] == libp2p]
    if any(critical and name != libp2p for name, critical, _ in facts["extensions"]):
        out["ext"] = "critical"
        return out
    if len(mine) != 1:
        out["ext"] = "twice" if mine else "missing"
        return out
    try:
        fields = der_fields(0x30, der_exact(0x30, mine[0][2], "signed-key"), "signed-key")
        if len(fields) != 2 or fields[0][0] != 4 or fields[1][0] != 4:
            raise RefusedError("signed-key")
    except RefusedError:
        out["ext"] = "malformed"
        return out
    key, signature = fields[0][1], fields[1][1]
    try:
        kind, body, canonical = read_public_key(key)
    except RefusedError:
        return out
    out["canon"] = "1" if canonical else "0"
    message = PREFIX + facts["spki"]
    public, order, low_s = None, 0, False
    try:
        if kind == 2:
            # Peer IDs, "Secp256k1": the compressed point, and the signature rules of BIP 62.
            if len(body) != 33:
                raise ValueError("not a compressed point")
            public = ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256K1(), body)
            out["host"], order, low_s = "k256", K256_ORDER, True
        elif kind == 3:
            # Peer IDs, "ECDSA": the key is the DER of a SubjectPublicKeyInfo.
            public = serialization.load_der_public_key(body)
            p256 = (
                isinstance(public, ec.EllipticCurvePublicKey) and public.curve.name == "secp256r1"
            )
            out["host"], order = ("p256" if p256 else "unsupported"), P256_ORDER
            # EthLib documents that it reads the uncompressed form of 91 bytes only.
            if p256 and len(body) != 91:
                out["canon"] = "0"
        elif kind in (0, 1):
            out["host"] = "unsupported"
    except Exception:  # Any refusal of the key by `cryptography`: it is not a key.
        return out
    if out["host"] in ("k256", "p256"):
        out["hostsig"] = "1" if ecdsa_verifies(public, message, signature, order, low_s) else "0"
        out["peer"] = tohex(peer_id(key))
    return out


def self_signature(facts):
    # RFC 5758 section 3.2: ecdsa-with-SHA256 has no parameters; RFC 5480 names the curve.
    algorithm = facts["sigalg"] == (oid_content(ECDSA_SHA256), None)
    key_oid, parameter = facts["keyalg"]
    p256 = key_oid == oid_content(EC_PUBLIC_KEY) and parameter is not None
    p256 = p256 and parameter[2] == oid(PRIME256V1)
    verified = False
    try:
        public = serialization.load_der_public_key(facts["spki"])
        if isinstance(public, ec.EllipticCurvePublicKey):
            order = P256_ORDER if p256 else 1 << 600
            verified = ecdsa_verifies(public, facts["tbs"], facts["signature"], order, False)
    except Exception:  # Any refusal of the key by `cryptography`: nothing verifies under it.
        pass
    # EthLib documents that it reads an uncompressed point only.
    if p256 and facts["key"][:1] != b"\x04" and facts["subset"] == "-":
        facts["subset"] = "compressed-point"
    return ("1" if algorithm and p256 else "0"), ("1" if verified else "0")


def crypt_reads(der):
    # Whether `cryptography` reads the certificate, and the validity it reads.
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            cert = x509.load_der_x509_certificate(der)
            aware = EPOCH.replace(tzinfo=datetime.UTC)
            second = datetime.timedelta(seconds=1)
            times = (
                (cert.not_valid_before_utc - aware) // second,
                (cert.not_valid_after_utc - aware) // second,
            )
            _ = (cert.serial_number, cert.issuer, cert.subject, cert.version)
            try:
                _ = list(cert.extensions)
            except x509.DuplicateExtension:
                return "error", None
            except ValueError:
                # The content of an extension that `cryptography` knows: no part of the reading.
                pass
            return "ok", times
    except Exception:
        return "error", None


# The rules of RFC 5280 that `cryptography` does not apply when it reads.
#
# It also reads no certificate of version 2, which the reader above does.
#
# It reads a signature or a key with unused bits, and refuses it when it is used.
CRYPT_LAX = {
    "unique-id-version",
    "extensions-version",
    "extensions-empty",
    "algorithm-mismatch",
    "bits",
}


def cert_facts_of(der):
    crypt, crypt_times = crypt_reads(der)
    try:
        facts = read_certificate(der)
    except RefusedError as refusal:
        rule = refusal.args[0]
        if crypt != "error" and rule not in CRYPT_LAX:
            return f"error the references disagree: cryptography reads, RFC 5280 says {rule}"
        return f"rfc={rule} crypt={crypt}"
    if crypt == "error":
        # `cryptography` reads versions 1 and 3 only, and no parameters of an ECDSA signature.
        #
        # It also reads the parameters of a key by the type that the algorithm gives them.
        parameters = facts["sigalg"][1] is not None
        typed = facts["keyalg"][1] is None or facts["keyalg"][1][0] != 6
        if not (find_version_two(der) or parameters or typed or facts["subset"] == "value-tag"):
            return "error the references disagree: RFC 5280 reads, cryptography does not"
    elif crypt_times != (facts["nb"], facts["na"]):
        return f"error the references disagree on the validity: {crypt_times}"
    alg, selfsig = self_signature(facts)
    host = host_facts(facts)
    words = [
        "rfc=ok",
        f"subset={facts['subset']}",
        f"crypt={crypt}",
        f"nb={facts['nb']}",
        f"na={facts['na']}",
        f"uid={facts['uid']}",
        f"alg={alg}",
        f"selfsig={selfsig}",
    ]
    return " ".join(words + [f"{name}={value}" for name, value in host.items()])


def find_version_two(der):
    # Whether the certificate says version 2: the explicit integer 1 in the first field.
    try:
        tbs = der_children(der_exact(0x30, der, "c")[1])[0]
        first = der_children(tbs[1])[0]
        return first[0] == 0xA0 and first[1] == bytes([2, 1, 1])
    except (RefusedError, IndexError):
        return False


def cert_facts(der):
    return cert_facts_of(unhex(der))


# A certificate from a description.


def private_key(word):
    kind, _, secret = word.partition(":")
    number = int(secret, 16) if secret else 1
    if kind == "p256":
        return ec.derive_private_key(number % (P256_ORDER - 1) + 1, ec.SECP256R1())
    if kind == "k256":
        return ec.derive_private_key(number % (K256_ORDER - 1) + 1, ec.SECP256K1())
    if kind == "p384":
        return ec.derive_private_key(number + 1, ec.SECP384R1())
    if kind == "ed25519":
        return ed25519.Ed25519PrivateKey.from_private_bytes(number.to_bytes(32, "big"))
    if kind == "rsa":
        return RSA_KEY
    raise ValueError("unknown key kind " + kind)


def spki_of(key, compressed=False):
    public = key.public_key()
    der = public.public_bytes(
        serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo
    )
    if compressed and isinstance(public, ec.EllipticCurvePublicKey):
        point = public.public_bytes(
            serialization.Encoding.X962, serialization.PublicFormat.CompressedPoint
        )
        algorithm = der_children(der_exact(0x30, der, "spki")[1])[0][2]
        der = tlv(0x30, algorithm + tlv(3, b"\x00" + point))
    return der


def sign(key, message, variant, digest=None):
    # A signature, and the ways to spoil one that leave it readable.
    if isinstance(key, ed25519.Ed25519PrivateKey):
        signature = key.sign(message)
    elif isinstance(key, rsa.RSAPrivateKey):
        from cryptography.hazmat.primitives.asymmetric import padding

        signature = key.sign(message, padding.PKCS1v15(), hashes.SHA256())
    else:
        order = {"secp256k1": K256_ORDER, "secp256r1": P256_ORDER}.get(key.curve.name)
        signature = key.sign(message, ec.ECDSA(digest or hashes.SHA256()))
        r, s = utils.decode_dss_signature(signature)
        if order:
            # Low by default, as BIP 62 asks of secp256k1; `highs` gives the other one.
            low = min(s, order - s)
            signature = utils.encode_dss_signature(r, order - low if variant == "highs" else low)
        if variant == "pad":
            body = tlv(2, b"\x00" + der_children(signature[2:])[0][1]) + tlv(
                2, der_children(signature[2:])[1][1]
            )
            signature = tlv(0x30, body)
    if variant == "flip":
        signature = signature[:-1] + bytes([signature[-1] ^ 1])
    return signature


ATTRIBUTE = oid("2.5.4.3")
OTHER = oid("2.5.4.10")


def attribute(tag, text, name=ATTRIBUTE):
    return tlv(0x30, name + tlv(tag, text))


NAMES = {
    "empty": b"",
    "cn": tlv(0x31, attribute(12, b"libp2p")),
    "printable": tlv(0x31, attribute(19, b"node 1 (a)")),
    "ia5": tlv(0x31, attribute(22, b"a@b")),
    "bmp": tlv(0x31, attribute(30, b"\x00a\x00b")),
    "universal": tlv(0x31, attribute(28, b"\x00\x00\x00a")),
    "two": tlv(0x31, attribute(12, b"a")) + tlv(0x31, attribute(19, b"b", OTHER)),
    "multi": tlv(0x31, attribute(12, b"a") + attribute(12, b"b")),
    "unsorted": tlv(0x31, attribute(12, b"b") + attribute(12, b"a")),
    # The shorter encoding comes first, whatever the text says.
    "lengths": tlv(0x31, attribute(12, b"b") + attribute(12, b"aa")),
    "unsortedlengths": tlv(0x31, attribute(12, b"aa") + attribute(12, b"b")),
    "emptyset": tlv(0x31, b""),
    "teletex": tlv(0x31, attribute(20, b"a")),
    "numeric": tlv(0x31, attribute(18, b"12")),
    "badprintable": tlv(0x31, attribute(19, b"a@b")),
    "badutf8": tlv(0x31, attribute(12, b"\xff")),
    "badbmp": tlv(0x31, attribute(30, b"\x00")),
    "surrogate": tlv(0x31, attribute(30, b"\xd8\x00")),
}


def host_key_bytes(key, variant):
    # The protobuf of the peer ID text, deterministic unless the variant says otherwise.
    public = key.public_key()
    if isinstance(public, ec.EllipticCurvePublicKey) and public.curve.name == "secp256k1":
        kind = 2
        data = public.public_bytes(
            serialization.Encoding.X962, serialization.PublicFormat.CompressedPoint
        )
    elif isinstance(public, ec.EllipticCurvePublicKey):
        kind, data = 3, spki_of(key, compressed=variant == "compressed")
    elif isinstance(public, ed25519.Ed25519PublicKey):
        kind = 1
        data = public.public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
    else:
        kind, data = 0, spki_of(key)
    first, second = bytes([0x08, kind]), b"\x12" + varint(len(data)) + data
    if variant == "swapped":
        return second + first
    if variant == "extrafield":
        return first + second + b"\x18\x00"
    if variant == "longvarint":
        return bytes([0x08, kind | 0x80, 0x00]) + second
    if variant == "nodata":
        return first
    return first + second


def extension(name, critical, value, explicit_false=False):
    flag = tlv(1, b"\xff") if critical else (tlv(1, b"\x00") if explicit_false else b"")
    return tlv(0x30, oid(name) + flag + value)


def signed_key(host, variant, cert_spki):
    key = host_key_bytes(host, variant)
    message = PREFIX + cert_spki
    if variant == "prefix":
        message = cert_spki
    if variant == "otherspki":
        message = PREFIX + spki_of(ec.derive_private_key(7, ec.SECP256R1()))
    flavour = {"badsig": "flip", "highs": "highs", "pad": "pad"}.get(variant, "good")
    signature = sign(host, message, flavour)
    body = tlv(4, key) + tlv(4, signature)
    if variant == "seqextra":
        body += tlv(4, b"")
    if variant == "bitstring":
        body = tlv(4, key) + tlv(3, b"\x00" + signature)
    out = tlv(0x30, body)
    return out + b"\x00" if variant == "trail" else out


def extensions_of(codes, host, variant, cert_spki):
    if codes == "none":
        return b""
    out = b""
    for code in [] if codes == "empty" else codes.split(","):
        critical = code.endswith("c")
        base = code.rstrip("c")
        if base in ("L", "LF"):
            value = tlv(4, signed_key(host, variant, cert_spki))
            out += extension(LIBP2P_OID, critical, value, explicit_false=base == "LF")
        elif base == "KU":
            out += extension("2.5.29.15", critical, tlv(4, bytes([3, 2, 7, 0x80])))
        elif base == "F":
            out += extension("1.2.3.4.5", False, tlv(4, b"x"), explicit_false=True)
        elif base == "X":
            out += extension("1.2.3.4.6", critical, tlv(12, b"x"))
        elif base.startswith("B"):
            # A value of a given size, for the lengths of one, two and three bytes.
            out += extension("1.2.3.4.9", critical, tlv(4, bytes(int(base[1:]))))
        elif base.startswith("O"):
            out += extension("1.2.3.4." + base[1:], critical, tlv(4, b"other"))
        else:
            raise ValueError("unknown extension " + code)
    return tlv(0xA3, tlv(0x30, out))


def cert_build(
    cert_key,
    sigalg,
    sig,
    version,
    serial,
    issuer,
    subject,
    not_before,
    not_after,
    spki_form,
    uids,
    exts,
    host_key,
    host_variant,
    tbs_flip,
):
    key = private_key(cert_key)
    host = private_key(host_key)
    spki = spki_of(key, compressed=spki_form == "compressed")
    if isinstance(key, ed25519.Ed25519PrivateKey):
        outer = inner = tlv(0x30, oid(ED25519_OID))
        digest = None
    else:
        name = ECDSA_SHA384 if sigalg == "sha384" else ECDSA_SHA256
        digest = hashes.SHA384() if sigalg == "sha384" else hashes.SHA256()
        outer = inner = tlv(0x30, oid(name) + (tlv(5, b"") if sigalg == "null" else b""))
        if sigalg == "mismatch":
            inner = tlv(0x30, oid(ECDSA_SHA384))
    tbs = b""
    if version != "none":
        tbs += tlv(0xA0, tlv(2, bytes([int(version)])))
    tbs += tlv(2, unhex(serial)) + inner + tlv(0x30, NAMES[issuer])
    times = b""
    for word in (not_before, not_after):
        tag, _, text = word.partition(":")
        times += tlv(int(tag, 16), unhex(text))
    tbs += tlv(0x30, times) + tlv(0x30, NAMES[subject]) + spki
    issuer_uid, _, subject_uid = uids.partition(":")
    if issuer_uid != "-":
        tbs += tlv(0x81, unhex(issuer_uid))
    if subject_uid != "-":
        tbs += tlv(0x82, unhex(subject_uid))
    tbs += extensions_of(exts, host, host_variant, spki)
    tbs = tlv(0x30, tbs)
    if tbs_flip != "-":
        # One byte of the signed part changed before it is signed, so the signature holds.
        position, _, mask = tbs_flip.partition(":")
        at = int(position) * (len(tbs) - 1) // 1000
        tbs = tbs[:at] + bytes([tbs[at] ^ int(mask)]) + tbs[at + 1 :]
    signature = sign(key, tbs, sig, digest)
    der = tlv(0x30, tbs + outer + tlv(3, b"\x00" + signature))
    return tohex(der) + " " + cert_facts_of(der)


# ECDSA signatures in DER.


def sig_der(r, s):
    return tohex(utils.encode_dss_signature(int(r), int(s)))


def sig_scalars(signature):
    r, s = strict_scalars(unhex(signature), 1 << 256)
    return f"{r} {s}"


def x509_time(tag, text):
    try:
        return str(read_time((int(tag, 16), unhex(text), b"")))
    except RefusedError as refusal:
        return "error " + refusal.args[0]


def p256_sign(secret, message):
    key = private_key("p256:" + secret)
    signature = key.sign(unhex(message), ec.ECDSA(hashes.SHA256()))
    return tohex(spki_of(key)) + " " + tohex(signature)


def p256_verify(spki, message, signature):
    public = serialization.load_der_public_key(unhex(spki))
    ok = ecdsa_verifies(public, unhex(message), unhex(signature), P256_ORDER, False)
    return "1" if ok else "0"


# yamux, "Framing": version, type, flags, stream ID and length, big-endian, then data.


def yamux(data):
    data = unhex(data)
    if len(data) < 12:
        return "error short-header"
    version, kind, flags, stream, length = struct.unpack(">BBHII", data[:12])
    if version != 0:
        return "error version"
    if kind > 3:
        return "error type"
    size = length if kind == 0 else 0
    if len(data) < 12 + size:
        return "error truncated"
    body = data[12 : 12 + size]
    return f"{kind} {flags} {stream} {length} {tohex(body)} {len(data) - 12 - size}"


# The unsigned varint of multiformats: minimal, and nine bytes at most.


def read_uvarint(data):
    value = 0
    for i, byte in enumerate(data[:9]):
        value |= (byte & 0x7F) << (7 * i)
        if byte < 128:
            if byte == 0 and i > 0:
                raise RefusedError("varint-not-minimal")
            return value, data[i + 1 :]
    raise RefusedError("varint-too-long" if len(data) >= 9 else "varint-truncated")


# mplex, "Message format": header = stream ID << 3 | flag, a length, then the data.
#
# The rules of a sender are named apart, since the text states them for a writer.


def mplex(data):
    data = unhex(data)
    try:
        header, rest = read_uvarint(data)
        length, rest = read_uvarint(rest)
    except RefusedError as refusal:
        return "error " + refusal.args[0]
    stream, flag = header >> 3, header & 7
    if flag == 7:
        return "error flag"
    if length > 1 << 20:
        return "error sender-rule too-long"
    if flag >= 3 and length:
        return "error sender-rule data-on-end"
    if len(rest) < length:
        return "error truncated"
    return f"{stream} {flag} {tohex(rest[:length])} {len(rest) - length}"


# multistream-select, "Protocol": a varint length, the message, a newline that it counts.


def mss(data):
    data = unhex(data)
    try:
        length, rest = read_uvarint(data)
    except RefusedError as refusal:
        return "error " + refusal.args[0]
    if length == 0:
        return "error empty"
    if len(rest) < length:
        return "error truncated"
    if rest[length - 1] != 0x0A:
        return "error newline"
    return f"{tohex(rest[: length - 1])} {len(rest) - length}"


HANDLERS = {
    "cert_build": cert_build,
    "cert_facts": cert_facts,
    "sig_der": sig_der,
    "sig_scalars": sig_scalars,
    "p256_sign": p256_sign,
    "p256_verify": p256_verify,
    "x509_time": x509_time,
    "yamux": yamux,
    "mplex": mplex,
    "mss": mss,
}

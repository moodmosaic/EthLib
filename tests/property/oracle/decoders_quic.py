"""References for the decoders driver: QUIC frames, headers, integers and the Retry tag."""

# quic_frame <packet> <hex>     One frame by a reader written from RFC 9000 section 19, and
#                               the bytes after it; aioquic reads the integers and the ACK.
# quic_header <cid len> <hex>   One header by a reader written from RFC 9000 section 17, and
#                               the bytes after it; aioquic's reader must agree where it reads.
# quic_split <cid len> <hex>    The lengths of the coalesced packets of a datagram, by aioquic.
# quic_var <hex>                A variable-length integer and the count of its bytes, by aioquic.
# quic_var_enc <n>              The shortest form of an integer, by aioquic.
# quic_retry <odcid> <dcid> <scid> <token> <unused>   A Retry packet with its tag, by aioquic.
# quic_seal <suite> <secret> <pn> <header> <payload>  A protected packet, by aioquic.
# quic_open <suite> <secret> <offset> <expected> <packet>   Its header, payload and number.
#
# A packet is one of initial, zerortt, handshake, onertt.

from aioquic.buffer import Buffer, encode_uint_var, size_uint_var
from aioquic.quic import packet as quic_packet
from aioquic.quic.crypto import CryptoContext
from aioquic.tls import CipherSuite
from decoders_util import tohex, unhex

MAX_VARINT = (1 << 62) - 1

# RFC 9000, Table 3: the packets that may carry each frame type.
EVERY, NOT_ZERO_RTT, DATA, ONE_RTT = "IH01", "IH1", "01", "1"
ALLOWED = {
    0x00: EVERY,
    0x01: EVERY,
    0x02: NOT_ZERO_RTT,
    0x03: NOT_ZERO_RTT,
    0x04: DATA,
    0x05: DATA,
    0x06: NOT_ZERO_RTT,
    0x07: ONE_RTT,
    **dict.fromkeys(range(0x08, 0x1B), DATA),
    0x1B: ONE_RTT,
    0x1C: EVERY,
    0x1D: DATA,
    0x1E: ONE_RTT,
}
PACKETS = {"initial": "I", "handshake": "H", "zerortt": "0", "onertt": "1"}


class RefusedError(Exception):
    """The input is not what the text accepts; the first word is the kind of error."""


class DisagreeError(Exception):
    """The reader written from the text and aioquic read the same bytes in two ways."""


def x(data):
    return "x" + bytes(data).hex()


def rest_of(buf):
    return tohex(buf.data_slice(buf.tell(), buf.capacity))


def read_ack(buf, ecn):
    """The fields of an ACK frame, section 19.3, with the ranges checked as 19.3.1 says."""
    start = buf.tell()
    var = buf.pull_uint_var
    largest, delay, count, first = var(), var(), var(), var()
    smallest = largest - first
    valid = smallest >= 0
    ranges = []
    for _ in range(count):
        gap, length = var(), var()
        smallest = smallest - gap - 2 - length
        # Each range must start at a packet number that is not negative.
        valid = valid and smallest >= 0
        ranges.append(f"{gap}-{length}")
    end = buf.tell()
    # aioquic reads the same fields, and refuses the same ranges.
    check = Buffer(data=buf.data_slice(start, end))
    try:
        quic_packet.pull_ack_frame(check)
        theirs = check.eof()
    except ValueError:
        theirs = False
    if theirs != valid:
        raise DisagreeError(f"ack ranges: the text says {valid}, aioquic {theirs}")
    if not valid:
        raise RefusedError("encoding: an ACK range below zero")
    counts = "-"
    if ecn:
        counts = f"{var()}/{var()}/{var()}"
    return f"ack:{largest}:{delay}:{first}:[{','.join(ranges)}]:{counts}"


def read_frame(buf, packet):
    """One frame, section 19, with the checks that the text lets a receiver make."""
    start = buf.tell()
    var = buf.pull_uint_var
    kind = var()
    if buf.tell() - start != size_uint_var(kind):
        raise RefusedError("encoding: a frame type in a longer form, section 12.4")
    if kind == 0x00:
        text = "padding"
    elif kind == 0x01:
        text = "ping"
    elif kind in (0x02, 0x03):
        text = read_ack(buf, kind == 0x03)
    elif kind == 0x04:
        text = f"reset_stream:{var()}:{var()}:{var()}"
    elif kind == 0x05:
        text = f"stop_sending:{var()}:{var()}"
    elif kind == 0x06:
        offset, length = var(), var()
        data = buf.pull_bytes(length)
        if offset + length > MAX_VARINT:
            raise RefusedError("encoding: CRYPTO past 2^62 - 1")
        text = f"crypto:{offset}:{x(data)}"
    elif kind == 0x07:
        length = var()
        if length == 0:
            raise RefusedError("encoding: an empty token")
        text = f"new_token:{x(buf.pull_bytes(length))}"
    elif 0x08 <= kind <= 0x0F:
        stream = var()
        offset = var() if kind & 0x04 else None
        if kind & 0x02:
            data = buf.pull_bytes(var())
        else:
            data = buf.pull_bytes(buf.capacity - buf.tell())
        if (offset or 0) + len(data) > MAX_VARINT:
            raise RefusedError("encoding: STREAM past 2^62 - 1")
        shown = "-" if offset is None else offset
        text = f"stream:{stream}:{shown}:{(kind >> 1) & 1}:{kind & 1}:{x(data)}"
    elif kind == 0x10:
        text = f"max_data:{var()}"
    elif kind == 0x11:
        text = f"max_stream_data:{var()}:{var()}"
    elif kind in (0x12, 0x13, 0x16, 0x17):
        limit = var()
        if limit > 1 << 60:
            raise RefusedError("encoding: a stream count above 2^60")
        name = "max_streams" if kind < 0x14 else "streams_blocked"
        text = f"{name}:{kind & 1}:{limit}"
    elif kind == 0x14:
        text = f"data_blocked:{var()}"
    elif kind == 0x15:
        text = f"stream_data_blocked:{var()}:{var()}"
    elif kind == 0x18:
        sequence, retire = var(), var()
        length = buf.pull_uint8()
        if not 1 <= length <= 20:
            raise RefusedError("encoding: a connection ID of no byte or of more than 20")
        cid = buf.pull_bytes(length)
        token = buf.pull_bytes(16)
        if retire > sequence:
            raise RefusedError("encoding: Retire Prior To above the sequence number")
        text = f"new_connection_id:{sequence}:{retire}:{x(cid)}:{x(token)}"
    elif kind == 0x19:
        text = f"retire_connection_id:{var()}"
    elif kind in (0x1A, 0x1B):
        name = "path_challenge" if kind == 0x1A else "path_response"
        text = f"{name}:{x(buf.pull_bytes(8))}"
    elif kind in (0x1C, 0x1D):
        code = var()
        frame = var() if kind == 0x1C else "-"
        text = f"connection_close:{code}:{frame}:{x(buf.pull_bytes(var()))}"
    elif kind == 0x1E:
        text = "handshake_done"
    else:
        raise RefusedError("encoding: an unknown frame type")
    if PACKETS[packet] not in ALLOWED[kind]:
        raise RefusedError("violation: the frame may not be in this packet")
    return text


def quic_frame(packet, data):
    buf = Buffer(data=unhex(data))
    try:
        text = read_frame(buf, packet)
    except RefusedError as e:
        return "error:" + str(e).split(":")[0]
    except ValueError:
        # A field that ends early is FRAME_ENCODING_ERROR, section 20.1.
        return "error:encoding"
    return f"{text} {rest_of(buf)}"


def read_header(buf, cid_length):
    """One header through its packet number, or a whole Retry or Version Negotiation packet."""
    first = buf.pull_uint8()
    width = (first & 3) + 1
    if not first & 0x80:
        # Section 17.3.1: the fixed bit, the spin bit, two reserved bits, the key phase.
        if not first & 0x40:
            raise RefusedError("the fixed bit is 0")
        if first & 0x18:
            raise RefusedError("a reserved bit is set")
        if cid_length > 20:
            raise RefusedError("a connection ID of more than 20 bytes")
        cid = buf.pull_bytes(cid_length)
        number = int.from_bytes(buf.pull_bytes(width), "big")
        return f"onertt:{x(cid)}:{(first >> 5) & 1}:{(first >> 2) & 1}:{width - 1}:{number}"
    version = buf.pull_uint32()
    # Section 17.2: version 1 bounds a connection ID at 20 bytes; the invariants at 255.
    limit = 20 if version == 1 else 255
    cids = []
    for _ in range(2):
        length = buf.pull_uint8()
        if length > limit:
            raise RefusedError("a connection ID of more than 20 bytes")
        cids.append(x(buf.pull_bytes(length)))
    if version == 0:
        versions = []
        while not buf.eof():
            versions.append(str(buf.pull_uint32()))
        return f"vn:{cids[0]}:{cids[1]}:{first & 0x7F}:[{','.join(versions)}]"
    if version != 1:
        raise RefusedError("a version that is neither 0 nor 1")
    if not first & 0x40:
        raise RefusedError("the fixed bit is 0")
    kind = (first >> 4) & 3
    if kind == 3:
        rest = buf.pull_bytes(buf.capacity - buf.tell())
        # Section 17.2.5.2: a client discards a Retry with a token of no bytes.
        if len(rest) <= 16:
            raise RefusedError("a Retry with no token")
        return f"retry:{cids[0]}:{cids[1]}:{x(rest[:-16])}:{x(rest[-16:])}:{first & 0x0F}"
    if first & 0x0C:
        raise RefusedError("a reserved bit is set")
    token = ""
    if kind == 0:
        token = ":" + x(buf.pull_bytes(buf.pull_uint_var()))
    length = buf.pull_uint_var()
    if length < width:
        raise RefusedError("a Length that does not hold the packet number")
    number = int.from_bytes(buf.pull_bytes(width), "big")
    name = ("initial", "zerortt", "handshake")[kind]
    return f"{name}:{cids[0]}:{cids[1]}{token}:{width - 1}:{length}:{number}"


TYPES = {
    "initial": quic_packet.QuicPacketType.INITIAL,
    "zerortt": quic_packet.QuicPacketType.ZERO_RTT,
    "handshake": quic_packet.QuicPacketType.HANDSHAKE,
    "retry": quic_packet.QuicPacketType.RETRY,
    "vn": quic_packet.QuicPacketType.VERSION_NEGOTIATION,
    "onertt": quic_packet.QuicPacketType.ONE_RTT,
}


def check_header(data, cid_length, text):
    """aioquic's reader must give the fields of an accepted header that it also reads."""
    fields = text.split(":")
    name = fields[0]
    pad = 0
    if name in ("initial", "zerortt", "handshake"):
        # aioquic asks for the payload that the Length announces, so give it one.
        pad = int(fields[-2])
        if pad > 4096:
            # A Length up to 2^62 - 1 is valid, and no buffer holds its payload.
            return
    if name == "vn" and (len(fields[1]) > 41 or len(fields[2]) > 41):
        # aioquic bounds every connection ID at 20 bytes, version 1 or not.
        return
    try:
        header = quic_packet.pull_quic_header(Buffer(data=data + bytes(pad)), cid_length)
    except ValueError as e:
        raise DisagreeError(f"aioquic refuses an accepted header: {e}") from None
    theirs = [header.packet_type, x(header.destination_cid)]
    ours = [TYPES[name], fields[1]]
    if name != "onertt":
        theirs.append(x(header.source_cid))
        ours.append(fields[2])
    if name in ("initial", "retry"):
        theirs.append(x(header.token))
        ours.append(fields[3])
    if name == "retry":
        theirs.append(x(header.integrity_tag))
        ours.append(fields[4])
    if name == "vn":
        theirs.append("[" + ",".join(str(v) for v in header.supported_versions) + "]")
        ours.append(fields[4])
    if theirs != ours:
        raise DisagreeError(f"aioquic reads {theirs}, the text {ours}")


def quic_header(cid_length, data):
    data = unhex(data)
    buf = Buffer(data=data)
    try:
        text = read_header(buf, int(cid_length))
    except (RefusedError, ValueError):
        return "error"
    check_header(data, int(cid_length), text)
    return f"{text} {rest_of(buf)}"


def quic_split(cid_length, data):
    """The lengths of the packets of a datagram, as aioquic's connection walks them."""
    buf = Buffer(data=unhex(data))
    lengths = []
    while not buf.eof():
        start = buf.tell()
        header = quic_packet.pull_quic_header(buf, int(cid_length))
        lengths.append(str(header.packet_length))
        buf.seek(start + header.packet_length)
    return ",".join(lengths) or "-"


def quic_var(data):
    buf = Buffer(data=unhex(data))
    value = buf.pull_uint_var()
    return f"{value} {buf.tell()}"


def quic_var_enc(value):
    return tohex(encode_uint_var(int(value)))


def quic_retry(odcid, dcid, scid, token, unused):
    return tohex(
        quic_packet.encode_quic_retry(
            version=1,
            source_cid=unhex(scid),
            destination_cid=unhex(dcid),
            original_destination_cid=unhex(odcid),
            retry_token=unhex(token),
            unused=int(unused),
        )
    )


SUITES = {
    "aes": CipherSuite.AES_128_GCM_SHA256,
    "chacha": CipherSuite.CHACHA20_POLY1305_SHA256,
}


def crypto_of(suite, secret):
    context = CryptoContext()
    context.setup(cipher_suite=SUITES[suite], secret=unhex(secret), version=1)
    return context


def quic_seal(suite, secret, number, header, payload):
    """aioquic protects any header it is given: it does not look at the reserved bits."""
    context = crypto_of(suite, secret)
    return tohex(context.encrypt_packet(unhex(header), unhex(payload), int(number)))


def quic_open(suite, secret, offset, expected, packet):
    context = crypto_of(suite, secret)
    packet = unhex(packet)
    # aioquic takes another key phase than its own for a key update, which is not tested here.
    first = context.hp.remove(packet, int(offset))[0][0]
    if not first & 0x80:
        context.key_phase = (first & 4) >> 2
    header, payload, number, _ = context.decrypt_packet(packet, int(offset), int(expected))
    return f"{tohex(header)} {tohex(payload)} {number}"


# RFC 9001, Appendix A.4: the Retry packet for the connection ID of Appendix A.
RETRY_VECTOR = "ff000000010008f067a5502a4262b5746f6b656e04a265ba2eff4d829058fb3f0f2496ba"
assert quic_retry("8394c8f03e515708", "-", "f067a5502a4262b5", "746f6b656e", "15") == RETRY_VECTOR

HANDLERS = {
    "quic_frame": quic_frame,
    "quic_header": quic_header,
    "quic_split": quic_split,
    "quic_var": quic_var,
    "quic_var_enc": quic_var_enc,
    "quic_retry": quic_retry,
    "quic_seal": quic_seal,
    "quic_open": quic_open,
}

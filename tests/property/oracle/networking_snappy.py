"""Snappy references."""

# snappy_raw_dec <hex>     cramjam (Rust snap) on a raw block.
# snappy_model_dec <hex>   A decoder written from format_description.txt.
# snappy_raw_enc <hex>     cramjam's raw block, to decode elsewhere.
# snappy_frame_dec <hex>   cramjam on a framed stream.
# snappy_frame_model <hex> A decoder written from framing_format.txt.
# snappy_frame_enc <hex>   cramjam's framed stream.
# reqresp_payload <min> <max> <hex>   The payload of a request or a response chunk.
# masked_crc <hex>         The masked CRC-32C of framing_format.txt, section 3.

import cramjam
from networking_util import tohex, unhex

import crc32c


class MalformedError(Exception):
    pass


def model_decompress(data):
    """Decompress a block as format_description.txt describes it.

    The preamble is read as the C++ reference reads it.
    That is at most five bytes, and a value of at most 2^32 - 1.
    """
    pos = 0
    declared = 0
    shift = 0
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
    out = bytearray()
    while pos < len(data):
        tag = data[pos]
        pos += 1
        kind = tag & 3
        if kind == 0:
            length = tag >> 2
            if length >= 60:
                extra = length - 59
                if pos + extra > len(data):
                    raise MalformedError("literal length truncated")
                length = int.from_bytes(data[pos : pos + extra], "little")
                pos += extra
            length += 1
            if pos + length > len(data):
                raise MalformedError("literal truncated")
            out += data[pos : pos + length]
            pos += length
        else:
            if kind == 1:
                length = 4 + ((tag >> 2) & 7)
                width = 1
            else:
                length = 1 + (tag >> 2)
                width = 2 if kind == 2 else 4
            if pos + width > len(data):
                raise MalformedError("copy truncated")
            offset = int.from_bytes(data[pos : pos + width], "little")
            if kind == 1:
                offset |= (tag >> 5) << 8
            pos += width
            if offset == 0 or offset > len(out):
                raise MalformedError("bad offset")
            for _ in range(length):
                out.append(out[-offset])
        if len(out) > declared:
            raise MalformedError("past the declared length")
    if len(out) != declared:
        raise MalformedError("short of the declared length")
    return bytes(out)


def masked_crc(data):
    crc = crc32c.crc32c(data)
    return (((crc >> 15) | (crc << 17)) + 0xA282EAD8) & 0xFFFFFFFF


IDENTIFIER = b"sNaPpY"


def read_chunk(data, pos):
    """The bytes that the chunk at `pos` adds, and the position after it."""
    if pos + 4 > len(data):
        raise MalformedError("header truncated")
    kind = data[pos]
    length = int.from_bytes(data[pos + 1 : pos + 4], "little")
    pos += 4
    if pos + length > len(data):
        raise MalformedError("chunk truncated")
    body = data[pos : pos + length]
    pos += length
    if kind == 0xFF:
        if body != IDENTIFIER:
            raise MalformedError("bad stream identifier")
        return b"", pos
    if kind in (0x00, 0x01):
        if length < 4:
            raise MalformedError("no checksum")
        stored = int.from_bytes(body[:4], "little")
        chunk = model_decompress(body[4:]) if kind == 0 else body[4:]
        if len(chunk) > 65536:
            raise MalformedError("chunk too large")
        if masked_crc(chunk) != stored:
            raise MalformedError("checksum")
        return chunk, pos
    if kind < 0x80:
        raise MalformedError("reserved unskippable")
    return b"", pos


def model_frames(data):
    """Decode a framed stream as framing_format.txt describes it."""
    if not data or data[0] != 0xFF:
        raise MalformedError("no stream identifier")
    pos = 0
    out = bytearray()
    while pos < len(data):
        chunk, pos = read_chunk(data, pos)
        out += chunk
    return bytes(out)


def reqresp_payload(low, high, word):
    """An ssz_snappy payload of the consensus layer: a length, then a framed stream.

    The reader stops at the chunk that completes the length, and nothing may follow it.
    """
    from networking_codecs import read_varint

    data = unhex(word)
    n, size, minimal = read_varint(data, 10)
    if not minimal or n >= 2**64:
        raise MalformedError("length prefix")
    rest = data[size:]
    if n > min(int(high), 10 * 2**20) or n < int(low):
        raise MalformedError("length out of bounds")
    if len(rest) > 32 + n + n // 6:
        raise MalformedError("too many compressed bytes")
    if not rest or rest[0] != 0xFF:
        raise MalformedError("no stream identifier")
    pos = 0
    out = bytearray()
    while pos < len(rest):
        chunk, pos = read_chunk(rest, pos)
        out += chunk
        if len(out) >= n:
            break
    if len(out) != n or pos != len(rest):
        raise MalformedError("length mismatch or trailing bytes")
    return tohex(out)


HANDLERS = {
    "snappy_raw_dec": lambda d: tohex(cramjam.snappy.decompress_raw(unhex(d))),
    "snappy_model_dec": lambda d: tohex(model_decompress(unhex(d))),
    "snappy_raw_enc": lambda d: tohex(cramjam.snappy.compress_raw(unhex(d))),
    "snappy_frame_dec": lambda d: tohex(cramjam.snappy.decompress(unhex(d))),
    "snappy_frame_model": lambda d: tohex(model_frames(unhex(d))),
    "snappy_frame_enc": lambda d: tohex(cramjam.snappy.compress(unhex(d))),
    "reqresp_payload": reqresp_payload,
    "masked_crc": lambda d: str(masked_crc(unhex(d))),
}

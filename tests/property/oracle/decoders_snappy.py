"""References for the decoders driver: Snappy blocks of more than 64 KiB."""

# snappy_block <hex>          The output of a block as its length and its SHA-256, by a reader
#                             written from format_description.txt, and by cramjam.
# snappy_check <block> <data> Whether each of the two readers gives exactly the data.

import hashlib

import cramjam
from decoders_util import unhex


class RefusedError(Exception):
    """The block is not what the format accepts."""


def decompress(data):
    """The output of a block, from sections 1 and 2 of the format description."""
    pos, length, shift = 0, 0, 0
    while True:
        if pos >= len(data):
            raise RefusedError("the preamble ends early")
        if pos >= 5:
            raise RefusedError("a preamble of more than five bytes")
        byte = data[pos]
        pos += 1
        length |= (byte & 0x7F) << shift
        shift += 7
        if byte < 0x80:
            break
    if length > 2**32 - 1:
        raise RefusedError("a length above 2^32 - 1")
    out = bytearray()
    while pos < len(data):
        tag = data[pos]
        pos += 1
        kind = tag & 3
        if kind == 0:
            # Section 2.1: a literal, its length less one in the tag or in 1 to 4 bytes.
            count = tag >> 2
            if count >= 60:
                extra = count - 59
                if pos + extra > len(data):
                    raise RefusedError("a literal length ends early")
                count = int.from_bytes(data[pos : pos + extra], "little")
                pos += extra
            count += 1
            if pos + count > len(data):
                raise RefusedError("a literal ends early")
            out += data[pos : pos + count]
            pos += count
        else:
            # Section 2.2: a copy, with an offset of one, two or four bytes.
            width = {1: 1, 2: 2, 3: 4}[kind]
            if pos + width > len(data):
                raise RefusedError("an offset ends early")
            if kind == 1:
                count = 4 + ((tag >> 2) & 7)
                offset = ((tag >> 5) << 8) | data[pos]
            else:
                count = (tag >> 2) + 1
                offset = int.from_bytes(data[pos : pos + width], "little")
            pos += width
            if offset == 0 or offset > len(out):
                raise RefusedError("an offset of zero or before the output")
            for _ in range(count):
                out.append(out[-offset])
        if len(out) > length:
            raise RefusedError("more output than the preamble says")
    if len(out) != length:
        raise RefusedError("less output than the preamble says")
    return bytes(out)


def digest(data):
    return f"{len(data)}:{hashlib.sha256(data).hexdigest()}"


def both(data):
    try:
        model = decompress(data)
    except RefusedError:
        model = None
    try:
        package = bytes(cramjam.snappy.decompress_raw(data))
    except Exception:
        package = None
    return model, package


def snappy_block(data):
    model, package = both(unhex(data))
    return " ".join("error" if out is None else digest(out) for out in (model, package))


def snappy_check(block, data):
    data = unhex(data)
    return " ".join("1" if out == data else "0" for out in both(unhex(block)))


HANDLERS = {"snappy_block": snappy_block, "snappy_check": snappy_check}

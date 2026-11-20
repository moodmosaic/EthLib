"""References for the general functions of the serialization layer, at every parameter."""

#     rlpprefix <kind> <length>      The prefix of a payload of a length, or error.
#     rlphead <hex>                  What the first bytes of an encoding announce.
#     rlpitem <hex> <pos> <stop>     The item read between two positions, and where it ends.
#     be <n>                         A number in base 256, most significant byte first.
#     uintmodel <width> <n>          The bytes and the root of an integer of any width.
#     merkle <hash> <limit> <chunks> The root of chunks under a limit, `-` for none.
#     progressive <hash> <level> <chunks>   The root of a progressive spine from a level.
#     zeroroot <hash> <depth>        The root of the perfect tree of zero chunks.
#     branchx <hash> <leaf> <branch> <index>   The root a branch climbs to, under a hash.
#     pgindex <chunk> <depth> <spine>   The node of a chunk on a progressive spine.
#     indices <index>                The path and the branch of a generalized index.
#     dertlvx <hex>                  One DER value, or what the input lacks.
#     derstring <width> <hex>        Whether bytes are code points of a fixed width.
#     e2shead <type> <length>        The header of an e2store record.
#     e2sindex <hex>                 The start and the offsets of an index record.
#     rpcfixed <n> <upper> <text>    A hexadecimal text of exactly n bytes.
#     rpcquantity <bits> <text>      A quantity below a power of two.
#     rpcmax <n> <text>              A hexadecimal text of at most n bytes.
#
# Each is written from the text of its source, and none calls a package.

import hashlib
import json
import re


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return bytes(data).hex() if data else "-"


# RLP: Appendix B of the Yellow Paper.


def rlpprefix(kind, length):
    """R_b and R_l: the bytes in front of a payload of a length."""
    base = 0x80 if kind == "bytes" else 0xC0
    if length < 56:
        return bytes([base + length]).hex()
    if length >= 2**64:
        return "error"
    digits = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return (bytes([base + 55 + len(digits)]) + digits).hex()


def rlphead(data):
    """The kind, the bytes of the length and the length that a first byte announces."""
    first = data[0]
    if first < 0x80:
        return "error not a prefix"
    kind = "list" if first >= 0xC0 else "bytes"
    base = 0xC0 if first >= 0xC0 else 0x80
    if first - base < 56:
        return f"{kind} 0 {first - base}"
    k = first - base - 55
    digits = data[1 : 1 + k]
    if len(digits) < k:
        return f"error short {k} {len(data) - 1}"
    length = int.from_bytes(digits, "big")
    # BE writes no leading zero, and a length below 56 has the short form: both may hold.
    faults = (["zero"] if digits[0] == 0 else []) + (["shortform"] if length < 56 else [])
    return f"error {' '.join(faults)}" if faults else f"{kind} {k} {length}"


def rlp_model(data, pos, stop):
    """The item at a position, and the position after it."""
    if pos >= stop:
        raise ValueError("short")
    first = data[pos]
    if first < 0x80:
        return data[pos : pos + 1].hex(), pos + 1
    is_list = first >= 0xC0
    base = 0xC0 if is_list else 0x80
    if first - base < 56:
        length, start = first - base, pos + 1
    else:
        k = first - base - 55
        if pos + 1 + k > stop:
            raise ValueError("short length")
        digits = data[pos + 1 : pos + 1 + k]
        length = int.from_bytes(digits, "big")
        if digits[0] == 0 or length < 56:
            raise ValueError("length not canonical")
        start = pos + 1 + k
    if start + length > stop:
        raise ValueError("short payload")
    if not is_list:
        if length == 1 and data[start] < 0x80:
            raise ValueError("single byte with a prefix")
        return data[start : start + length].hex(), start + length
    items, at = [], start
    while at < start + length:
        item, at = rlp_model(data, at, start + length)
        items.append(item)
    return items, start + length


def rlpitem(data, pos, stop):
    try:
        item, end = rlp_model(data, pos, stop)
    except ValueError:
        return "error"
    return f"{json.dumps(item, separators=(',', ':'))} {end}"


# SSZ: simple-serialize.md, with the hash as a parameter.


def toy(data):
    """A hash that is not a hash: cheap, and unlike any real one."""
    out = bytearray(32)
    for i, byte in enumerate(data):
        out[(7 * i + byte) % 32] ^= (byte + i) % 256
    return bytes(out)


HASHES = {
    "sha256": lambda data: hashlib.sha256(data).digest(),
    "twice": lambda data: hashlib.sha256(hashlib.sha256(data).digest()).digest(),
    "sha3": lambda data: hashlib.sha3_256(data).digest(),
    "toy": toy,
}
ZERO = bytes(32)


def zero_root(h, depth):
    node = ZERO
    for _ in range(depth):
        node = h(node + node)
    return node


def perfect(h, chunks, depth, start):
    """The root of the perfect tree of a depth over the chunks from a position."""
    if start >= len(chunks):
        return zero_root(h, depth)
    if depth == 0:
        return chunks[start]
    left = perfect(h, chunks, depth - 1, start)
    return h(left + perfect(h, chunks, depth - 1, start + (1 << (depth - 1))))


def depth_for(count):
    return (count - 1).bit_length() if count > 1 else 0


def merkle(h, limit, chunks):
    """merkleize(chunks, limit): pad to the next power of two of the limit."""
    if limit is None:
        limit = len(chunks)
    if limit < len(chunks):
        return "error"
    return perfect(h, chunks, depth_for(limit), 0).hex()


def progressive(h, level, chunks):
    """merkleize_progressive (EIP-7916): a tree of 4^level chunks, then the rest."""
    if not chunks:
        return ZERO
    width = 4**level
    left = perfect(h, chunks[:width], 2 * level, 0)
    return h(left + progressive(h, level + 1, chunks[width:]))


def chunks_of(word):
    data = unhex(word)
    return [data[i : i + 32] for i in range(0, len(data), 32)]


def uintmodel(width, n):
    """An integer of a width in bytes: little-endian, and the root of its packed chunks."""
    if n >= 256**width:
        return "error"
    data = n.to_bytes(width, "little")
    padded = data + bytes(-len(data) % 32)
    chunks = [padded[i : i + 32] for i in range(0, len(padded), 32)]
    return f"{tohex(data)} {merkle(HASHES['sha256'], None, chunks)}"


def branchx(h, leaf, branch, index):
    """calculate_merkle_root of merkle-proofs.md: one node of the branch for each bit."""
    node = leaf
    for i, sibling in enumerate(branch):
        node = h(sibling + node) if index >> i & 1 else h(node + sibling)
    return node.hex()


def pgindex(chunk, depth, spine):
    """EIP-7916: a spine node has a tree of chunks on its left and the next node on its right."""
    while chunk >= 1 << depth:
        chunk -= 1 << depth
        depth += 2
        spine = spine * 2 + 1
    return ((spine * 2) << depth) + chunk


def pgindex_closed(chunk):
    """The same from the contents node 2: run k holds 4^k chunks from (4^k - 1) / 3."""
    k = 0
    while chunk >= (4 ** (k + 1) - 1) // 3:
        k += 1
    return (3 * 2**k - 1) * 2 * 4**k + chunk - (4**k - 1) // 3


def indices(index):
    """get_path_indices and get_branch_indices of ssz/merkle-proofs.md."""
    path = [index]
    while path[-1] > 1:
        path.append(path[-1] // 2)
    path = path[:-1]
    return f"{json.dumps(path)} {json.dumps([i ^ 1 for i in path])}"


# DER: X.690 8.1.


def dertlvx(data):
    """One tag, length and value, or the fault and the bytes that the input lacks."""
    if len(data) < 2:
        return f"truncated 2 {len(data)}"
    tag, first = data[0], data[1]
    if tag & 0x1F == 0x1F or tag == 0:
        return "tag"
    if first < 0x80:
        length, header = first, 2
    else:
        count = first & 0x7F
        if count in (0, 127):
            return "length"
        if len(data) < 2 + count:
            return f"truncated {2 + count} {len(data)}"
        length, header = int.from_bytes(data[2 : 2 + count], "big"), 2 + count
        if data[2] == 0 or length < 128:
            return "length"
    if len(data) < header + length:
        return f"truncated {header + length} {len(data)}"
    content, rest = data[header : header + length], data[header + length :]
    return f"{tag} {tohex(content)} {tohex(rest)}"


def derstring(width, data):
    """UniversalString and BMPString (X.690 8.23): code points on a fixed count of octets."""
    if width == 0 or len(data) % width:
        return "error"
    points = [int.from_bytes(data[i : i + width], "big") for i in range(0, len(data), width)]
    return "ok" if all(p <= 0x10FFFF and not 0xD800 <= p <= 0xDFFF for p in points) else "error"


# E2store: type[2] | length[4] little-endian | reserved[2].


def e2shead(kind, length):
    if length >= 2**32:
        return "error"
    return (kind.to_bytes(2, "big") + length.to_bytes(4, "little") + b"\0\0").hex()


def e2sindex(data):
    """An index record: starting-number | index | index ... | count, each of 8 bytes."""
    if len(data) < 16 or len(data) % 8:
        return "error"
    words = [data[i : i + 8] for i in range(0, len(data), 8)]
    count = int.from_bytes(words[-1], "little")
    if len(words) != count + 2:
        return "error"
    offsets = [int.from_bytes(w, "little", signed=True) for w in words[1:-1]]
    return " ".join(map(str, [int.from_bytes(words[0], "little"), *offsets]))


# JSON-RPC: the patterns of execution-apis, src/schemas/base-types.yaml, at every width.


def text_of(word):
    try:
        return unhex(word).decode("utf-8")
    except UnicodeDecodeError:
        return None


def rpcfixed(n, upper, chars):
    """`^0x[0-9a-f]{2n}$`, as hash32 and bytes8 are; `[0-9a-fA-F]` as address is."""
    digits = "[0-9a-fA-F]" if upper else "[0-9a-f]"
    if chars is None or not re.fullmatch(f"0x{digits}{{{2 * n}}}", chars):
        return "error"
    return tohex(bytes.fromhex(chars[2:]))


def rpcquantity(bits, chars):
    """`^0x(0|[1-9a-f][0-9a-f]*)$`, and below `2 ^ bits` as uint64 and uint256 are."""
    if chars is None or not re.fullmatch("0x(0|[1-9a-f][0-9a-f]*)", chars):
        return "error"
    value = int(chars, 16)
    return str(value) if value < 2**bits else "error"


def rpcmax(n, chars):
    """`^0x[0-9a-f]*$` on whole bytes, and at most n of them."""
    if chars is None or not re.fullmatch("0x([0-9a-f]{2})*", chars):
        return "error"
    data = bytes.fromhex(chars[2:])
    return tohex(data) if len(data) <= n else "error"


def limit_of(word):
    return None if word == "-" else int(word)


HANDLERS = {
    "rlpprefix": lambda kind, length: rlpprefix(kind, int(length)),
    "rlphead": lambda data: rlphead(unhex(data)),
    "rlpitem": lambda data, pos, stop: rlpitem(unhex(data), int(pos), int(stop)),
    "be": lambda n: tohex(int(n).to_bytes((int(n).bit_length() + 7) // 8, "big")),
    "uintmodel": lambda width, n: uintmodel(int(width), int(n)),
    "merkle": lambda h, limit, chunks: merkle(HASHES[h], limit_of(limit), chunks_of(chunks)),
    "progressive": lambda h, level, chunks: progressive(
        HASHES[h], int(level), chunks_of(chunks)
    ).hex(),
    "zeroroot": lambda h, depth: zero_root(HASHES[h], int(depth)).hex(),
    "branchx": lambda h, leaf, branch, index: branchx(
        HASHES[h], unhex(leaf), chunks_of(branch), int(index)
    ),
    "pgindex": lambda chunk, depth, spine: str(
        pgindex_closed(int(chunk))
        if (depth, spine) == ("0", "2")
        else pgindex(int(chunk), int(depth), int(spine))
    ),
    "indices": lambda index: indices(int(index)),
    "dertlvx": lambda data: dertlvx(unhex(data)),
    "derstring": lambda width, data: derstring(int(width), unhex(data)),
    "e2shead": lambda kind, length: e2shead(int(kind), int(length)),
    "e2sindex": lambda data: e2sindex(unhex(data)),
    "rpcfixed": lambda n, upper, text: rpcfixed(int(n), upper == "1", text_of(text)),
    "rpcquantity": lambda bits, text: rpcquantity(int(bits), text_of(text)),
    "rpcmax": lambda n, text: rpcmax(int(n), text_of(text)),
}

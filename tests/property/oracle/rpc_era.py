"""A writer of era1 files, from the era1 document, with cramjam and eth-remerkleable."""

#     era1 <start> <blocks> <fault>
#         The bytes of a file and its accumulator root: `<file>|<root>`.
#
# A block is `header.body.receipts.total difficulty`.
# The first three are RLP items in hexadecimal, and the last a number in decimal.
# Blocks are joined with `,`, and `-` is no block.
#
# The file is that of `formats/era1.md` of e2store-format-specs:
#     era1 := Version | block-tuple* | other-entries* | Accumulator | BlockIndex
#     block-tuple := CompressedHeader | CompressedBody | CompressedReceipts | TotalDifficulty
# A record is its type on two bytes, then the length of its data on four bytes, little-endian.
# Two reserved bytes of zero follow, then its data (`docs/e2store.md` of nimbus-eth2).
# The total difficulty and the numbers of the index are little-endian, as SSZ writes them.
# An offset of the index counts from the start of the BlockIndex record.
# That is how `internal/era` of go-ethereum writes it.
#
# The fault names one change that makes the bytes another file, or `-` for none:
#     truncate, swap, noversion, version, accumulator, count, offset, noindex, size, frame,
#     reserved, between, and `other`, a record of another type before the accumulator,
#     which the document allows.

import cramjam
from Crypto.Hash import keccak
from remerkleable.basic import uint256
from remerkleable.byte_arrays import Bytes32
from remerkleable.complex import Container, List


def keccak256(data):
    return keccak.new(digest_bits=256, data=bytes(data)).digest()


class HeaderRecord(Container):
    block_hash: Bytes32
    total_difficulty: uint256


VERSION = b"\x65\x32"
HEADER = b"\x03\x00"
BODY = b"\x04\x00"
RECEIPTS = b"\x05\x00"
DIFFICULTY = b"\x06\x00"
ACCUMULATOR = b"\x07\x00"
INDEX = b"\x66\x32"


def record(kind, data, reserved=b"\x00\x00"):
    return kind + len(data).to_bytes(4, "little") + reserved + data


def framed(data):
    return bytes(cramjam.snappy.compress(data))


def era1(start, blocks, fault):
    start = int(start)
    entries = []
    if blocks != "-":
        for block in blocks.split(","):
            header, body, receipts, difficulty = block.split(".")
            entries.append(
                (
                    bytes.fromhex(header),
                    bytes.fromhex(body),
                    bytes.fromhex(receipts),
                    int(difficulty),
                )
            )
    records = [HeaderRecord(block_hash=keccak256(e[0]), total_difficulty=e[3]) for e in entries]
    # A file of too many blocks has no root, and takes that of its first 8192.
    root = bytes(List[HeaderRecord, 8192](*records[:8192]).hash_tree_root())
    out = b"" if fault == "noversion" else record(VERSION, b"")
    offsets = []
    for i, (header, body, receipts, difficulty) in enumerate(entries):
        if fault == "between" and i == 1:
            out += record(b"\x99\x00", b"other")
        offsets.append(len(out))
        compressed = framed(header)
        if fault == "frame" and i == 0:
            compressed = compressed[:-1] + bytes([compressed[-1] ^ 0xFF])
        total = difficulty.to_bytes(32, "little")
        if fault == "size" and i == 0:
            total = total[:31]
        parts = [
            record(
                HEADER, compressed, b"\x00\x01" if fault == "reserved" and i == 0 else b"\x00\x00"
            ),
            record(BODY, framed(body)),
            record(RECEIPTS, framed(receipts)),
            record(DIFFICULTY, total),
        ]
        if fault == "swap" and i == 0:
            parts[1], parts[2] = parts[2], parts[1]
        out += b"".join(parts)
    if fault == "version":
        out += record(VERSION, b"")
    if fault == "other":
        out += record(b"\x99\x00", b"other") + record(b"\x98\x00", b"")
    accumulator = root
    if fault == "accumulator":
        accumulator = bytes([root[0] ^ 1]) + root[1:]
    out += record(ACCUMULATOR, accumulator)
    base = len(out)
    relative = [offset - base for offset in offsets]
    if fault == "offset" and relative:
        relative[-1] += 1
    count = len(entries) + (1 if fault == "count" else 0)
    index = start.to_bytes(8, "little")
    index += b"".join(offset.to_bytes(8, "little", signed=True) for offset in relative)
    index += count.to_bytes(8, "little")
    if fault != "noindex":
        out += record(INDEX, index)
    if fault == "truncate":
        out = out[:-1]
    return f"{out.hex()}|{root.hex()}"


COMMANDS = {"era1": era1}

"""A reader of the eth and snap messages, written from devp2p with the `rlp` package."""

#     eth <version> <id> <data>     The message of eth/<version> with an ID, as text, or `error`.
#     snap <version> <id> <data>    The same for snap/<version>.
#     headers <request> <headers>   Whether some headers answer a GetBlockHeaders: `ok` or `no`.
#     pooled <hashes> <txs>         Whether some transactions answer a GetPooledTransactions.
#     slim <account>                The value in the state trie of an account in slim form.
#     forkid <genesis> <genesis time> <activations> <merge> <number> <time>
#     validate <genesis> <genesis time> <activations> <merge> <number> <time> <hash> <next>
#         The fork identifier of a head, and whether a node accepts one, by EIP-2124.
#     accounts <start> <count> <limit> <entries>
#         A range of a state trie and its proof, with py-trie: `root|accounts|proof|more`.
#
# The shapes are those of `caps/eth.md` and `caps/snap.md`.
# `P` is a scalar with no leading zero, `B_n` a string of `n` bytes, and `{0, 1}` a flag.
# A request ID is below `2^64`, as EIP-2481 has it.
# The text of a message is its fields in order.
# A scalar is in decimal, and a string is `x` and its hexadecimal.
# An item that the message carries whole is `i` and the hexadecimal of its encoding.
# A list is in `[]` and a group of fields in `()`.

import zlib

from Crypto.Hash import keccak

import rlp
from trie import HexaryTrie


def keccak256(data):
    return keccak.new(digest_bits=256, data=bytes(data)).digest()


class InvalidError(Exception):
    """Bytes that are not the message."""


def scalar(bits=None):
    def read(item):
        if not isinstance(item, bytes) or item[:1] == b"\x00":
            raise InvalidError()
        value = int.from_bytes(item, "big")
        if bits is not None and value >= 2**bits:
            raise InvalidError()
        return str(value)

    return read


def fixed(size):
    def read(item):
        if not isinstance(item, bytes) or len(item) != size:
            raise InvalidError()
        return "x" + item.hex()

    return read


def string(item):
    if not isinstance(item, bytes):
        raise InvalidError()
    return "x" + item.hex()


def whole(item):
    return "i" + rlp.encode(item).hex()


def flag(item):
    if item not in (b"", b"\x01"):
        raise InvalidError()
    return "1" if item else "0"


def listed(read):
    def many(item):
        if not isinstance(item, list):
            raise InvalidError()
        return "[" + ",".join(read(entry) for entry in item) + "]"

    return many


def group(*readers):
    def read(item):
        if not isinstance(item, list) or len(item) != len(readers):
            raise InvalidError()
        fields = [reader(entry) for reader, entry in zip(readers, item, strict=True)]
        return "(" + ",".join(fields) + ")"

    return read


def start(item):
    """The first block of a request: 32 bytes are a hash, and a shorter scalar a number."""
    if isinstance(item, bytes) and len(item) == 32:
        return "x" + item.hex()
    return scalar(64)(item)


def cells(item):
    """The bitmap of an announcement: 16 bytes, or none when no blob transaction is announced."""
    if item == b"":
        return "_"
    return fixed(16)(item)


P = scalar()
ID = scalar(64)
HASH = fixed(32)
FORK_ID = group(fixed(4), scalar(64))


def announcement(version):
    readers = [string, listed(P), listed(HASH)] + ([cells] if version >= 72 else [])

    def read(item):
        text = group(*readers)(item)
        # "All three payload elements must contain an equal number of items."
        if not len(item[0]) == len(item[1]) == len(item[2]):
            raise InvalidError()
        return text

    return read


def eth_reader(version, ident):
    """The reader of the message with an ID on a version, or none when it has none."""
    if ident == 0x00 and version == 68:
        return group(P, P, P, HASH, HASH, FORK_ID)
    table = {
        0x00: group(P, P, HASH, FORK_ID, P, P, HASH),
        0x01: listed(group(HASH, P)),
        0x02: listed(whole),
        0x03: group(ID, group(start, P, P, flag)),
        0x04: group(ID, listed(whole)),
        0x05: group(ID, listed(HASH)),
        0x06: group(ID, listed(whole)),
        0x07: group(whole, P),
        0x08: announcement(version),
        0x09: group(ID, listed(HASH)),
        0x0A: group(ID, listed(whole)),
        0x0F: group(ID, listed(HASH)) if version < 70 else group(ID, P, listed(HASH)),
        0x10: group(ID, listed(listed(whole)))
        if version < 70
        else group(ID, flag, listed(listed(whole))),
    }
    if version >= 69:
        table[0x11] = group(P, P, HASH)
    if version >= 71:
        table[0x12] = group(ID, listed(HASH))
        table[0x13] = group(ID, listed(whole))
    if version >= 72:
        table[0x14] = group(ID, listed(HASH), fixed(16))
        table[0x15] = group(ID, listed(HASH), listed(listed(string)), fixed(16))
    return table.get(ident)


def snap_reader(version, ident):
    entry = group(HASH, string)
    table = {
        0x00: group(ID, HASH, HASH, HASH, P),
        0x01: group(ID, listed(entry), listed(string)),
        0x02: group(ID, HASH, listed(HASH), string, string, P),
        0x03: group(ID, listed(listed(entry)), listed(string)),
        0x04: group(ID, listed(HASH), P),
        0x05: group(ID, listed(string)),
    }
    if version == 1:
        table[0x06] = group(ID, HASH, listed(listed(string)), P)
        table[0x07] = group(ID, listed(string))
    if version == 2:
        table[0x08] = group(ID, listed(HASH), P)
        table[0x09] = group(ID, listed(whole))
    return table.get(ident)


def message(reader, data):
    if reader is None:
        return "error id"
    try:
        return reader(rlp.decode(bytes.fromhex(data) if data != "-" else b""))
    except (InvalidError, rlp.exceptions.DecodingError):
        return "error"


def eth(version, ident, data):
    return message(eth_reader(int(version), int(ident)), data)


def snap(version, ident, data):
    return message(snap_reader(int(version), int(ident)), data)


def headers(request, answer):
    """Whether some headers answer a request, by "GetBlockHeaders (0x03)"."""
    # The request is `start,limit,skip,reverse`, the start a number or 32 bytes in hexadecimal.
    # The headers are of rising number, or falling when `reverse` is set, `skip` blocks apart.
    # They begin at the start block, and are at most `limit`.
    # Headers that are consecutive blocks must chain by their parent hash.
    # "Block Encoding and Validity" asks that of headers in sequence.
    first, limit, skip, reverse = request.split(",")
    limit, skip, reverse = int(limit), int(skip), reverse == "1"
    items = [] if answer == "-" else [rlp.decode(bytes.fromhex(h)) for h in answer.split(",")]
    if len(items) > limit:
        return "no"
    numbers = [int.from_bytes(item[8], "big") for item in items]
    hashes = [keccak256(rlp.encode(item)) for item in items]
    if items:
        if len(first) == 64 and hashes[0].hex() != first:
            return "no"
        if len(first) != 64 and numbers[0] != int(first):
            return "no"
    step = skip + 1
    for i in range(1, len(items)):
        if numbers[i] != (numbers[i - 1] - step if reverse else numbers[i - 1] + step):
            return "no"
        if skip == 0:
            child, parent = (i - 1, i) if reverse else (i, i - 1)
            if items[child][0] != hashes[parent]:
                return "no"
    return "ok"


def wire_hash(item):
    """The hash of a transaction on the wire: of its list, or of its typed bytes.

    A blob transaction in its network form hashes without its blobs (EIP-4844).
    """
    if isinstance(item, list):
        return keccak256(rlp.encode(item))
    if item[:1] == b"\x03":
        try:
            body = rlp.decode(item[1:])
        except rlp.exceptions.DecodingError:
            return keccak256(item)
        if isinstance(body, list) and body and isinstance(body[0], list):
            return keccak256(b"\x03" + rlp.encode(body[0]))
    return keccak256(item)


def pooled(hashes, txs):
    """Whether some transactions answer a request of hashes, by "PooledTransactions (0x0a)".

    The transactions are in the order of the request, and the peer may leave some out.
    """
    wanted = [] if hashes == "-" else hashes.split(",")
    items = [] if txs == "-" else [rlp.decode(bytes.fromhex(t)) for t in txs.split(",")]
    position = 0
    for item in items:
        digest = wire_hash(item).hex()
        while position < len(wanted) and wanted[position] != digest:
            position += 1
        if position == len(wanted):
            return "no"
        position += 1
    return "ok"


EMPTY_ROOT = keccak256(rlp.encode(b""))
EMPTY_CODE = keccak256(b"")


def slim(account):
    """The value of an account in the state trie, from its slim form, or `error`."""
    # The slim form has the empty string for the root of the empty trie.
    # It has the empty string for the hash of empty code too.
    # No other form of the account is the slim one.
    try:
        item = rlp.decode(bytes.fromhex(account) if account != "-" else b"")
    except rlp.exceptions.DecodingError:
        return "error"
    if not isinstance(item, list) or len(item) != 4 or any(isinstance(f, list) for f in item):
        return "error"
    nonce, balance, root, code = item
    if nonce[:1] == b"\x00" or balance[:1] == b"\x00":
        return "error"
    # The nonce has no bound here: no state trie holds one of `2^64` or more (EIP-2681).
    if len(balance) > 32:
        return "error"
    if len(root) not in (0, 32) or len(code) not in (0, 32):
        return "error"
    if root == EMPTY_ROOT or code == EMPTY_CODE:
        return "error"
    return rlp.encode([nonce, balance, root or EMPTY_ROOT, code or EMPTY_CODE]).hex()


def accounts(first, count, limit, entries):
    """A range of a trie of 32-byte keys, with the proof that py-trie gives for it."""
    # The entries are `key=value` joined with `,`.
    # The range starts at the first key at or after `first`.
    # It holds `count` keys, or fewer at the end of the trie.
    # The proof holds the nodes on the path of `first` and on the path of the last key.
    # "GetAccountRange (0x00)" asks for those, and for no node when the range is the whole trie.
    trie = HexaryTrie(db={})
    pairs = {}
    if entries != "-":
        for entry in entries.split(","):
            key, value = entry.split("=")
            pairs[bytes.fromhex(key)] = bytes.fromhex(value)
            trie[bytes.fromhex(key)] = bytes.fromhex(value)
    origin = bytes.fromhex(first)
    keys = sorted(k for k in pairs if k >= origin)
    taken = keys[: int(count)]
    more = len(keys) > len(taken)
    whole_trie = origin == b"\x00" * 32 and not more
    nodes = []
    if not whole_trie or limit == "proof":
        for key in [origin] + taken[-1:]:
            for node in trie.get_proof(key):
                encoded = rlp.encode(node)
                if encoded not in nodes:
                    nodes.append(encoded)
    return "|".join(
        [
            trie.root_hash.hex(),
            ",".join(f"{k.hex()}={pairs[k].hex()}" for k in taken) or "-",
            ",".join(node.hex() for node in nodes) or "-",
            "1" if more else "0",
        ]
    )


THRESHOLD = 1438269973


def schedule(genesis, genesis_time, activations, merge):
    """The fork blocks and the fork times of a chain, and the checksum after each fork."""
    # An activation is `b<number>`, `t<time>`, or `p<number>` for Paris at a block.
    # Activations are joined with `,`.
    # EIP-2124 leaves out a fork at block 0.
    # EIP-6122 leaves out a fork at or before the time of the genesis block.
    # EIP-3675 takes `FORK_NEXT_VALUE` for Paris, when it is set.
    words = [] if activations == "-" else activations.split(",")
    blocks = [int(w[1:]) for w in words if w[0] == "b"]
    if merge != "-":
        blocks.append(int(merge))
    blocks = sorted({b for b in blocks if b > 0})
    times = sorted({int(w[1:]) for w in words if w[0] == "t" and int(w[1:]) > int(genesis_time)})
    data = bytes.fromhex(genesis)
    sums = [zlib.crc32(data)]
    for fork in blocks + times:
        data += fork.to_bytes(8, "big")
        sums.append(zlib.crc32(data))
    return blocks, times, sums


def passed(blocks, times, number, time):
    """How many forks a head has passed: the forks by block, then the forks by time."""
    count = 0
    for fork in blocks:
        if number < fork:
            return count
        count += 1
    for fork in times:
        if time < fork:
            return count
        count += 1
    return count


def forkid(genesis, genesis_time, activations, merge, number, time):
    """The fork identifier of a node at a head, by EIP-2124: `hash,next`."""
    blocks, times, sums = schedule(genesis, genesis_time, activations, merge)
    forks = blocks + times
    count = passed(blocks, times, int(number), int(time))
    following = forks[count] if count < len(forks) else 0
    return f"{sums[count].to_bytes(4, 'big').hex()},{following}"


def validate(genesis, genesis_time, activations, merge, number, time, remote_hash, remote_next):
    """Whether a node accepts the fork identifier of a peer, by the rules of EIP-2124.

    The answer is `ok`, `stale` for a peer that needs an update, or `incompatible`.
    """
    blocks, times, sums = schedule(genesis, genesis_time, activations, merge)
    forks = blocks + times
    number, time, following = int(number), int(time), int(remote_next)
    count = passed(blocks, times, number, time)
    remote = int(remote_hash, 16)
    if sums[count] == remote:
        # Rule 1: the same fork, unless the node has passed the next fork of the peer.
        if following > 0 and (number >= following or (following > THRESHOLD and time >= following)):
            return "incompatible"
        return "ok"
    for j in range(count):
        if sums[j] == remote:
            # Rule 2: the peer is behind, and must announce the fork that follows.
            return "ok" if forks[j] == following else "stale"
    # Rule 3: the peer is ahead; rule 4: otherwise the chains differ.
    return "ok" if remote in sums[count + 1 :] else "incompatible"


COMMANDS = {
    "forkid": forkid,
    "validate": validate,
    "eth": eth,
    "snap": snap,
    "headers": headers,
    "pooled": pooled,
    "slim": slim,
    "accounts": accounts,
}

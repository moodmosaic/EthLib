"""Codec references: varints, QUIC, fork identifiers, gossip.

pb_varint <hex>               A whole input as one varint, by the consensus rules.
uvarint <hex>                 A multiformats unsigned varint at the start: value, rest.
quic_varint_dec <hex>         aioquic's read of a QUIC integer: value, rest.
quic_varint_enc <n>           aioquic's shortest encoding.
quic_pn <bits> <trunc> <exp>  RFC 9000 Appendix A.3, and aioquic's, which must agree.
quic_initial <dcid>           The Initial secrets of client and server, by aioquic.
quic_keys <suite> <secret>    The key, IV and header key of a secret, by aioquic.
quic_protect <suite> <secret> <pn> <header> <payload>   aioquic's protected packet.
forkid <genesis> <blocks> <times> <genesisTime> <head> <time>   EIP-2124 hash and next.
forkid_validate ... <remoteHash> <remoteNext>   EIP-2124 validation, as geth filters.
forkid_mainnet <head> <time>  Mainnet's identifier, checked against the EIPs' vectors.
topic <hex>                   The fork digest and name of a gossip topic.
subnet_name <base> <hex>      The subnet of a topic name.
message_id <altair 0/1> <topic> <data>   The gossip message ID of the consensus layer.
subnets <node> <epoch> <per> <count> <extra> <n>   compute_subscribed_subnets.
"""

import hashlib
import re
import zlib

import cramjam
from aioquic.buffer import Buffer
from aioquic.quic.crypto import CryptoContext, CryptoPair, derive_key_iv_hp
from aioquic.quic.packet import decode_packet_number
from aioquic.tls import CipherSuite
from networking_util import tohex, unhex


class MalformedError(Exception):
    pass


def read_varint(data, limit):
    """The groups of a base-128 varint at the start: value, length, minimal."""
    value = 0
    for i, byte in enumerate(data):
        if i >= limit:
            raise MalformedError("too long")
        value |= (byte & 0x7F) << (7 * i)
        if byte < 0x80:
            return value, i + 1, i == 0 or byte != 0
    raise MalformedError("unterminated")


def pb_varint(word):
    data = unhex(word)
    value, length, minimal = read_varint(data, 10)
    if length != len(data) or not minimal or value >= 2**64:
        raise MalformedError("not one minimal 64-bit varint")
    return str(value)


def uvarint(word):
    data = unhex(word)
    value, length, minimal = read_varint(data, 9)
    if not minimal:
        raise MalformedError("not minimal")
    return f"{value} {tohex(data[length:])}"


def quic_varint_dec(word):
    data = unhex(word)
    buf = Buffer(data=data)
    value = buf.pull_uint_var()
    return f"{value} {tohex(data[buf.tell() :])}"


def quic_varint_enc(n):
    buf = Buffer(capacity=8)
    buf.push_uint_var(int(n))
    return tohex(buf.data)


def quic_pn(bits, truncated, expected):
    bits, truncated, expected = int(bits), int(truncated), int(expected)
    win = 1 << bits
    hwin = win // 2
    candidate = (expected & ~(win - 1)) | truncated
    if candidate <= expected - hwin and candidate < (1 << 62) - win:
        rfc = candidate + win
    elif candidate > expected + hwin and candidate >= win:
        rfc = candidate - win
    else:
        rfc = candidate
    theirs = decode_packet_number(truncated, bits, expected)
    if theirs != rfc:
        return f"references differ {rfc} {theirs}"
    return str(rfc)


def quic_initial(dcid):
    pair = CryptoPair()
    pair.setup_initial(cid=unhex(dcid), is_client=True, version=1)
    return f"{pair.send.secret.hex()} {pair.recv.secret.hex()}"


SUITES = {
    "aes": CipherSuite.AES_128_GCM_SHA256,
    "chacha": CipherSuite.CHACHA20_POLY1305_SHA256,
}


def quic_protect(suite, secret, number, header, payload):
    ctx = CryptoContext()
    ctx.setup(cipher_suite=SUITES[suite], secret=unhex(secret), version=1)
    return tohex(ctx.encrypt_packet(unhex(header), unhex(payload), int(number)))


def quic_keys(suite, secret):
    key, iv, hp = derive_key_iv_hp(cipher_suite=SUITES[suite], secret=unhex(secret), version=1)
    return f"{key.hex()} {iv.hex()} {hp.hex()}"


def fork_list(blocks, times, genesis_time):
    blocks = sorted({int(b) for b in blocks.split(",") if b} - {0})
    times = sorted({int(t) for t in times.split(",") if t and int(t) > genesis_time})
    return blocks, times


def checksums(genesis, forks):
    sums = [zlib.crc32(genesis)]
    for fork in forks:
        sums.append(zlib.crc32(fork.to_bytes(8, "big"), sums[-1]))
    return sums


def forkid(genesis, blocks, times, genesis_time, head, time):
    """EIP-2124 with the timestamps of EIP-6122: forks by block, then by time."""
    blocks, times = fork_list(blocks, times, int(genesis_time))
    head, time = int(head), int(time)
    crc = zlib.crc32(unhex(genesis))
    for fork in blocks:
        if fork <= head:
            crc = zlib.crc32(fork.to_bytes(8, "big"), crc)
            continue
        return f"{crc:08x} {fork}"
    for fork in times:
        if fork <= time:
            crc = zlib.crc32(fork.to_bytes(8, "big"), crc)
            continue
        return f"{crc:08x} {fork}"
    return f"{crc:08x} 0"


def forkid_validate(genesis, blocks, times, genesis_time, head, time, rhash, rnext):
    """The filter of geth's forkid.newFilter, which EIP-6122 cites as the rules."""
    blocks, times = fork_list(blocks, times, int(genesis_time))
    head, time = int(head), int(time)
    rhash, rnext = int(rhash, 16), int(rnext)
    forks = blocks + times + [2**64 - 1]
    sums = checksums(unhex(genesis), blocks + times)
    for i, fork in enumerate(forks):
        local = head if i < len(blocks) else time
        if local >= fork:
            continue
        if sums[i] == rhash:
            if rnext > 0 and (head >= rnext or (rnext > 1438269973 and time >= rnext)):
                return "local stale"
            return "ok"
        for j in range(i):
            if sums[j] == rhash:
                return "ok" if forks[j] == rnext else "remote stale"
        for j in range(i + 1, len(sums)):
            if sums[j] == rhash:
                return "ok"
        return "local stale"
    return "unreachable"


MAINNET_BLOCKS = [
    1150000, 1920000, 2463000, 2675000, 4370000, 7280000, 9069000, 9200000,
    12244000, 12965000, 13773000, 15050000,
]  # fmt: skip
MAINNET_TIMES = [1681338455, 1710338135, 1746612311, 1764798551, 1765290071, 1767747671]
MAINNET_GENESIS = "d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3"
# The fork identifiers that EIP-2124 and EIP-6122 list for mainnet, by head.
MAINNET_VECTORS = {
    (0, 0): "fc64ec04 1150000",
    (1149999, 0): "fc64ec04 1150000",
    (1150000, 0): "97c2c34c 1920000",
    (1919999, 0): "97c2c34c 1920000",
    (1920000, 0): "91d1f948 2463000",
    (2463000, 0): "7a64da13 2675000",
    (2675000, 0): "3edd5b10 4370000",
    (4370000, 0): "a00bc324 7280000",
    (7280000, 0): "668db0af 9069000",
    (9069000, 0): "879d6e30 9200000",
    (9200000, 0): "e029e991 12244000",
    (12244000, 0): "0eb440f6 12965000",
    (12965000, 0): "b715077d 13773000",
    (13773000, 0): "20c327fc 15050000",
    (15050000, 0): "f0afd0e3 1681338455",
    (20000000, 1681338455): "dce96c2d 1710338135",
    (20000000, 1710338135): "9f3d2254 1746612311",
}


def forkid_mainnet(head, time):
    """Mainnet's identifier: from the lists of this file, and the EIPs' where they give one."""
    blocks = ",".join(map(str, MAINNET_BLOCKS))
    times = ",".join(map(str, MAINNET_TIMES))
    ours = forkid(MAINNET_GENESIS, blocks, times, "0", head, time)
    vector = MAINNET_VECTORS.get((int(head), int(time)))
    if vector is not None and vector != ours:
        return f"the vector {vector} is not the model's {ours}"
    return ours


TOPIC = re.compile(r"/eth2/([0-9a-f]{8})/([^/]*)/ssz_snappy", re.DOTALL)
SUBNET = re.compile(r"_(0|[1-9][0-9]*)")


def topic(word):
    """A gossip topic of the consensus layer: its fork digest and its name."""
    match = TOPIC.fullmatch(unhex(word).decode("utf-8"))
    if match is None:
        raise MalformedError("not a topic")
    return f"{match.group(1)} {tohex(match.group(2).encode())}"


def subnet_name(base, word):
    """The subnet of a topic name `base_N`, with N a decimal 64-bit number."""
    name, base = unhex(word).decode("utf-8"), unhex(base).decode("utf-8")
    if not name.startswith(base):
        raise MalformedError("base")
    match = SUBNET.fullmatch(name[len(base) :])
    if match is None or int(match.group(1)) >= 2**64:
        raise MalformedError("not a subnet")
    return match.group(1)


def message_id(altair, topic, data):
    topic, data = unhex(topic), unhex(data)
    try:
        body = bytes(cramjam.snappy.decompress_raw(data))
        domain = bytes([1, 0, 0, 0])
    except Exception:
        body = data
        domain = bytes(4)
    if altair == "1":
        body = len(topic).to_bytes(8, "little") + topic + body
    return hashlib.sha256(domain + body).digest()[:20].hex()


def shuffle(index, count, seed):
    """The stand-in shuffle that the driver passes to EthLib: a rotation by the seed."""
    return (index + int.from_bytes(seed[:8], "little")) % count


def subnets(node, epoch, per, count, extra, n):
    node, epoch, per, count, extra, n = map(int, (node, epoch, per, count, extra, n))
    bits = (count - 1).bit_length() + extra
    prefix = node >> (256 - bits)
    offset = node % per
    seed = hashlib.sha256(((epoch + offset) // per).to_bytes(8, "little")).digest()
    permuted = shuffle(prefix, 1 << bits, seed)
    return ",".join(str((permuted + i) % count) for i in range(n)) or "-"


HANDLERS = {
    "pb_varint": pb_varint,
    "uvarint": uvarint,
    "quic_varint_dec": quic_varint_dec,
    "quic_varint_enc": quic_varint_enc,
    "quic_pn": quic_pn,
    "quic_initial": quic_initial,
    "quic_keys": quic_keys,
    "quic_protect": quic_protect,
    "forkid": forkid,
    "forkid_validate": forkid_validate,
    "forkid_mainnet": forkid_mainnet,
    "topic": topic,
    "subnet_name": subnet_name,
    "message_id": message_id,
    "subnets": subnets,
}

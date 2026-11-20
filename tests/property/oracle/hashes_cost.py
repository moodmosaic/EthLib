"""The work of PBKDF2 and scrypt, counted while they run, from RFC 2104, 8018 and 7914."""

# `cost(kdf, password)` gives the bytes of the buffers and the count of block functions.
#
# The count is not a formula: it grows as the derivation runs.
# Each SHA-256 call adds the blocks of its padded message (FIPS 180-4 section 5.1.1).
# Each Salsa20/8 core adds one.
# The outputs are checked against hashlib, so the count is of a correct derivation.
# The bytes of the buffers have no source but the text of `Keystore.Kdf.memory`.

import hashlib
import struct

M32 = 0xFFFFFFFF
COUNT = {"sha": 0, "salsa": 0}


def sha256(data):
    COUNT["sha"] += (len(data) + 1 + 8 + 63) // 64
    return hashlib.sha256(data).digest()


def hmac(key, message):
    """RFC 2104 section 2, with no state kept between calls."""
    if len(key) > 64:
        key = sha256(key)
    key = key.ljust(64, b"\x00")
    inner = sha256(bytes(b ^ 0x36 for b in key) + message)
    return sha256(bytes(b ^ 0x5C for b in key) + inner)


def xor(a, b):
    return bytes(p ^ q for p, q in zip(a, b, strict=True))


def pbkdf2(password, salt, count, length):
    """RFC 8018 section 5.2."""
    out = b""
    for i in range(1, -(-length // 32) + 1):
        u = hmac(password, salt + struct.pack(">I", i))
        t = u
        for _ in range(count - 1):
            u = hmac(password, u)
            t = xor(t, u)
        out += t
    return out[:length]


def rotl32(x, n):
    return ((x << n) | (x >> (32 - n))) & M32


def salsa208(block):
    """RFC 7914 section 3."""
    COUNT["salsa"] += 1
    x = list(struct.unpack("<16I", block))
    start = list(x)

    def quarter(a, b, c, d):
        x[b] ^= rotl32((x[a] + x[d]) & M32, 7)
        x[c] ^= rotl32((x[b] + x[a]) & M32, 9)
        x[d] ^= rotl32((x[c] + x[b]) & M32, 13)
        x[a] ^= rotl32((x[d] + x[c]) & M32, 18)

    for _ in range(4):
        quarter(0, 4, 8, 12)
        quarter(5, 9, 13, 1)
        quarter(10, 14, 2, 6)
        quarter(15, 3, 7, 11)
        quarter(0, 1, 2, 3)
        quarter(5, 6, 7, 4)
        quarter(10, 11, 8, 9)
        quarter(15, 12, 13, 14)
    return struct.pack("<16I", *[(a + b) & M32 for a, b in zip(x, start, strict=True)])


def blockmix(data, r):
    """RFC 7914 section 4."""
    x = data[-64:]
    y = []
    for i in range(2 * r):
        x = salsa208(xor(x, data[64 * i : 64 * i + 64]))
        y.append(x)
    return b"".join(y[0::2] + y[1::2])


def romix(data, n, r):
    """RFC 7914 section 5."""
    x = data
    table = []
    for _ in range(n):
        table.append(x)
        x = blockmix(x, r)
    for _ in range(n):
        j = int.from_bytes(x[-64:], "little") % n
        x = blockmix(xor(x, table[j]), r)
    return x


def scrypt(password, salt, n, r, p, length):
    """RFC 7914 section 6."""
    b = pbkdf2(password, salt, 1, p * 128 * r)
    mixed = b"".join(romix(b[128 * r * i : 128 * r * (i + 1)], n, r) for i in range(p))
    return pbkdf2(password, mixed, 1, length)


def counted(run):
    COUNT["sha"] = COUNT["salsa"] = 0
    out = run()
    return out, COUNT["sha"] + COUNT["salsa"]


def cost(kdf, password):
    """The memory and the work of the key derivation of a keystore module, or none.

    None when the parameters are not ones that the derivation accepts.
    """
    params = kdf.get("params", {})
    try:
        salt = bytes.fromhex(params["salt"])
        length = params["dklen"]
        blocks = -(-length // 32) * 32
        if kdf["function"] == "pbkdf2":
            count = params["c"]
            if count < 1 or length < 1:
                return None
            _, work = counted(lambda: pbkdf2(password, salt, count, length))
            return blocks + length, work
        if kdf["function"] == "scrypt":
            n, r, p = params["n"], params["r"], params["p"]
            if r < 1 or p < 1 or length < 1 or n < 2 or n & (n - 1) or n >= 2 ** (16 * r):
                return None
            _, work = counted(lambda: scrypt(password, salt, n, r, p, length))
            return 128 * r * n + 4 * 128 * r * p + blocks + length, work
    except (KeyError, ValueError, TypeError):
        return None
    return None


def selftest():
    """The counted derivations give the keys of hashlib."""
    for password, salt, count, length in ((b"pw", b"salt", 3, 70), (b"p" * 100, b"", 1, 32)):
        got, _ = counted(lambda: pbkdf2(password, salt, count, length))  # noqa: B023
        assert got == hashlib.pbkdf2_hmac("sha256", password, salt, count, length)
    got, work = counted(lambda: scrypt(b"pw", b"salt", 8, 2, 2, 40))
    assert got == hashlib.scrypt(b"pw", salt=b"salt", n=8, r=2, p=2, dklen=40)
    # Each of 2 blocks takes 2 N BlockMix calls of 2 r cores: 128 cores in all.
    assert COUNT["salsa"] == 4 * 8 * 2 * 2
    assert work == COUNT["sha"] + COUNT["salsa"]


selftest()

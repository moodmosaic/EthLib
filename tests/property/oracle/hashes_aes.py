"""Rijndael and GCM written from FIPS 197 and SP 800-38D, at any key and round count."""

# rijndael <nk> <nr> <key> <block>     CIPHER of FIPS 197 Algorithm 1 after KEYEXPANSION.
# rijndaelinv <nk> <nr> <key> <block>  INVCIPHER of Algorithm 3.
# gcm_chosen <key> <j0> <p> <aad>      The 16-byte IV whose pre-counter block is j0, then C and T.
# gf128 <x> <y>                        The product of two blocks in GF(2^128).
# ghash <h> <data>                     GHASH of whole blocks under any hash subkey.
#
# A library has AES at three key sizes and no way to choose the pre-counter block of GCM.
# The transcriptions are checked against `cryptography` at start, where the library runs.

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

M32 = 0xFFFFFFFF


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return data.hex() if data else "-"


# FIPS 197 section 4: the field GF(2^8) modulo x^8 + x^4 + x^3 + x + 1.


def xtimes(b):
    return ((b << 1) ^ 0x1B) & 0xFF if b & 0x80 else b << 1


def gmul(a, b):
    product = 0
    while b:
        if b & 1:
            product ^= a
        a = xtimes(a)
        b >>= 1
    return product


def rotl8(b, n):
    return ((b << n) | (b >> (8 - n))) & 0xFF


def make_sbox():
    """Section 5.1.1: the inverse in the field, then the affine map of (5.3)."""
    box = []
    for x in range(256):
        inverse = next((y for y in range(256) if gmul(x, y) == 1), 0)
        box.append(
            inverse
            ^ rotl8(inverse, 1)
            ^ rotl8(inverse, 2)
            ^ rotl8(inverse, 3)
            ^ rotl8(inverse, 4)
            ^ 0x63
        )
    return box


SBOX = make_sbox()
INV_SBOX = [SBOX.index(x) for x in range(256)]


def key_expansion(nk, nr, key):
    """Algorithm 2: the words w[0 .. 4 Nr + 3]."""
    w = [list(key[4 * i : 4 * i + 4]) for i in range(nk)]
    for i in range(nk, 4 * (nr + 1)):
        temp = list(w[i - 1])
        if i % nk == 0:
            temp = [SBOX[b] for b in temp[1:] + temp[:1]]
            rcon = 1
            for _ in range(i // nk - 1):
                rcon = xtimes(rcon)
            temp[0] ^= rcon
        elif nk > 6 and i % nk == 4:
            temp = [SBOX[b] for b in temp]
        w.append([a ^ b for a, b in zip(w[i - nk], temp, strict=True)])
    return w[: 4 * (nr + 1)]


def add_round_key(state, w, round_index):
    """Section 5.1.4: byte s[r, c] is at index r + 4 c, and the key word of column c is w[c]."""
    return [state[i] ^ w[4 * round_index + i // 4][i % 4] for i in range(16)]


def shift_rows(state, inverse=False):
    """Section 5.1.2: s'[r, c] = s[r, (c + r) mod 4], and the other way for the inverse."""
    sign = -1 if inverse else 1
    return [state[i % 4 + 4 * ((i // 4 + sign * (i % 4)) % 4)] for i in range(16)]


def mix_columns(state, matrix):
    """Section 5.1.3: each column times the circulant matrix of the given first row."""
    out = []
    for c in range(4):
        column = state[4 * c : 4 * c + 4]
        for r in range(4):
            byte = 0
            for k in range(4):
                byte ^= gmul(matrix[(k - r) % 4], column[k])
            out.append(byte)
    return out


def cipher(nr, w, block):
    """Algorithm 1."""
    state = add_round_key(list(block), w, 0)
    for round_index in range(1, nr):
        state = [SBOX[b] for b in state]
        state = shift_rows(state)
        state = mix_columns(state, [2, 3, 1, 1])
        state = add_round_key(state, w, round_index)
    state = shift_rows([SBOX[b] for b in state])
    return bytes(add_round_key(state, w, nr))


def inv_cipher(nr, w, block):
    """Algorithm 3."""
    state = add_round_key(list(block), w, nr)
    for round_index in range(nr - 1, 0, -1):
        state = [INV_SBOX[b] for b in shift_rows(state, inverse=True)]
        state = add_round_key(state, w, round_index)
        state = mix_columns(state, [0x0E, 0x0B, 0x0D, 0x09])
    state = [INV_SBOX[b] for b in shift_rows(state, inverse=True)]
    return bytes(add_round_key(state, w, 0))


def ecb(key, block, decrypt=False):
    op = Cipher(algorithms.AES(key), modes.ECB())
    op = op.decryptor() if decrypt else op.encryptor()
    return op.update(block) + op.finalize()


# SP 800-38D: blocks are integers, the first bit most significant.

ONE = 1 << 127


def gf_mul(x, y):
    """Section 6.3, Algorithm 1."""
    z, v = 0, y
    for i in range(128):
        if (x >> (127 - i)) & 1:
            z ^= v
        v = (v >> 1) ^ (0xE1 << 120) if v & 1 else v >> 1
    return z


def reflect(x):
    """The block read with its last bit most significant: bit `i` is the coefficient of x^i."""
    return int(f"{x:0128b}"[::-1], 2)


def gf_mul_poly(x, y):
    """The same product as polynomials: multiply, then reduce by x^128 + x^7 + x^2 + x + 1.

    Section 6.3 names this field; Algorithm 1 is one way to compute in it, and this is another.
    """
    a, b, product = reflect(x), reflect(y), 0
    while b:
        if b & 1:
            product ^= a
        a <<= 1
        b >>= 1
    for degree in range(product.bit_length() - 1, 127, -1):
        if (product >> degree) & 1:
            product ^= ((1 << 128) | 0x87) << (degree - 128)
    return reflect(product)


def gf_inv(x):
    """The inverse in GF(2^128): the power 2^128 - 2."""
    result, base, exponent = ONE, x, 2**128 - 2
    while exponent:
        if exponent & 1:
            result = gf_mul(result, base)
        base = gf_mul(base, base)
        exponent >>= 1
    return result


def ghash(h, data):
    """Section 6.4, Algorithm 2, on whole blocks."""
    y = 0
    for i in range(0, len(data), 16):
        y = gf_mul(y ^ int.from_bytes(data[i : i + 16], "big"), h)
    return y


def pad16(data):
    return data + bytes(-len(data) % 16)


def inc32(block):
    return block[:12] + ((int.from_bytes(block[12:], "big") + 1) & M32).to_bytes(4, "big")


def gcm(key, iv, p, aad):
    """Section 7.1, Algorithm 4, with a tag of 16 bytes; also the pre-counter block."""
    h = int.from_bytes(ecb(key, bytes(16)), "big")
    if len(iv) == 12:
        j0 = iv + b"\x00\x00\x00\x01"
    else:
        lengths = bytes(8) + (8 * len(iv)).to_bytes(8, "big")
        j0 = ghash(h, pad16(iv) + lengths).to_bytes(16, "big")
    counter, c = inc32(j0), b""
    for i in range(0, len(p), 16):
        stream = ecb(key, counter)
        c += bytes(a ^ b for a, b in zip(p[i : i + 16], stream, strict=False))
        counter = inc32(counter)
    lengths = (8 * len(aad)).to_bytes(8, "big") + (8 * len(c)).to_bytes(8, "big")
    s = ghash(h, pad16(aad) + pad16(c) + lengths).to_bytes(16, "big")
    tag = bytes(a ^ b for a, b in zip(ecb(key, j0), s, strict=True))
    return j0, c, tag


def iv_for(key, j0):
    """The IV of 16 bytes that GHASH takes to the pre-counter block `j0`.

    Section 7.1 step 2 gives `J0 = (IV * H + L) * H` for one block of IV, `L` its length block.
    """
    h_inv = gf_inv(int.from_bytes(ecb(key, bytes(16)), "big"))
    iv = gf_mul(gf_mul(int.from_bytes(j0, "big"), h_inv) ^ 128, h_inv)
    return iv.to_bytes(16, "big")


def library_gcm(key, iv, p, aad):
    op = Cipher(algorithms.AES(key), modes.GCM(iv)).encryptor()
    op.authenticate_additional_data(aad)
    c = op.update(p) + op.finalize()
    return c, op.tag


def gcm_chosen(key, j0, p, aad):
    iv = iv_for(key, j0)
    got_j0, c, tag = gcm(key, iv, p, aad)
    assert got_j0 == j0
    # The library takes an IV of 16 bytes, and wraps the 32-bit counter as section 6.5 says.
    assert library_gcm(key, iv, p, aad) == (c, tag)
    return iv, c, tag


def answer(w):
    match w:
        case ["rijndael", nk, nr, key, block]:
            schedule = key_expansion(int(nk), int(nr), unhex(key))
            return cipher(int(nr), schedule, unhex(block)).hex()
        case ["rijndaelinv", nk, nr, key, block]:
            schedule = key_expansion(int(nk), int(nr), unhex(key))
            return inv_cipher(int(nr), schedule, unhex(block)).hex()
        case ["gf128", x, y]:
            x, y = int(x, 16), int(y, 16)
            assert gf_mul(x, y) == gf_mul_poly(x, y)
            return f"{gf_mul(x, y):032x}"
        case ["ghash", h, data]:
            return f"{ghash(int(h, 16), unhex(data)):032x}"
        case ["gcm_chosen", key, j0, p, aad]:
            iv, c, tag = gcm_chosen(unhex(key), unhex(j0), unhex(p), unhex(aad))
            return f"{iv.hex()} {tohex(c)} {tag.hex()}"
    return None


def selftest():
    """The transcriptions agree with the library before they judge EthLib."""
    block = bytes(range(16))
    for nk, nr in ((4, 10), (6, 12), (8, 14)):
        key = bytes(range(40, 40 + 4 * nk))
        schedule = key_expansion(nk, nr, key)
        assert cipher(nr, schedule, block) == ecb(key, block)
        assert inv_cipher(nr, schedule, block) == ecb(key, block, decrypt=True)
    key, p, aad = bytes(range(16)), bytes(range(70)), bytes(range(20))
    for size in (8, 12, 16, 17, 32, 60):
        iv = bytes(range(100, 100 + size))
        _, c, tag = gcm(key, iv, p, aad)
        assert library_gcm(key, iv, p, aad) == (c, tag)
    for x, y in ((ONE, 5), (3 << 100, 1), (2**128 - 1, 2**128 - 1), (0xE1 << 120, 1 << 126)):
        assert gf_mul(x, y) == gf_mul_poly(x, y)
    assert gf_mul(ONE, 12345) == 12345
    # A counter that wraps in the first block of the text, and one that wraps later.
    for low in (0xFFFFFFFF, 0xFFFFFFFD):
        gcm_chosen(key, bytes(12) + low.to_bytes(4, "big"), p, aad)


selftest()

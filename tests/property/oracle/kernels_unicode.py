"""NFKD data for every code point: the host's tables, or a `UnicodeData.txt` named by a variable."""

# uni <start> <count> <entries>   Compare the entries of a range of code points.
# uniorder <code points>          NFKD of a string, or skip when the reference lacks one.
#
# An entry is `code:class:d1.d2...`, in hexadecimal.
# A code point has one when its combining class is not 0 or its full decomposition is not itself.
#
# `ETHLIB_UCD` names a `UnicodeData.txt`.
# EthLib's tables are those of Unicode 16.0.0.
# Without `ETHLIB_UCD` the reference is `unicodedata`.
# Then a code point that the host's version does not assign is counted and not compared.

import os
import unicodedata

HANGUL = range(0xAC00, 0xAC00 + 11172)


def load(path):
    decomposition, combining = {}, {}
    with open(path) as file:
        for line in file:
            fields = line.split(";")
            code = int(fields[0], 16)
            if fields[3] != "0":
                combining[code] = int(fields[3])
            if fields[5]:
                parts = fields[5].split()
                if parts[0].startswith("<"):
                    parts = parts[1:]
                decomposition[code] = [int(part, 16) for part in parts]
    return decomposition, combining


UCD = load(os.environ["ETHLIB_UCD"]) if os.environ.get("ETHLIB_UCD") else None
VERSION = "the file ETHLIB_UCD" if UCD else f"unicodedata {unicodedata.unidata_version}"


def hangul(code):
    # Unicode 16.0.0, section 3.12.2.
    index = code - 0xAC00
    parts = [0x1100 + index // 588, 0x1161 + index % 588 // 28]
    return parts + ([0x11A7 + index % 28] if index % 28 else [])


def full(code):
    if code in HANGUL:
        return hangul(code)
    if code in UCD[0]:
        return [part for piece in UCD[0][code] for part in full(piece)]
    return [code]


def known(code):
    return UCD is not None or unicodedata.category(chr(code)) != "Cn"


def entry(code):
    if UCD is not None:
        return full(code), UCD[1].get(code, 0)
    char = chr(code)
    return [ord(c) for c in unicodedata.normalize("NFKD", char)], unicodedata.combining(char)


def show(code, parts, combining):
    return f"{code:x}:{combining:x}:{'.'.join(f'{part:x}' for part in parts)}"


def uni(start, count, words):
    got = {}
    for word in words:
        code, combining, parts = word.split(":")
        got[int(code, 16)] = (int(combining, 16), [int(part, 16) for part in parts.split(".")])
    compared = skipped = 0
    for code in range(start, start + count):
        if 0xD800 <= code < 0xE000:
            continue
        mine = got.get(code, (0, [code]))
        if not known(code):
            # A newer version may assign it; an older one cannot have an entry for it.
            skipped += mine != (0, [code])
            continue
        parts, combining = entry(code)
        compared += 1
        if (combining, parts) != mine:
            return f"differs {show(code, parts, combining)} {show(code, mine[1], mine[0])}"
    return f"ok {compared} {skipped} {VERSION}"


def order(points):
    text = "".join(chr(point) for point in points)
    if UCD is None:
        if any(unicodedata.category(c) in ("Cn", "Cs") for c in text):
            return "skip"
        return " ".join(f"{ord(c):x}" for c in unicodedata.normalize("NFKD", text)) or "-"
    # Unicode 16.0.0, section 3.11: decompose, then sort each run of non-starters.
    out = []
    for point in points:
        out.extend(full(point))
    i = 0
    while i < len(out):
        j = i
        while j < len(out) and UCD[1].get(out[j], 0) != 0:
            j += 1
        out[i:j] = sorted(out[i:j], key=lambda c: UCD[1].get(c, 0))
        i = j + 1
    return " ".join(f"{c:x}" for c in out) or "-"


def answer(words):
    match words:
        case ["uni", start, count, *entries]:
            return uni(int(start), int(count), entries)
        case ["uniorder", *points]:
            return order([int(point, 16) for point in points])
    return None

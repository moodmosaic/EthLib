"""References for the base layer: one command per line, one answer per line."""

# b64enc <hex>             URL-safe base64 without padding (RFC 4648, section 5).
# b64dec <hex of text>     Its bytes, or error unless the text is canonical.
# nfkd <code points>       NFKD by the host's Unicode tables, or skip.
# isqrt <n>                The integer square root.

import base64
import math
import sys
import unicodedata


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return data.hex() if data else "-"


def b64dec(text):
    # The reference decodes leniently, so canonical means it encodes back.
    try:
        chars = text.decode("ascii")
    except UnicodeDecodeError:
        return "error"
    if "=" in chars or len(chars) % 4 == 1:
        return "error"
    try:
        data = base64.b64decode(chars + "=" * (-len(chars) % 4), altchars=b"-_", validate=True)
    except ValueError:
        return "error"
    canonical = base64.urlsafe_b64encode(data).rstrip(b"=")
    return tohex(data) if canonical == text else "error"


def nfkd(words):
    points = [int(word, 16) for word in words]
    text = "".join(chr(point) for point in points)
    # The host's tables may be older than EthLib's: skip what they lack.
    if any(unicodedata.category(c) in ("Cn", "Cs") for c in text):
        return "skip"
    out = unicodedata.normalize("NFKD", text)
    return " ".join(format(ord(c), "x") for c in out) or "-"


def answer(words):
    match words:
        case ["b64enc", data]:
            return base64.urlsafe_b64encode(unhex(data)).rstrip(b"=").decode()
        case ["b64dec", text]:
            return b64dec(unhex(text))
        case ["nfkd", *points]:
            return nfkd(points)
        case ["isqrt", n]:
            return str(math.isqrt(int(n)))
    return "error unknown command"


for line in sys.stdin:
    print(answer(line.rstrip("\n").split("\t")) or "-", flush=True)

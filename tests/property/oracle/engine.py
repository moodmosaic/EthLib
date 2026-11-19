"""References for the Engine API layer: one command per line, one answer per line."""

#     wire <kind> <hex of JSON text>      A base type by base-types.yaml and by common.md.
#     jwtmint <secret> <header> <claims>  The HS256 tag of two encoded parts, encoded.
#     jwtcheck <secret> <clock> <token>   Whether the Engine profile accepts a token.
#     jwtiat <secret> <token>             The iat claim of a token that PyJWT verifies.
#     method <hex of name>                Whether a name is a method with its version.
#     methods                             The methods the specification defines.
#     shape <name> <hex of JSON text>     The version of a structure that a value has, or 0.
#     reads <name> <hex of JSON text>     Whether a value is a structure of a response.
#     newpayload <hex of a case>          The answers allowed for a call, and its parameters.
#
# The rules are written from execution-apis at commit 3284ee8: src/engine/*.md and
# src/schemas/base-types.yaml.

import base64
import hashlib
import hmac
import json
import os
import re
import sys
import warnings
from fractions import Fraction

import jwt

# With -I the directory of the script is not on the path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import engine_payload  # noqa: E402

sys.set_int_max_str_digits(0)
warnings.simplefilter("ignore")


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return data.hex() if data else "-"


# base-types.yaml: the pattern of each type, copied from the file.
YAML = {
    "address": r"^0x[0-9a-fA-F]{40}$",
    "bytes": r"^0x[0-9a-f]*$",
    "bytesMax32": r"^0x[0-9a-f]{0,64}$",
    "bytes4": r"^0x[0-9a-f]{8}$",
    "bytes8": r"^0x[0-9a-f]{16}$",
    "bytes16": r"^0x[0-9a-f]{32}$",
    "bytes32": r"^0x[0-9a-f]{64}$",
    "bytes48": r"^0x[0-9a-f]{96}$",
    "bytes256": r"^0x[0-9a-f]{512}$",
    "uint": r"^0x(0|[1-9a-f][0-9a-f]*)$",
    "uint64": r"^0x(0|[1-9a-f][0-9a-f]{0,15})$",
    "uint256": r"^0x(0|[1-9a-f][0-9a-f]{0,63})$",
}

# common.md, Encoding: the two patterns of the Engine API itself.
COMMON_DATA = r"^0x(?:[a-fA-F0-9]{2})*$"
COMMON_QUANTITY = r"^0x(?:0|(?:[a-fA-F1-9][a-fA-F0-9]*))$"

# The size in bytes of a DATA type, or the size in bits of a QUANTITY type.
DATA_SIZE = {
    "address": (20, 20),
    "bytes": (0, None),
    "bytesMax32": (0, 32),
    "bytes4": (4, 4),
    "bytes8": (8, 8),
    "bytes16": (16, 16),
    "bytes32": (32, 32),
    "bytes48": (48, 48),
    "bytes256": (256, 256),
}
QUANTITY_BITS = {"uint": None, "uint64": 64, "uint256": 256}


def fullmatch(pattern, text):
    # Python's $ also matches before a final newline, so use \Z.
    return re.match(pattern[:-1] + r"\Z", text) is not None


def wire(kind, text):
    """Two verdicts on a JSON value: the schema's and the Encoding section's."""
    try:
        value = json.loads(text.decode("utf-8"))
    except ValueError:
        return "error error -"
    if not isinstance(value, str):
        return "error error -"
    by_yaml = fullmatch(YAML[kind], value)
    if kind in DATA_SIZE:
        # The pattern of `bytes` also matches half a byte, which names no byte string.
        by_yaml = by_yaml and len(value) % 2 == 0
        low, high = DATA_SIZE[kind]
        by_common = fullmatch(COMMON_DATA, value)
        if by_common:
            size = (len(value) - 2) // 2
            by_common = low <= size and (high is None or size <= high)
        shown = tohex(bytes.fromhex(value[2:])) if by_common else "-"
    else:
        bits = QUANTITY_BITS[kind]
        by_common = fullmatch(COMMON_QUANTITY, value)
        if by_common and bits is not None:
            by_common = int(value[2:], 16) < 2**bits
        shown = str(int(value[2:], 16)) if by_common else "-"

    def verdict(ok):
        return "ok" if ok else "error"

    return f"{verdict(by_yaml)} {verdict(by_common)} {shown}"


# PyJWT checks the tag, the algorithm and the form only: authentication.md has the
# reader ignore every claim but iat, so exp and nbf must not count.
PYJWT_OPTIONS = {
    "verify_iat": False,
    "verify_exp": False,
    "verify_nbf": False,
    "verify_aud": False,
    "verify_iss": False,
}

# JWT: RFC 7515 (compact form, base64url without padding), RFC 7518 section 3.2
# (HS256), RFC 7519 (NumericDate), RFC 8259 (JSON) and authentication.md.


def b64url(data):
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode()


def b64url_strict(text):
    """The bytes of a canonical base64url text without padding, or None."""
    if not re.fullmatch(r"[A-Za-z0-9_-]*", text) or len(text) % 4 == 1:
        return None
    data = base64.urlsafe_b64decode(text + "=" * (-len(text) % 4))
    return data if b64url(data) == text else None


class Number:
    """A JSON number as mantissa * 10 ** exponent, never expanded."""

    def __init__(self, text):
        m = re.fullmatch(r"(-?)(\d+)(?:\.(\d+))?(?:[eE]([-+]?\d+))?", text)
        sign, whole, fraction, exponent = m.groups()
        fraction = fraction or ""
        self.mantissa = int(whole + fraction) * (-1 if sign else 1)
        self.exponent = int(exponent or "0") - len(fraction)

    def within(self, low, high):
        """Whether low <= value <= high, for integers low and high."""
        if self.mantissa == 0:
            return low <= 0 <= high
        if self.exponent > 100:
            # Larger in magnitude than any clock this oracle is asked about.
            assert max(abs(low), abs(high)) < 10**100
            return False
        if self.exponent < -(len(str(abs(self.mantissa))) + 2):
            # Strictly between 0 and 1 in magnitude.
            return low <= 0 and high >= 1 if self.mantissa > 0 else low <= -1 and high >= 0
        value = Fraction(self.mantissa) * Fraction(10) ** self.exponent
        return low <= value <= high


def refuse(_):
    raise ValueError("not JSON")


def json_object(data):
    """The members of a part that is one JSON object in UTF-8, or None."""
    try:
        value = json.loads(
            data.decode("utf-8"), parse_float=Number, parse_int=Number, parse_constant=refuse
        )
    except (ValueError, RecursionError):
        return None
    return value if isinstance(value, dict) else None


def jwtcheck(secret, clock, token):
    """Whether an execution client of the Engine profile accepts the token."""
    if len(secret) != 32:
        return "error secret"
    parts = token.split(".")
    if len(parts) != 3:
        return "error compact"
    tag = b64url_strict(parts[2])
    signed = (parts[0] + "." + parts[1]).encode()
    if tag is None or not hmac.compare_digest(
        tag, hmac.new(secret, signed, hashlib.sha256).digest()
    ):
        return "error signature"
    header_bytes, claims_bytes = b64url_strict(parts[0]), b64url_strict(parts[1])
    header = json_object(header_bytes) if header_bytes is not None else None
    if header is None:
        return "error header"
    if "crit" in header:
        return "error critical"
    if header.get("alg") != "HS256" or not isinstance(header.get("alg"), str):
        return "error algorithm"
    claims = json_object(claims_bytes) if claims_bytes is not None else None
    if claims is None or not isinstance(claims.get("iat"), Number):
        return "error claims"
    if not claims["iat"].within(clock - 60, clock + 60):
        return "error iat"
    # A second opinion on the tag and the algorithm: PyJWT must verify what the model accepts.
    try:
        jwt.decode(token, secret, algorithms=["HS256"], options=PYJWT_OPTIONS)
    except jwt.InvalidTokenError as e:
        return f"conflict {type(e).__name__}"
    return "ok"


def jwtiat(secret, token):
    try:
        claims = jwt.decode(token, secret, algorithms=["HS256"], options=PYJWT_OPTIONS)
    except jwt.InvalidTokenError as e:
        return f"error {type(e).__name__}"
    header = jwt.get_unverified_header(token)
    if set(claims) != {"iat"} or header.get("alg") != "HS256":
        return "error claims"
    return str(claims["iat"])


# The method headings of src/engine/*.md, and the name rule of common.md.
METHODS = """
engine_newPayloadV1 engine_forkchoiceUpdatedV1 engine_getPayloadV1
engine_exchangeTransitionConfigurationV1
engine_newPayloadV2 engine_forkchoiceUpdatedV2 engine_getPayloadV2
engine_getPayloadBodiesByHashV1 engine_getPayloadBodiesByRangeV1
engine_newPayloadV3 engine_forkchoiceUpdatedV3 engine_getPayloadV3 engine_getBlobsV1
engine_newPayloadV4 engine_getPayloadV4
engine_getPayloadV5 engine_getBlobsV2 engine_getBlobsV3
engine_newPayloadV5 engine_getPayloadV6 engine_getPayloadBodiesByHashV2
engine_getPayloadBodiesByRangeV2 engine_forkchoiceUpdatedV4 engine_getBlobsV4
engine_getClientVersionV1
""".split()


def answer(words):
    match words:
        case ["wire", kind, text]:
            return wire(kind, unhex(text))
        case ["jwtmint", secret, header, claims]:
            signed = unhex(header) + b"." + unhex(claims)
            return b64url(hmac.new(unhex(secret), signed, hashlib.sha256).digest())
        case ["jwtcheck", secret, clock, token]:
            try:
                text = unhex(token).decode("utf-8")
            except UnicodeDecodeError:
                return "error utf8"
            return jwtcheck(unhex(secret), int(clock), text)
        case ["jwtiat", secret, token]:
            return jwtiat(unhex(secret), unhex(token).decode())
        case ["method", name]:
            text = unhex(name).decode("utf-8")
            return "ok" if re.fullmatch(r"engine_[A-Za-z]+V[1-9][0-9]*", text) else "error"
        case ["newpayload", case]:
            return engine_payload.new_payload(unhex(case).decode())
        case ["shape", name, text]:
            return engine_payload.shape(name, unhex(text).decode())
        case ["reads", name, text]:
            return engine_payload.reads(name, unhex(text).decode())
        case ["methods"]:
            return " ".join(sorted(METHODS))
    return None


def main():
    for line in sys.stdin:
        words = line.rstrip("\n").split("\t")
        try:
            result = answer(words)
        except Exception as e:  # The driver must see a reason, not a dead pipe.
            result = f"crash {type(e).__name__}: {e}".replace("\n", " ")
        print(result if result is not None else "crash unknown command", flush=True)


if __name__ == "__main__":
    main()

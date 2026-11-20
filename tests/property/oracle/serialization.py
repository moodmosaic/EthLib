"""References for the serialization layer: one command per line, one answer per line."""

#     rlpenc <item>            The RLP encoding of an item (pyrlp).
#     rlpdec <hex>             The item of a strict decoding, or error (pyrlp and a model).
#     rlpint <hex>             The scalar of a strict decoding, or error.
#     sszenc <type> <value>    The SSZ bytes and the root (ssz-specs and remerkleable).
#     sszdec <type> <hex>      The bytes written back and the root, or error.
#     ssznode <type> <value> <gindex>   The node at a generalized index, or error.
#     sszgindex <type> <path>  The generalized index of a path.
#     sszposition <type> <step>   The chunk and the bytes of an element, and the chunk count.
#     sszcompat <type> <type>  Whether the two can be options of one CompatibleUnion.
#     sszbounds <type>         The fewest and the most bytes of an encoding.
#     ssztype <type>           Whether the specification lets the declaration name a type.
#     sszjson <type> <value> <document>   Whether the document is the specification's.
#     sszjsonread <type> <document>       The bytes of the value a document holds.
#     spechelpers <indices>    get_helper_indices of the specification.
#     specroot <leaves> <proof> <indices> The root of a proof or of a multiproof.
#     sszdef <type>            The bytes and the root of the default value.
#     ssziszero <type> <value> Whether a value is the default of its type.
#     branchroot <leaf> <branch> <depth> <index>   The root a branch climbs to.
#     helpers <indices>        get_helper_indices of consensus-specs.
#     multiroot <leaves> <proof> <indices>   calculate_multi_merkle_root.
#     branch <leaf> <branch> <depth> <index> <root>   is_valid_merkle_branch.
#     dss <hex>                The two integers of a DER signature (cryptography), or error.
#     dertlv <hex>             One DER tag, length and value, by a model of X.690.
#     dervalid <hex>           Whether one value is DER for its type, by a model of X.690.
#     derint <hex>             The integer of a DER INTEGER, by the model.
#     jsonint <hex of text>    The integer that a JSON number is, or error.
#     rpc <kind> <hex of text> Whether the text matches the pattern of base-types.yaml.
#     e2s <hex>                The records of an e2store file, by a model.
#     modelnode <hash> <type> <value> <gindex>   A node of the tree model, under a hash.
#
# `serialization_params.py` holds the commands of the general functions.
#
# An item or a value or a type is JSON.  Bytes are hexadecimal, `-` for none.

import json
import os
import re
import struct
import sys

# The interpreter runs isolated (-I), so the directory of the script is added by hand.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import serialization_params as params  # noqa: E402
import ssz as spec  # noqa: E402
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature
from remerkleable.basic import boolean, uint8, uint16, uint32, uint64, uint128, uint256
from remerkleable.bitfields import Bitlist, Bitvector
from remerkleable.byte_arrays import ByteList, ByteVector
from remerkleable.complex import Container, List, Vector
from remerkleable.progressive import (
    CompatibleUnion,
    ProgressiveBitlist,
    ProgressiveContainer,
    ProgressiveList,
)
from ssz import paths as spec_paths  # noqa: E402

import rlp

UINTS = {1: uint8, 2: uint16, 4: uint32, 8: uint64, 16: uint128, 32: uint256}

# A scalar of RLP has no bound, and one of 65535 bytes has more digits than Python prints.
sys.set_int_max_str_digits(0)


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return bytes(data).hex() if data else "-"


# RLP.


def rlp_item(obj):
    return [rlp_item(x) for x in obj] if isinstance(obj, list) else bytes.fromhex(obj)


def rlp_json(item):
    return [rlp_json(x) for x in item] if isinstance(item, list) else item.hex()


def rlp_model(data, pos, stop):
    """The item at a position by Appendix B of the Yellow Paper, and the position after."""
    if pos >= stop:
        raise ValueError("short")
    first = data[pos]
    if first < 0x80:
        return data[pos : pos + 1], pos + 1
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
        # BE has no leading zero, and a length below 56 has the short form.
        if digits[0] == 0 or length < 56:
            raise ValueError("length not canonical")
        start = pos + 1 + k
    if start + length > stop:
        raise ValueError("short payload")
    if not is_list:
        if length == 1 and data[start] < 0x80:
            raise ValueError("single byte with a prefix")
        return data[start : start + length], start + length
    items, at = [], start
    while at < start + length:
        item, at = rlp_model(data, at, start + length)
        items.append(item)
    return items, start + length


def rlpdec(data):
    try:
        mine, end = rlp_model(data, 0, len(data))
        if end != len(data):
            raise ValueError("trailing")
        mine = json.dumps(rlp_json(mine), separators=(",", ":"))
    except ValueError:
        mine = "error"
    try:
        theirs = json.dumps(rlp_json(rlp.decode(data, strict=True)), separators=(",", ":"))
    except rlp.exceptions.DecodingError:
        theirs = "error"
    return mine if mine == theirs else f"references differ {mine} {theirs}"


def rlpint(data):
    try:
        item = rlp.decode(data, strict=True)
        # The sedes takes the empty list for 0: a scalar is a byte string (Yellow Paper, B).
        if not isinstance(item, bytes):
            return "error"
        return str(rlp.sedes.big_endian_int.deserialize(item))
    except (rlp.exceptions.RLPException, TypeError):
        return "error"


# SSZ.

TYPES = {}


def ssz_type(t):
    key = json.dumps(t)
    if key not in TYPES:
        TYPES[key] = build_type(t)
    return TYPES[key]


def build_type(t):
    match t:
        case ["bool"]:
            return boolean
        case ["byte"]:
            return uint8
        case ["uint", width]:
            return UINTS[width]
        case ["bvec", n]:
            return ByteVector[n]
        case ["blist", n]:
            return ByteList[n]
        case ["bitvec", n]:
            return Bitvector[n]
        case ["bitlist", n]:
            return Bitlist[n]
        case ["pbitlist"]:
            return ProgressiveBitlist
        case ["vec", elem, n]:
            return Vector[ssz_type(elem), n]
        case ["list", elem, n]:
            return List[ssz_type(elem), n]
        case ["plist", elem]:
            return ProgressiveList[ssz_type(elem)]
        case ["cont", names, fields]:
            notes = {name: ssz_type(f) for name, f in zip(names, fields, strict=False)}
            return type("C", (Container,), {"__annotations__": notes})
        case ["pcont", active, names, fields]:
            notes = {name: ssz_type(f) for name, f in zip(names, fields, strict=False)}
            base = ProgressiveContainer(active_fields=active)
            return type("P", (base,), {"__annotations__": notes})
        case ["union", selectors, options]:
            return CompatibleUnion(
                {s: ssz_type(o) for s, o in zip(selectors, options, strict=False)}
            )
    raise ValueError(f"unknown type {t}")


def ssz_value(t, v):
    typ = ssz_type(t)
    match t:
        case ["bool"]:
            return typ(v)
        case ["uint", _] | ["byte"]:
            return typ(int(v))
        case ["bvec", _] | ["blist", _]:
            return typ(bytes.fromhex(v))
        case ["bitvec", _] | ["bitlist", _] | ["pbitlist"]:
            return typ([bool(b) for b in v])
        case ["vec", elem, n] if len(v) != n:
            # The first reference takes no elements for the default vector: a vector has its count.
            raise ValueError(f"a vector of {n} elements, given {len(v)}")
        case ["vec", elem, _] | ["list", elem, _] | ["plist", elem]:
            return typ([ssz_value(elem, x) for x in v])
        case ["cont", names, fields] | ["pcont", _, names, fields]:
            return typ(**{n: ssz_value(f, x) for n, f, x in zip(names, fields, v, strict=False)})
        case ["union", selectors, options]:
            option = options[selectors.index(v["s"])]
            return typ(selector=v["s"], data=ssz_value(option, v["d"]))
    raise ValueError(f"unknown type {t}")


def sszenc(t, v):
    value = ssz_value(t, v)
    first = f"{tohex(value.encode_bytes())} {value.hash_tree_root().hex()}"
    theirs = spec_value(t, v)
    second = f"{tohex(theirs.encode_bytes())} {bytes(theirs.hash_tree_root()).hex()}"
    return first if first == second else f"references differ {first} {second}"


def sszdec(t, data):
    """What the specification reads, and whether the first reference agrees."""
    try:
        value = spec_type(t).decode_bytes(data)
        theirs = f"{tohex(value.encode_bytes())} {bytes(value.hash_tree_root()).hex()}"
    except spec.SSZError as e:
        theirs = f"error {e.fault.name} {e}".replace("\n", " ")
    try:
        value = ssz_type(t).decode_bytes(data)
        # The first reference skips some checks, and an encoding has one value: write it back.
        if value.encode_bytes() != data:
            first = "error not canonical"
        else:
            first = f"{tohex(data)} {value.hash_tree_root().hex()}"
    except Exception as e:
        first = f"error {type(e).__name__}"
    if first.startswith("error") != theirs.startswith("error"):
        return f"references differ {theirs} | {first}"
    if not first.startswith("error") and first != theirs:
        return f"references differ {theirs} | {first}"
    return theirs


# The specification that EthLib cites for SSZ: the Python of ethereum/ssz-specs.

SPEC_UINTS = {
    1: spec.Uint8,
    2: spec.Uint16,
    4: spec.Uint32,
    8: spec.Uint64,
    16: spec.Uint128,
    32: spec.Uint256,
}
SPEC_TYPES = {}


def spec_type(t):
    key = json.dumps(t)
    if key not in SPEC_TYPES:
        SPEC_TYPES[key] = spec_build(t)
    return SPEC_TYPES[key]


def spec_build(t, sub=None):
    """The declaration in the specification; `sub` builds the types it holds."""
    sub = sub or spec_type
    body = {"__module__": "oracle"}

    def declare(base, **parts):
        return type(base.__name__, (base,), body | parts)

    match t:
        case ["bool"]:
            return spec.Boolean
        case ["byte"]:
            return spec.Byte
        case ["uint", width]:
            if width in SPEC_UINTS:
                return SPEC_UINTS[width]
            return declare(spec.BaseUint, BITS=8 * width)
        case ["bvec", n]:
            return declare(spec.ByteVector, LENGTH=n)
        case ["blist", n]:
            return declare(spec.ByteList, LIMIT=n)
        case ["bitvec", n]:
            return declare(spec.BitVector, LENGTH=n)
        case ["bitlist", n]:
            return declare(spec.BitList, LIMIT=n)
        case ["pbitlist"]:
            return declare(spec.ProgressiveBitList)
        case ["vec", elem, n]:
            return declare(spec.Vector, ELEMENT_TYPE=sub(elem), LENGTH=n)
        case ["list", elem, n]:
            return declare(spec.List, ELEMENT_TYPE=sub(elem), LIMIT=n)
        case ["plist", elem]:
            return declare(spec.ProgressiveList, ELEMENT_TYPE=sub(elem))
        case ["cont", names, fields]:
            if len(names) != len(fields) or len(set(names)) != len(names):
                raise spec.SSZTypeError(spec.TypeFault.NOT_AN_INTEGER, type="", field="", got="")
            notes = {name: sub(f) for name, f in zip(names, fields, strict=True)}
            return declare(spec.Container, __annotations__=notes)
        case ["pcont", active, names, fields]:
            if len(names) != len(fields) or len(set(names)) != len(names):
                raise spec.SSZTypeError(spec.TypeFault.NOT_AN_INTEGER, type="", field="", got="")
            notes = {name: sub(f) for name, f in zip(names, fields, strict=True)}
            return declare(
                spec.ProgressiveContainer,
                ACTIVE_FIELDS=tuple(active),
                __annotations__=notes,
            )
        case ["union", selectors, options]:
            if len(selectors) != len(options) or len(set(selectors)) != len(selectors):
                raise spec.SSZTypeError(spec.TypeFault.NOT_AN_INTEGER, type="", field="", got="")
            chosen = {s: sub(o) for s, o in zip(selectors, options, strict=True)}
            return declare(spec.CompatibleUnion, OPTIONS=chosen)
    raise ValueError(f"unknown type {t}")


def spec_fresh(t):
    """The declaration built anew, so that no two share a class."""
    return spec_build(t, spec_fresh)


def spec_value(t, v):
    """A value of the specification, read from the bytes the first reference writes."""
    return spec_type(t).decode_bytes(ssz_value(t, v).encode_bytes())


def ssztype(t):
    try:
        spec_fresh(t)
        return "ok"
    except spec.SSZError as e:
        return f"error {e.fault.name} {e}".replace("\n", " ")


def spec_document(t, v):
    return json.loads(spec.base.json_writer(spec_type(t)).dump_json(spec_value(t, v)))


def sszjson(t, v, document):
    """Whether a document is the one the specification writes for the value."""
    theirs = spec_document(t, v)
    if theirs == json.loads(document):
        return "ok"
    return "differ " + json.dumps(theirs, separators=(",", ":"))


def sszjsonread(t, document):
    """The bytes of the value the specification reads from a document, or error."""
    from pydantic import ValidationError

    try:
        value = spec.base.json_writer(spec_type(t)).validate_json(document)
    except (ValidationError, spec.SSZError) as e:
        return "error " + str(e).replace("\n", " ")[:200]
    return tohex(value.encode_bytes())


def spec_path(t, path):
    """A path in the words of the specification: names for fields, numbers for the rest."""
    out = []
    for step in path:
        if step in ("len", "active", "selector"):
            key = {
                "len": spec.LENGTH_KEY,
                "active": spec.ACTIVE_FIELDS_KEY,
                "selector": spec.SELECTOR_KEY,
            }
            out.append(key[step])
            t = None
        elif t is not None and t[0] in ("cont", "pcont"):
            names, fields = t[-2], t[-1]
            # A field the type lacks goes under a name it lacks, for the specification to refuse.
            out.append(names[step] if step < len(names) else f"no field {step}")
            t = fields[step] if step < len(names) else None
        elif t is not None and t[0] == "union":
            out.append(step)
            t = dict(zip(t[1], t[2], strict=True)).get(step)
        else:
            out.append(step)
            t = None if t is None or is_basic(t) else elem_of(t)
    return out


# A tree written from the text of the specification.
# It answers for nodes that the reference keeps collapsed.
# A leaf is a chunk, or a value with a tree of its own.

ZERO = b"\0" * 32


def zero_root(depth):
    node = ZERO
    for _ in range(depth):
        node = sha(node, node)
    return node


def pack(data):
    data = data + b"\0" * (-len(data) % 32)
    return [("chunk", data[i : i + 32]) for i in range(0, len(data), 32)]


def pack_bits(bits):
    out = bytearray((len(bits) + 7) // 8)
    for i, bit in enumerate(bits):
        out[i // 8] |= bit << (i % 8)
    return pack(bytes(out))


def basic_bytes(t, v):
    return bytes([v]) if t[0] == "bool" else int(v).to_bytes(t[1], "little")


def word(n):
    return n.to_bytes(32, "little")


def tree_layout(t, v):
    """The leaves of a value, the count of leaves of its tree or None, and the word mixed in."""

    def elements(elem, items):
        if is_basic(elem):
            return pack(b"".join(basic_bytes(elem, x) for x in items))
        return [("value", elem, x) for x in items]

    match t:
        case ["bool"] | ["uint", _]:
            return pack(basic_bytes(t, v)), 1, None
        case ["bvec", n]:
            return pack(bytes.fromhex(v)), (n + 31) // 32, None
        case ["blist", n]:
            data = bytes.fromhex(v)
            return pack(data), (n + 31) // 32, word(len(data))
        case ["bitvec", n]:
            return pack_bits(v), (n + 255) // 256, None
        case ["bitlist", n]:
            return pack_bits(v), (n + 255) // 256, word(len(v))
        case ["pbitlist"]:
            return pack_bits(v), None, word(len(v))
        case ["vec", elem, n]:
            return elements(elem, v), chunk_count(t), None
        case ["list", elem, n]:
            return elements(elem, v), chunk_count(t), word(len(v))
        case ["plist", elem]:
            return elements(elem, v), None, word(len(v))
        case ["cont", _, fields]:
            return [("value", f, x) for f, x in zip(fields, v, strict=False)], len(fields), None
        case ["pcont", active, _, fields]:
            values = iter(zip(fields, v, strict=False))
            leaves = [("value", *next(values)) if bit else ("chunk", ZERO) for bit in active]
            return leaves, None, pack_bits(active)[0][1]
        case ["union", selectors, options]:
            option = options[selectors.index(v["s"])]
            return [("value", option, v["d"])], 1, word(v["s"])
    raise ValueError(f"unknown type {t}")


def leaf_root(leaf):
    return leaf[1] if leaf[0] == "chunk" else tree_node(leaf[1], leaf[2], [])


def perfect_node(leaves, depth, start, bits):
    """A node of the perfect tree of a depth over the leaves from a position."""
    if not bits:
        if start >= len(leaves):
            return zero_root(depth)
        if depth == 0:
            return leaf_root(leaves[start])
        return sha(
            perfect_node(leaves, depth - 1, start, []),
            perfect_node(leaves, depth - 1, start + (1 << (depth - 1)), []),
        )
    if depth == 0:
        if start >= len(leaves) or leaves[start][0] == "chunk":
            raise LookupError("below a chunk")
        return tree_node(leaves[start][1], leaves[start][2], bits)
    half = 1 << (depth - 1)
    return perfect_node(leaves, depth - 1, start + half * bits[0], bits[1:])


def spine_node(leaves, level, bits):
    """A node of a progressive spine (EIP-7916): a tree of 4^level leaves, then the rest."""
    if not leaves:
        if bits:
            raise LookupError("past the spine")
        return ZERO
    width = 4**level
    if not bits:
        return sha(
            perfect_node(leaves[:width], 2 * level, 0, []),
            spine_node(leaves[width:], level + 1, []),
        )
    if bits[0]:
        return spine_node(leaves[width:], level + 1, bits[1:])
    return perfect_node(leaves[:width], 2 * level, 0, bits[1:])


def tree_node(t, v, bits):
    """The node that the turns reach from the root of a value, 1 for right."""
    leaves, limit, mixin = tree_layout(t, v)

    def contents(turns):
        if limit is None:
            return spine_node(leaves, 0, turns)
        if len(leaves) > limit:
            raise ValueError("over the limit")
        return perfect_node(leaves, (pow2ceil(limit) - 1).bit_length(), 0, turns)

    if mixin is None:
        return contents(bits)
    if not bits:
        return sha(contents([]), mixin)
    if bits[0]:
        if bits[1:]:
            raise LookupError("below a word")
        return mixin
    return contents(bits[1:])


def ssznode(t, v, gindex):
    if gindex < 1:
        return "error NOT_A_GINDEX"
    bits = [int(b) for b in bin(gindex)[3:]]
    try:
        mine = tree_node(t, v, bits).hex()
    except LookupError as e:
        mine = f"error model {e}"
    # The reference answers for the nodes it keeps, and there the two must agree.
    try:
        theirs = ssz_value(t, v).get_backing().getter(gindex).merkle_root().hex()
    except Exception:
        theirs = None
    if theirs is not None and theirs != mine:
        return f"references differ {mine} {theirs}"
    try:
        cited = bytes(spec.node_root(spec_value(t, v), gindex)).hex()
    except spec.SSZError as e:
        cited = f"error {e.fault.name} {e}"
    if cited.startswith("error") != mine.startswith("error") or (
        not cited.startswith("error") and cited != mine
    ):
        return f"references differ {cited} | {mine}"
    return cited


def sszbounds(t):
    typ = ssz_type(t)
    return f"{typ.min_byte_length()} {typ.max_byte_length()}"


def sszdef(t):
    value = ssz_type(t).default(None)
    first = f"{tohex(value.encode_bytes())} {value.hash_tree_root().hex()}"
    theirs = spec_type(t).default()
    if not theirs.is_zero():
        return "references differ: the default is not zero"
    second = f"{tohex(theirs.encode_bytes())} {bytes(theirs.hash_tree_root()).hex()}"
    return first if first == second else f"references differ {first} {second}"


def ssziszero(t, v):
    """is_zero of the specification, or the fault of a type that has no default."""
    try:
        return "true" if spec_value(t, v).is_zero() else "false"
    except spec.SSZError as e:
        return f"error {e.fault.name}"


def spechelpers(indices):
    try:
        return " ".join(map(str, spec.get_helper_indices(indices))) or "-"
    except spec.SSZError as e:
        return f"error {e.fault.name} {e}"


def specroot(leaves, proof, indices):
    """The root that the specification rebuilds from one index or from several."""
    try:
        if isinstance(indices, int):
            return bytes(spec.calculate_merkle_root(leaves[0], proof, indices)).hex()
        return bytes(spec.calculate_multi_merkle_root(leaves, proof, indices)).hex()
    except spec.SSZError as e:
        return f"error {e.fault.name} {e}"


def is_basic(t):
    return t[0] in ("bool", "uint")


def item_length(t):
    return {"bool": 1, "uint": t[-1]}.get(t[0], 32) if is_basic(t) else 32


def elem_of(t):
    match t:
        case ["bvec", _] | ["blist", _]:
            return ["uint", 1]
        case ["bitvec", _] | ["bitlist", _] | ["pbitlist"]:
            return ["bool"]
    return t[1]


def chunk_count(t):
    """chunk_count of ssz/simple-serialize.md."""
    match t:
        case ["bitvec", n] | ["bitlist", n]:
            return (n + 255) // 256
        case ["bvec", n] | ["blist", n]:
            return (n + 31) // 32
        case ["vec", elem, n] | ["list", elem, n]:
            return (n * item_length(elem) + 31) // 32
        case ["cont", _, fields]:
            return len(fields)
    raise ValueError("no chunk count")


def pow2ceil(x):
    return 1 if x <= 1 else 2 * pow2ceil((x + 1) // 2)


def concat(outer, inner):
    """concat_generalized_indices of ssz/merkle-proofs.md, for two."""
    floor = 1 << (inner.bit_length() - 1)
    return outer * floor + (inner - floor)


def progressive_gindex(chunk):
    """The node of a chunk under the contents of a progressive shape (EIP-7916)."""
    spine, depth = 1, 0
    while chunk >= 1 << depth:
        chunk -= 1 << depth
        depth += 2
        spine = spine * 2 + 1
    return ((spine * 2) << depth) + chunk


def spec_gindex(t, path):
    """get_generalized_index of ssz/merkle-proofs.md, with the progressive shapes."""
    root = 1
    for at, step in enumerate(path):
        if is_basic(t):
            raise ValueError("basic")
        if step in ("len", "active", "selector"):
            wants = {
                "len": ("list", "blist", "bitlist", "plist", "pbitlist"),
                "active": ("pcont",),
                "selector": ("union",),
            }[step]
            if t[0] not in wants:
                raise ValueError("no such word")
            return concat(root, 3) if at == len(path) - 1 else None
        kind = t[0]
        if kind == "union":
            t = t[2][t[1].index(step)]
            root = concat(root, 2)
        elif kind in ("cont", "pcont"):
            child = t[-1][step]
            if kind == "cont":
                root = concat(root, pow2ceil(len(t[2])) + step)
            else:
                position = [i for i, bit in enumerate(t[1]) if bit][step]
                root = concat(root, concat(2, progressive_gindex(position)))
            t = child
        else:
            elem = elem_of(t)
            if kind in ("bitvec", "bitlist", "pbitlist"):
                chunk = step // 256
            else:
                chunk = step * item_length(elem) // 32
            if kind in ("plist", "pbitlist"):
                root = concat(root, concat(2, progressive_gindex(chunk)))
            else:
                if step >= t[-1]:
                    raise ValueError("past the capacity")
                leaf = pow2ceil(chunk_count(t)) + chunk
                base = 2 if kind in ("list", "blist", "bitlist") else 1
                root = concat(root, concat(base, leaf) if base == 2 else leaf)
            t = elem
    return root


def sszgindex(t, path):
    try:
        index = spec_gindex(t, path)
    except (ValueError, IndexError):
        index = None
    mine = "error" if index is None else str(index)
    try:
        cited = str(spec.get_generalized_index(spec_type(t), *spec_path(t, path)))
    except spec.SSZError as e:
        cited = f"error {e.fault.name}"
    except LookupError:
        cited = "error NO_SUCH_FIELD"
    if cited.startswith("error") != mine.startswith("error") or (
        not cited.startswith("error") and cited != mine
    ):
        return f"references differ {cited} | {mine}"
    return cited


def sszposition(t, step):
    """chunk_position, chunk_count and item_length of the specification, or their faults."""
    typ = spec_type(t)

    def ask(question):
        try:
            return question()
        except spec.SSZError as e:
            return f"error {e.fault.name}"

    word = spec_path(t, [step])[0]
    position = ask(lambda: "{} {} {}".format(*spec_paths.chunk_position(typ, word)))
    count = ask(lambda: str(spec_paths.chunk_count(typ)))
    return f"{position} | {count} | {spec_paths.item_length(typ)}"


def sszcompat(a, b):
    try:
        CompatibleUnion({1: ssz_type(a), 2: ssz_type(b)})
        first = "ok"
    except TypeError:
        first = "error"
    cited = "ok" if spec.is_compatible(spec_fresh(a), spec_fresh(b)) else "error"
    return cited if cited == first else f"references differ {cited} | {first}"


# Merkle proofs: ssz/merkle-proofs.md of consensus-specs, as written there.


def get_branch_indices(tree_index):
    o = [tree_index ^ 1]
    while o[-1] > 1:
        o.append((o[-1] // 2) ^ 1)
    return o[:-1]


def get_path_indices(tree_index):
    o = [tree_index]
    while o[-1] > 1:
        o.append(o[-1] // 2)
    return o[:-1]


def get_helper_indices(indices):
    all_helper_indices = set()
    all_path_indices = set()
    for index in indices:
        all_helper_indices = all_helper_indices.union(set(get_branch_indices(index)))
        all_path_indices = all_path_indices.union(set(get_path_indices(index)))
    return sorted(all_helper_indices.difference(all_path_indices), reverse=True)


# The hash of the tree model: SHA-256, unless a command names another.
HASH = [params.HASHES["sha256"]]


def sha(a, b):
    return HASH[0](a + b)


def modelnode(name, t, v, gindex):
    """A node of the tree model with another hash in the place of SHA-256."""
    HASH[0] = params.HASHES[name]
    try:
        return tree_node(t, v, [int(b) for b in bin(gindex)[3:]]).hex()
    except LookupError as e:
        return f"error model {e}"
    finally:
        HASH[0] = params.HASHES["sha256"]


def calculate_multi_merkle_root(leaves, proof, indices):
    assert len(leaves) == len(indices)
    helper_indices = get_helper_indices(indices)
    assert len(proof) == len(helper_indices)
    objects = {
        **dict(zip(indices, leaves, strict=False)),
        **dict(zip(helper_indices, proof, strict=False)),
    }
    keys = sorted(objects.keys(), reverse=True)
    pos = 0
    while pos < len(keys):
        k = keys[pos]
        if k in objects and k ^ 1 in objects and k // 2 not in objects:
            objects[k // 2] = sha(objects[(k | 1) ^ 1], objects[k | 1])
            keys.append(k // 2)
        pos += 1
    return objects[1]


def is_valid_merkle_branch(leaf, branch, depth, index, root):
    """is_valid_merkle_branch of phase0/beacon-chain.md."""
    value = leaf
    for i in range(depth):
        if index // (2**i) % 2:
            value = sha(branch[i], value)
        else:
            value = sha(value, branch[i])
    return value == root


def chunks_of(word):
    data = unhex(word)
    return [data[i : i + 32] for i in range(0, len(data), 32)]


# DER.


def dss(data):
    try:
        r, s = decode_dss_signature(data)
        return f"{r} {s}"
    except ValueError:
        return "error"


def dertlv(data):
    """One tag, length and value by X.690 8.1.2, 8.1.3 and 10.1, low tag numbers only."""
    if len(data) < 2:
        return "error"
    tag, first = data[0], data[1]
    if tag & 0x1F == 0x1F or tag == 0:
        return "error"
    if first < 0x80:
        length, header = first, 2
    else:
        count = first & 0x7F
        # 0x80 is the indefinite form, and 0xff is reserved.
        if count == 0 or count == 127 or len(data) < 2 + count:
            return "error"
        length, header = int.from_bytes(data[2 : 2 + count], "big"), 2 + count
        # The shortest form: no leading zero octet, and the short form below 128.
        if data[2] == 0 or length < 128:
            return "error"
    if len(data) < header + length:
        return "error"
    content, rest = data[header : header + length], data[header + length :]
    return f"{tag} {tohex(content)} {tohex(rest)}"


PRINTABLE = set(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789 '()+,-./:=?")


def scalar(n):
    return n <= 0x10FFFF and not 0xD800 <= n <= 0xDFFF


def der_children(data):
    out = []
    while data:
        words = dertlv(data).split(" ")
        if words[0] == "error":
            raise ValueError("child")
        rest = unhex(words[2])
        out.append((int(words[0]), unhex(words[1]), data[: len(data) - len(rest)]))
        data = rest
    return out


def der_valid(tag, content):
    """Whether the content is DER for the tag, by X.690 8.2 to 8.23, 10 and 11."""
    match tag:
        case 1:
            return content in (b"\x00", b"\xff")
        case 2:
            if not content:
                return False
            if len(content) > 1:
                top = content[0] << 1 | content[1] >> 7
                return top not in (0, 0x1FF)
            return True
        case 3:
            if not content or content[0] > 7:
                return False
            if len(content) == 1:
                return content[0] == 0
            return content[-1] & ((1 << content[0]) - 1) == 0
        case 4:
            return True
        case 5:
            return content == b""
        case 6:
            if not content or content[-1] & 0x80:
                return False
            start = True
            for byte in content:
                if start and byte == 0x80:
                    return False
                start = byte < 0x80
            return True
        case 12:
            try:
                content.decode("utf-8")
                return True
            except UnicodeDecodeError:
                return False
        case 19:
            return all(byte in PRINTABLE for byte in content)
        case 22:
            return all(byte < 0x80 for byte in content)
        case 28 | 30:
            width = 4 if tag == 28 else 2
            if len(content) % width:
                return False
            units = range(0, len(content), width)
            return all(scalar(int.from_bytes(content[i : i + width], "big")) for i in units)
        case 48 | 49:
            try:
                children = der_children(content)
            except ValueError:
                return False
            if tag == 49:
                # X.690 11.6: ascending, the shorter padded with zero octets.
                width = max((len(c[2]) for c in children), default=0)
                keys = [c[2].ljust(width, b"\0") for c in children]
                if keys != sorted(keys):
                    return False
            return all(der_valid(t, c) for t, c, _ in children)
    return False


def dervalid(data):
    words = dertlv(data).split(" ")
    if words[0] == "error" or words[2] != "-":
        return "error"
    return "ok" if der_valid(int(words[0]), unhex(words[1])) else "error"


def derint(data):
    """The integer of a DER INTEGER (X.690 8.3), or error."""
    words = dertlv(data).split(" ")
    if words[0] != "2" or words[2] != "-" or not der_valid(2, unhex(words[1])):
        return "error"
    return str(int.from_bytes(unhex(words[1]), "big", signed=True))


def jsonint(text):
    """The integer that a JSON number is, or error: by Python's exact decimals."""
    from decimal import Decimal, InvalidOperation

    try:
        if not re.fullmatch(r"-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?", text):
            return "error not a number"
        value = Decimal(text)
    except InvalidOperation:
        return "error not a number"
    return str(int(value)) if value == value.to_integral_value() else "error"


# JSON-RPC: the patterns of execution-apis, src/schemas/base-types.yaml.

PATTERNS = {
    "bytes": r"^0x[0-9a-f]*$",
    "address": r"^0x[0-9a-fA-F]{40}$",
    "hash32": r"^0x[0-9a-f]{64}$",
    "bytes8": r"^0x[0-9a-f]{16}$",
    "uint": r"^0x(0|[1-9a-f][0-9a-f]*)$",
    "uint64": r"^0x(0|[1-9a-f][0-9a-f]{0,15})$",
    "uint256": r"^0x(0|[1-9a-f][0-9a-f]{0,63})$",
}


def rpc(kind, text):
    try:
        chars = text.decode("utf-8")
    except UnicodeDecodeError:
        return "error"
    # `$` of Python also matches before a final newline, which the schema does not mean.
    if not re.fullmatch(PATTERNS[kind].strip("^$"), chars):
        return "error"
    if kind.startswith("uint"):
        return str(int(chars, 16))
    # The pattern of `bytes` admits an odd count of digits, which spells no bytes.
    # Two digits make a byte, as the "hex encoded bytes" of the schema say.
    if len(chars) % 2:
        return "error"
    return tohex(bytes.fromhex(chars[2:]))


# E2store.


def e2s(data):
    """The records of a file: type[2] | length[4] little-endian | reserved[2] | data."""
    out, pos = [], 0
    while pos < len(data):
        if len(data) < pos + 8:
            return "error"
        kind = data[pos : pos + 2]
        (length,) = struct.unpack("<I", data[pos + 2 : pos + 6])
        if data[pos + 6 : pos + 8] != b"\0\0" or len(data) < pos + 8 + length:
            return "error"
        out.append(f"{kind.hex()}:{tohex(data[pos + 8 : pos + 8 + length])}")
        pos += 8 + length
    return " ".join(out) or "-"


def answer(words):
    match words:
        case ["rlpenc", item]:
            return tohex(rlp.encode(rlp_item(json.loads(item))))
        case ["rlpdec", data]:
            return rlpdec(unhex(data))
        case ["rlpint", data]:
            return rlpint(unhex(data))
        case ["sszenc", t, v]:
            return sszenc(json.loads(t), json.loads(v))
        case ["sszdec", t, data]:
            return sszdec(json.loads(t), unhex(data))
        case ["ssztype", t]:
            return ssztype(json.loads(t))
        case ["sszjson", t, v, document]:
            return sszjson(json.loads(t), json.loads(v), document)
        case ["sszjsonread", t, document]:
            return sszjsonread(json.loads(t), document)
        case ["spechelpers", indices]:
            return spechelpers(json.loads(indices))
        case ["specroot", leaves, proof, indices]:
            return specroot(chunks_of(leaves), chunks_of(proof), json.loads(indices))
        case ["sszbounds", t]:
            return sszbounds(json.loads(t))
        case ["sszdef", t]:
            return sszdef(json.loads(t))
        case ["ssziszero", t, v]:
            return ssziszero(json.loads(t), json.loads(v))
        case ["branchroot", leaf, branch, depth, index]:
            value = unhex(leaf)
            for i, node in enumerate(chunks_of(branch)[: int(depth)]):
                value = sha(node, value) if int(index) >> i & 1 else sha(value, node)
            return value.hex()
        case ["ssznode", t, v, gindex]:
            return ssznode(json.loads(t), json.loads(v), int(gindex))
        case ["sszgindex", t, path]:
            return sszgindex(json.loads(t), json.loads(path))
        case ["sszposition", t, step]:
            return sszposition(json.loads(t), json.loads(step))
        case ["sszcompat", a, b]:
            return sszcompat(json.loads(a), json.loads(b))
        case ["helpers", indices]:
            return " ".join(map(str, get_helper_indices(json.loads(indices)))) or "-"
        case ["multiroot", leaves, proof, indices]:
            root = calculate_multi_merkle_root(
                chunks_of(leaves), chunks_of(proof), json.loads(indices)
            )
            return root.hex()
        case ["branch", leaf, branch, depth, index, root]:
            ok = is_valid_merkle_branch(
                unhex(leaf), chunks_of(branch), int(depth), int(index), unhex(root)
            )
            return "true" if ok else "false"
        case ["dss", data]:
            return dss(unhex(data))
        case ["dervalid", data]:
            return dervalid(unhex(data))
        case ["derint", data]:
            return derint(unhex(data))
        case ["jsonint", text]:
            return jsonint(unhex(text).decode())
        case ["dertlv", data]:
            return dertlv(unhex(data))
        case ["rpc", kind, text]:
            return rpc(kind, unhex(text))
        case ["e2s", data]:
            return e2s(unhex(data))
        case ["modelnode", name, t, v, gindex]:
            return modelnode(name, json.loads(t), json.loads(v), int(gindex))
    if words[0] in params.HANDLERS:
        return params.HANDLERS[words[0]](*words[1:])
    return "error unknown command"


for line in sys.stdin:
    try:
        reply = answer(line.rstrip("\n").split("\t"))
    except Exception as e:  # The driver reads one line for each command.
        reply = f"error oracle {type(e).__name__} {e}".replace("\n", " ")
    print(reply or "-", flush=True)

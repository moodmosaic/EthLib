"""A model of engine_newPayload before execution, and the hash of a payload's header."""

# The model is written from execution-apis at commit 3284ee8: paris.md, shanghai.md,
# cancun.md, prague.md, osaka.md and amsterdam.md.  The header is that of EIP-3675 and
# EIP-4399, with the fields that EIP-4895, EIP-4844, EIP-4788, EIP-7685, EIP-7928 and
# EIP-7843 append.  Its hash is computed with `rlp` and Keccak-256, and again with the
# header classes of execution-specs for the forks that it has.
#
# A case names a payload and what is done to it; the answer is the outcomes that the
# specification allows, and the JSON text of the parameters.

import hashlib
import json
import re

from Crypto.Hash import keccak
from eth_account import Account
from ethereum.forks.cancun import blocks as cancun_blocks
from ethereum.forks.paris import blocks as paris_blocks
from ethereum.forks.prague import blocks as prague_blocks
from ethereum.forks.prague.requests import compute_requests_hash
from ethereum.forks.shanghai import blocks as shanghai_blocks
from ethereum_rlp import rlp as eels_rlp
from ethereum_types.bytes import Bytes8, Bytes20, Bytes32, Bytes256
from ethereum_types.numeric import U64, U256, Uint

import rlp
from trie import HexaryTrie

# The forks of the test chain, in order, with the time from which each is active.
# Before block 10 the chain is before Paris.
PARIS_BLOCK = 10
FORKS = [
    ("paris", 0),
    ("shapella", 1000),
    ("dencun", 2000),
    ("pectra", 3000),
    ("fusaka", 4000),
    ("bpo1", 5000),
    ("bpo2", 6000),
    ("glamsterdam", 7000),
    ("hegota", 8000),
]
ORDER = ["london"] + [name for name, _ in FORKS]


def active_fork(number, timestamp):
    # The latest fork that the block has reached, by its number or by its time.
    if number < PARIS_BLOCK and timestamp < FORKS[1][1]:
        return "london"
    return [name for name, start in FORKS if start <= timestamp][-1]


def since(fork, first):
    return ORDER.index(fork) >= ORDER.index(first)


# The forks whose payloads each version of the method takes.
# V1: paris.md.  V2: shanghai.md, and before Cancun by cancun.md.  V3: the time frame of
# Cancun, cancun.md.  V4: the time frame of Prague, prague.md, read with the update of
# amsterdam.md, which refuses Amsterdam and so leaves Osaka and its blob forks.
# V5: the time frame of Amsterdam.
TAKES = {
    1: {"paris"},
    2: {"paris", "shapella"},
    3: {"dencun"},
    4: {"pectra", "fusaka", "bpo1", "bpo2"},
    5: {"glamsterdam"},
}
PARAM_COUNT = {1: 1, 2: 1, 3: 3, 4: 4, 5: 4}

V1 = [
    ("parentHash", "bytes32"),
    ("feeRecipient", "address"),
    ("stateRoot", "bytes32"),
    ("receiptsRoot", "bytes32"),
    ("logsBloom", "bytes256"),
    ("prevRandao", "bytes32"),
    ("blockNumber", "uint64"),
    ("gasLimit", "uint64"),
    ("gasUsed", "uint64"),
    ("timestamp", "uint64"),
    ("extraData", "bytesMax32"),
    ("baseFeePerGas", "uint256"),
    ("blockHash", "bytes32"),
    ("transactions", "txs"),
]
V2 = V1 + [("withdrawals", "withdrawals")]
V3 = V2 + [("blobGasUsed", "uint64"), ("excessBlobGas", "uint64")]
V4 = V3 + [("blockAccessList", "bytes"), ("slotNumber", "uint64")]
STRUCTURES = {1: V1, 2: V2, 3: V3, 4: V4}
# The versions of the structure that each version of the method takes.
STRUCTURE_OF = {1: [1], 2: [1, 2], 3: [3], 4: [3], 5: [4]}
WITHDRAWAL = [
    ("index", "uint64"),
    ("validatorIndex", "uint64"),
    ("address", "address"),
    ("amount", "uint64"),
]

PATTERN = {
    "address": r"0x[0-9a-fA-F]{40}",
    "bytes": r"0x([0-9a-f]{2})*",
    "bytesMax32": r"0x([0-9a-f]{2}){0,32}",
    "bytes8": r"0x[0-9a-f]{16}",
    "bytes16": r"0x[0-9a-f]{32}",
    "bytes32": r"0x[0-9a-f]{64}",
    "bytes256": r"0x[0-9a-f]{512}",
    "uint64": r"0x(0|[1-9a-f][0-9a-f]{0,15})",
    "uint256": r"0x(0|[1-9a-f][0-9a-f]{0,63})",
}


A1 = [("timestamp", "uint64"), ("prevRandao", "bytes32"), ("suggestedFeeRecipient", "address")]
A2 = A1 + [("withdrawals", "withdrawals")]
A3 = A2 + [("parentBeaconBlockRoot", "bytes32")]
A4 = A3 + [("slotNumber", "uint64"), ("targetGasLimit", "uint64")]
STATE = [
    ("headBlockHash", "bytes32"),
    ("safeBlockHash", "bytes32"),
    ("finalizedBlockHash", "bytes32"),
]
# The structures of a name, by version: the one that a value matches is its shape.
SHAPES = {
    "attributes": {1: A1, 2: A2, 3: A3, 4: A4},
    "state": {1: STATE},
    "payload": STRUCTURES,
}


def shape(name, text):
    """The version of the structure that a JSON value has, or 0 for none."""
    try:
        value = json.loads(text)
    except ValueError:
        return "0"
    for version, fields in SHAPES[name].items():
        if is_object(fields, value):
            return str(version)
    return "0"


STATUSES = ["VALID", "INVALID", "SYNCING", "ACCEPTED", "INVALID_BLOCK_HASH"]


def reads(name, text):
    """Whether a JSON value is a structure of a response, by paris.md and identification.md.

    A field whose value is null is not provided, and a status needs its `status` only.
    """
    try:
        value = json.loads(text)
    except ValueError:
        return "error"
    if not isinstance(value, dict):
        return "error"
    held = present(value)
    match name:
        case "status":
            ok = (
                held.get("status") in STATUSES
                and set(held) <= {"status", "latestValidHash", "validationError"}
                and ("latestValidHash" not in held or is_type("bytes32", held["latestValidHash"]))
                and isinstance(held.get("validationError", ""), str)
            )
        case "transition":
            ok = is_object(
                [
                    ("terminalTotalDifficulty", "uint256"),
                    ("terminalBlockHash", "bytes32"),
                    ("terminalBlockNumber", "uint64"),
                ],
                value,
            )
        case "client":
            ok = (
                set(held) == {"code", "name", "version", "commit"}
                and isinstance(held["code"], str)
                and re.fullmatch(r"[A-Za-z]{2}", held["code"]) is not None
                and isinstance(held["name"], str)
                and isinstance(held["version"], str)
                and isinstance(held["commit"], str)
                and re.fullmatch(r"0x[0-9a-f]{8}", held["commit"]) is not None
            )
    return "ok" if ok else "error"


def keccak256(data):
    return keccak.new(digest_bits=256, data=data).digest()


def is_type(kind, value):
    """Whether a JSON value is of a type of the schema."""
    if kind == "txs":
        return isinstance(value, list) and all(is_type("bytes", v) for v in value)
    if kind == "withdrawals":
        return isinstance(value, list) and all(is_object(WITHDRAWAL, v) for v in value)
    return isinstance(value, str) and re.fullmatch(PATTERN[kind], value) is not None


def present(obj):
    """The fields of an object that count: a field whose value is null is not provided."""
    return {k: v for k, v in obj.items() if v is not None}


def is_object(fields, value):
    """Whether a JSON value is an object with exactly the fields, each of its type."""
    if not isinstance(value, dict):
        return False
    held = present(value)
    return set(held) == {name for name, _ in fields} and all(
        is_type(kind, held[name]) for name, kind in fields
    )


# Transactions signed once, each with the first fork that takes its type.
ACCOUNT = Account.from_key(b"\x01" * 32)
BASE = {"nonce": 0, "gas": 21000, "to": "0x" + "11" * 20, "value": 1, "data": b"", "chainId": 1}
FEES = {"maxFeePerGas": 10, "maxPriorityFeePerGas": 1}
BLOB_HASHES = [b"\x01" + hashlib.sha256(bytes([i]) * 48).digest()[1:] for i in range(3)]


def sign(fields):
    return bytes(ACCOUNT.sign_transaction({**BASE, **fields}).raw_transaction)


def blob(hashes):
    return sign({"type": 3, **FEES, "maxFeePerBlobGas": 1, "blobVersionedHashes": hashes})


AUTHORIZATION = ACCOUNT.sign_authorization({"chainId": 1, "address": "0x" + "22" * 20, "nonce": 1})
# Name: the bytes, the first fork that takes them (none takes them if None), blob hashes.
TXS = {
    "legacy": (sign({"gasPrice": 10}), "london", []),
    "accessList": (sign({"type": 1, "gasPrice": 10, "accessList": []}), "london", []),
    "dynamicFee": (sign({"type": 2, **FEES}), "london", []),
    "blob1": (blob(BLOB_HASHES[:1]), "dencun", BLOB_HASHES[:1]),
    "blob2": (blob(BLOB_HASHES[1:]), "dencun", BLOB_HASHES[1:]),
    "setCode": (sign({"type": 4, **FEES, "authorizationList": [AUTHORIZATION]}), "pectra", []),
    "empty": (b"", None, []),
    "unknownType": (b"\x05\xc0", None, []),
    "truncated": (sign({"gasPrice": 10})[:-1], None, []),
}


def trie_root(items):
    trie = HexaryTrie(db={})
    for i, item in enumerate(items):
        trie[rlp.encode(i)] = item
    return trie.root_hash


def unhex(text):
    return bytes.fromhex(text[2:])


def header_fields(case, fork):
    """The fields of the header of a payload at a fork, in order."""
    c = case["common"]
    txs = [TXS[name][0] for name in case["txs"]]
    fields = [
        unhex(c["parentHash"]),
        keccak256(rlp.encode([])),
        unhex(c["feeRecipient"]),
        unhex(c["stateRoot"]),
        trie_root(txs),
        unhex(c["receiptsRoot"]),
        unhex(c["logsBloom"]),
        0,
        int(c["blockNumber"]),
        int(c["gasLimit"]),
        int(c["gasUsed"]),
        int(c["timestamp"]),
        unhex(c["extraData"]),
        unhex(c["prevRandao"]),
        bytes(8),
        int(c["baseFeePerGas"]),
    ]
    if since(fork, "shapella"):
        fields.append(
            trie_root(
                rlp.encode([int(i), int(v), unhex(a), int(g)]) for i, v, a, g in case["withdrawals"]
            )
        )
    if since(fork, "dencun"):
        fields += [int(case["blobGasUsed"]), int(case["excessBlobGas"]), unhex(case["root"])]
    if since(fork, "pectra"):
        requests = [unhex(r) for r in case["requests"]]
        digest = hashlib.sha256(b"".join(hashlib.sha256(r).digest() for r in requests)).digest()
        if all(len(r) > 1 for r in requests):
            assert digest == compute_requests_hash(requests)
        fields.append(digest)
    if since(fork, "glamsterdam"):
        fields += [keccak256(unhex(case["bal"])), int(case["slot"])]
    return fields


def eels_hash(fields, fork):
    """The hash of the header by execution-specs, for the forks that it has."""
    if len(fields) > 21 or len(fields[12]) > 32:
        return None
    kinds = [Bytes32, Bytes32, Bytes20, Bytes32, Bytes32, Bytes32, Bytes256, Uint, Uint, Uint, Uint]
    kinds += [U256, bytes, Bytes32, Bytes8, Uint, Bytes32, U64, U64, Bytes32, Bytes32]
    header = {16: paris_blocks, 17: shanghai_blocks, 20: cancun_blocks, 21: prague_blocks}[
        len(fields)
    ].Header(*(kind(value) for kind, value in zip(kinds, fields, strict=False)))
    return keccak256(eels_rlp.encode(header))


def block_hash(case, fork):
    fields = header_fields(case, fork)
    digest = keccak256(rlp.encode(fields))
    other = eels_hash(fields, fork)
    assert other is None or other == digest, "execution-specs gives another header hash"
    return digest


def quantity(n):
    return hex(int(n))


def respell(text, how):
    """Another spelling of a value: one that names the same value, or none at all."""
    match how:
        case "upper":
            return "0x" + text[2:].upper()
        case "leadingZero":
            return "0x0" + text[2:]
        case "number":
            return 1


def build_params(case, fork):
    """The parameters as JSON, after the damage that the case names."""
    c = case["common"]
    payload = {
        name: (quantity(c[name]) if kind.startswith("uint") else c[name])
        for name, kind in V1
        if name not in ("blockHash", "transactions")
    }
    digest = block_hash(case, fork)
    if case["hashDamage"]:
        digest = bytes([digest[0] ^ 1]) + digest[1:]
    payload["blockHash"] = "0x" + digest.hex()
    payload["transactions"] = ["0x" + TXS[name][0].hex() for name in case["txs"]]
    if case["sv"] >= 2:
        payload["withdrawals"] = [
            {
                "index": quantity(i),
                "validatorIndex": quantity(v),
                "address": a,
                "amount": quantity(g),
            }
            for i, v, a, g in case["withdrawals"]
        ]
    if case["sv"] >= 3:
        payload["blobGasUsed"] = quantity(case["blobGasUsed"])
        payload["excessBlobGas"] = quantity(case["excessBlobGas"])
    if case["sv"] >= 4:
        payload["blockAccessList"] = case["bal"]
        payload["slotNumber"] = quantity(case["slot"])
    for name in case["drop"]:
        payload.pop(name, None)
    for name in case["nulls"]:
        payload[name] = None
    for name in case["extra"]:
        payload.setdefault(name, "0x1")
    for name, how in case["replace"]:
        if isinstance(payload.get(name), str):
            payload[name] = respell(payload[name], how)
    actual = [h for name in case["txs"] for h in TXS[name][2]]
    hashes = {
        "match": actual,
        "drop": actual[:-1],
        "extra": actual + [BLOB_HASHES[0]],
        "reverse": actual[::-1],
        "flip": [bytes([h[0] ^ 3]) + h[1:] for h in actual],
    }[case["hashes"]]
    params = [payload, ["0x" + h.hex() for h in hashes], case["root"], case["requests"]]
    params = params[: PARAM_COUNT[case["version"]]]
    match case["params"]:
        case "short":
            params = params[:-1]
        case "long":
            params.append("0x")
        case "nullLast":
            params[-1] = None
        case "object":
            return {"executionPayload": payload}, hashes, actual
    return params, hashes, actual


def valid_requests(requests):
    """prague.md: ascending by type, each longer than one byte, no type twice."""
    data = [unhex(r) for r in requests]
    return all(len(r) > 1 for r in data) and all(
        a[0] < b[0] for a, b in zip(data, data[1:], strict=False)
    )


def valid_access_list(data):
    """Whether bytes are the RLP form of a list with nothing after it; the cases use no more."""
    try:
        return isinstance(rlp.decode(data, strict=True), list)
    except rlp.exceptions.RLPException:
        return False


def outcomes(case, params, hashes, actual):
    """The answers that the specification allows for a call."""
    version = case["version"]
    fork = active_fork(int(case["common"]["blockNumber"]), int(case["common"]["timestamp"]))
    supported = fork in TAKES[version]
    # The source does not order its two errors, so a call with both faults may give either.
    wrong = {"E32602"} if supported else {"E32602", "E38005"}
    payload = params[0] if isinstance(params, list) and params else None
    timed = isinstance(payload, dict) and all(
        is_type("uint64", payload.get(name)) for name in ("blockNumber", "timestamp")
    )
    if not timed:
        # A payload without its number and its time names no fork.
        wrong = {"E32602"}
    if not isinstance(params, list) or len(params) != PARAM_COUNT[version]:
        return wrong
    if any(p is None for p in params):
        return wrong
    layouts = [v for v in STRUCTURE_OF[version] if is_object(STRUCTURES[v], payload)]
    if not layouts:
        return wrong
    if version >= 3:
        if not (isinstance(params[1], list) and all(is_type("bytes32", h) for h in params[1])):
            return wrong
        if not is_type("bytes32", params[2]):
            return wrong
    if version >= 4:
        if not (isinstance(params[3], list) and all(is_type("bytes", r) for r in params[3])):
            return wrong
        if not valid_requests(params[3]):
            return wrong
    if not supported:
        return {"E38005"}
    if version == 2 and layouts != [2 if fork == "shapella" else 1]:
        return {"E32602"}
    found = set()
    for name in case["txs"]:
        first = TXS[name][1]
        if first is None or not since(fork, first):
            found.add("INVALID")
    if case["hashDamage"]:
        found.add("INVALID_BLOCK_HASH" if version == 1 else "INVALID")
    if version >= 5 and not valid_access_list(unhex(case["bal"])):
        found.add("INVALID")
    if version >= 3 and hashes != actual:
        found.add("INVALID")
    return found or {"SYNCING"}


def new_payload(text):
    case = json.loads(text)
    fork = active_fork(int(case["common"]["blockNumber"]), int(case["common"]["timestamp"]))
    params, hashes, actual = build_params(case, fork)
    allowed = outcomes(case, params, hashes, actual)
    return "|".join(sorted(allowed)) + " " + json.dumps(params).encode().hex()

"""A model of the state getters and of eth_getProof, with py-trie and the `rlp` package."""

#     state <accounts> <method> <params>
#         The result of a state method as JSON text, or `error <codes>`, `error *` for any.
#
# An account is `address,nonce,balance,code,key=value&key=value`, and they are joined with `;`.
# The state is the one after the head, the only block of the node.
#
# The values are those of `src/eth/state.yaml` of execution-apis and of EIP-1186.
# An address with no account reads as the empty account, as the fixtures of the source fix.
# The tries are those of the Yellow Paper, built by py-trie.
# The state trie holds each account under the hash of its address.
# A storage trie holds each word under the hash of its key.
# A proof of the empty trie has no node in py-trie and in go-ethereum.
# It has the one node `0x80` in EthLib, and the model writes `0x80`.
# `findings/execution.md` holds that open point.

import json
import re

from Crypto.Hash import keccak

import rlp
from trie import HexaryTrie


def keccak256(data):
    return keccak.new(digest_bits=256, data=bytes(data)).digest()


def scalar(number):
    return number.to_bytes((number.bit_length() + 7) // 8, "big")


ADDRESS = re.compile(r"^0x[0-9a-fA-F]{40}$")
KEY = re.compile(r"^0x[0-9a-f]{0,64}$")
UINT = re.compile(r"^0x(0|[1-9a-f][0-9a-f]*)$")
EMPTY_ROOT = keccak256(rlp.encode(b""))


class RefusedError(Exception):
    """A request that a method refuses, with the codes that the source allows."""


class State:
    """The accounts of a state, and its tries."""

    def __init__(self, text):
        self.accounts = {}
        self.trie = HexaryTrie(db={})
        for entry in [] if text == "-" else text.split(";"):
            address, nonce, balance, code, storage = entry.split(",")
            code = b"" if code == "-" else bytes.fromhex(code)
            slots = {}
            trie = HexaryTrie(db={})
            for slot in [] if storage == "-" else storage.split("&"):
                key, value = slot.split("=")
                if int(value, 16):
                    slots[int(key, 16)] = int(value, 16)
                    trie[keccak256(bytes.fromhex(key))] = rlp.encode(scalar(int(value, 16)))
            address = bytes.fromhex(address)
            self.accounts[address] = (int(nonce), int(balance), code, slots, trie)
            self.trie[keccak256(address)] = rlp.encode(
                [scalar(int(nonce)), scalar(int(balance)), trie.root_hash, keccak256(code)]
            )

    def account(self, address):
        return self.accounts.get(address, (0, 0, b"", {}, HexaryTrie(db={})))


def proof_of(trie, key):
    """The nodes on the path of a key, each as its encoding."""
    nodes = [rlp.encode(node) for node in trie.get_proof(key)]
    return ["0x" + node.hex() for node in nodes] or ["0x80"]


def address_of(value):
    if not isinstance(value, str) or not ADDRESS.match(value):
        raise RefusedError("-32602")
    return bytes.fromhex(value[2:])


def key_of(value):
    """A storage key: at most 64 hex digits, read as a number (the type `bytesMax32`)."""
    if not isinstance(value, str) or not KEY.match(value):
        raise RefusedError("-32602")
    return int(value[2:] or "0", 16)


def block_of(rest):
    """The optional block of a request: the head by a tag or its number 5, else none."""
    if len(rest) > 1:
        raise RefusedError("-32602")
    if not rest or rest[0] in ("latest", "earliest", "0x5"):
        return True
    if rest[0] in ("pending", "safe", "finalized"):
        return False
    if isinstance(rest[0], str) and UINT.match(rest[0]):
        return False
    raise RefusedError("-32602")


def word(value):
    return "0x" + value.to_bytes(32, "big").hex()


def call(state, method, params):
    if not isinstance(params, list) or not params:
        raise RefusedError("-32602")
    if method == "eth_getStorageValues":
        requests, rest = params[0], params[1:]
        if not isinstance(requests, dict) or not requests:
            raise RefusedError("-32602")
        out = {}
        for name, keys in requests.items():
            address = address_of(name)
            if not isinstance(keys, list) or "0x" + address.hex() in out:
                raise RefusedError("-32602")
            slots = state.account(address)[3]
            out["0x" + address.hex()] = [word(slots.get(key_of(k), 0)) for k in keys]
        if not block_of(rest):
            raise RefusedError("*")
        return out
    address = address_of(params[0])
    nonce, balance, code, slots, trie = state.account(address)
    if method in ("eth_getStorageAt", "eth_getProof"):
        if len(params) < 2:
            raise RefusedError("-32602")
        keys, rest = params[1], params[2:]
    else:
        keys, rest = None, params[1:]
    if method == "eth_getStorageAt":
        keys = key_of(keys)
    if method == "eth_getProof":
        if not isinstance(keys, list):
            raise RefusedError("-32602")
        keys = [key_of(k) for k in keys]
    if not block_of(rest):
        # No text gives the code of an unknown block.
        raise RefusedError("*")
    if method == "eth_getBalance":
        return hex(balance)
    if method == "eth_getTransactionCount":
        return hex(nonce)
    if method == "eth_getCode":
        return "0x" + code.hex()
    if method == "eth_getStorageAt":
        return word(slots.get(keys, 0))
    if method == "eth_getProof":
        return {
            "address": "0x" + address.hex(),
            "accountProof": proof_of(state.trie, keccak256(address)),
            "balance": hex(balance),
            "codeHash": "0x" + keccak256(code).hex(),
            "nonce": hex(nonce),
            "storageHash": "0x" + trie.root_hash.hex(),
            "storageProof": [
                {
                    "key": hex(key),
                    "value": hex(slots.get(key, 0)),
                    "proof": proof_of(trie, keccak256(key.to_bytes(32, "big"))),
                }
                for key in keys
            ],
        }
    raise RefusedError("-32601")


def state(accounts, method, params):
    try:
        result = call(State(accounts), method, json.loads(params))
    except RefusedError as refused:
        return f"error {refused}"
    return json.dumps(result, separators=(",", ":"))


COMMANDS = {"state": state}

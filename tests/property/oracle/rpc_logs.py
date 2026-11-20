"""A model of the getters of a node: logs, receipts, blocks, transactions and raw forms."""

#     chain <activations> <blocks> <side> <marks>
#         The signed transactions of each block, and the hash of each block.
#     rpc <activations> <blocks> <side> <marks> <method> <params>
#         The result of a method as JSON text, or `error <codes>`, `error *` for any code.
#
# A block is `fork|header|txs`, and blocks are joined with `;`.
# A header is the eleven fields of `HeaderSpec.show`, joined with `,`.
# A transaction is `spec~gas used~status~logs`, and they are joined with `+`.
# The spec is that of `rpc_txs.py`.
# A log is `address!topics!data`, its topics joined with `.`, and logs are joined with `^`.
# The marks are `safe&finalized&pending`: two block numbers and a block, `-` for none.
#
# The JSON forms are written from the schemas of execution-apis and the texts of its methods.
# The schemas are `block.yaml`, `receipt.yaml`, `transaction.yaml` and `filter.yaml`.
# The encodings are those of the Yellow Paper and of the EIPs of each type and field.
# They are EIP-2718, 2930, 1559, 4844, 4895, 4788, 7685 and 7702, written with `rlp`.
# The Bloom filter is the one of the `eth-bloom` package.

import json
import re

import rpc_txs
from Crypto.Hash import keccak
from eth_bloom import BloomFilter
from rpc_fees import SCHEDULES, fake_exponential, since

import rlp


def keccak256(data):
    return keccak.new(digest_bits=256, data=bytes(data)).digest()


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def scalar(number):
    """A number as RLP holds it: big-endian, with no leading zero."""
    return number.to_bytes((number.bit_length() + 7) // 8, "big")


def quantity(number):
    return hex(number)


def data(value):
    return "0x" + bytes(value).hex()


EMPTY_OMMERS = keccak256(rlp.encode([]))
ZERO = b"\x00" * 32


class Tx:
    """A transaction of a block, with the receipt that the view gives it."""

    def __init__(self, text):
        spec, gas_used, status, logs = text.split("~")
        self.raw = rpc_txs.make(spec)
        self.hash = keccak256(self.raw)
        words = spec.split(",")
        self.kind = int(words[0])
        self.sender = bytes(rpc_txs.address_of(int(words[1])))
        self.gas_used = int(gas_used)
        self.status = int(status)
        self.logs = []
        if logs != "-":
            for log in logs.split("^"):
                address, topics, payload = log.split("!")
                topics = [] if topics == "-" else [bytes.fromhex(t) for t in topics.split(".")]
                self.logs.append((bytes.fromhex(address), topics, unhex(payload)))
        # The fields are read back from the signed bytes, as a node reads them.
        body = rlp.decode(self.raw if self.kind == 0 else self.raw[1:])
        number = [int.from_bytes(item, "big") if isinstance(item, bytes) else item for item in body]
        self.fields = body
        if self.kind == 0:
            names = ["nonce", "gasPrice", "gas", "to", "value", "input", "v", "r", "s"]
        elif self.kind == 1:
            names = ["chainId", "nonce", "gasPrice", "gas", "to", "value", "input", "accessList"]
            names += ["yParity", "r", "s"]
        else:
            names = ["chainId", "nonce", "maxPriorityFeePerGas", "maxFeePerGas", "gas", "to"]
            names += ["value", "input", "accessList"]
            if self.kind == 3:
                names += ["maxFeePerBlobGas", "blobVersionedHashes"]
            if self.kind == 4:
                names += ["authorizationList"]
            names += ["yParity", "r", "s"]
        self.named = dict(zip(names, body, strict=True))
        self.number = dict(zip(names, number, strict=True))
        self.to = self.named["to"] or None

    def price(self, base_fee):
        """What the sender pays per gas, by EIP-1559."""
        if self.kind < 2:
            return self.number["gasPrice"]
        return min(self.number["maxFeePerGas"], base_fee + self.number["maxPriorityFeePerGas"])

    def bloom(self):
        bloom = BloomFilter()
        for address, topics, _ in self.logs:
            bloom.add(address)
            for topic in topics:
                bloom.add(topic)
        return int(bloom).to_bytes(256, "big")


class Block:
    """A block of a view: its header as RLP, its transactions and their receipts."""

    def __init__(self, text):
        self.fork, header, txs = text.split("|")
        words = header.split(",")
        (
            self.number,
            self.time,
            self.gas_limit,
            self.gas_used,
            self.base_fee,
            self.excess,
            self.blob_used,
        ) = (int(word) for word in words[:7])
        self.coinbase = bytes.fromhex(words[7])
        self.difficulty = int(words[8])
        self.randao = bytes.fromhex(words[9])
        self.parent = bytes.fromhex(words[10])
        self.txs = [] if txs == "-" else [Tx(tx) for tx in txs.split("+")]
        self.header = rlp.encode(self.header_fields())
        self.hash = keccak256(self.header)

    def has(self, fork):
        return since(self.fork, fork)

    def fee(self):
        return self.base_fee if self.has("london") else 0

    def header_fields(self):
        """The fields of the header in the order of its RLP list, with those of each EIP."""
        fields = [
            self.parent,
            EMPTY_OMMERS,
            self.coinbase,
            ZERO,
            ZERO,
            ZERO,
            b"\x00" * 256,
            scalar(self.difficulty),
            scalar(self.number),
            scalar(self.gas_limit),
            scalar(self.gas_used),
            scalar(self.time),
            b"",
            self.randao,
            b"\x00" * 8,
        ]
        if self.has("london"):
            fields.append(scalar(self.base_fee))
        if self.has("shapella"):
            fields.append(ZERO)
        if self.has("dencun"):
            fields += [scalar(self.blob_used), scalar(self.excess), b"\x22" * 32]
        if self.has("pectra"):
            fields.append(ZERO)
        return fields

    def body(self):
        """The transactions as a block holds them: a typed one is a byte string."""
        return [tx.fields if tx.kind == 0 else tx.raw for tx in self.txs]

    def raw(self):
        parts = [self.header_fields(), self.body(), []]
        if self.has("shapella"):
            parts.append([])
        return rlp.encode(parts)

    def header_json(self):
        out = {
            "hash": data(self.hash),
            "parentHash": data(self.parent),
            "sha3Uncles": data(EMPTY_OMMERS),
            "miner": data(self.coinbase),
            "stateRoot": data(ZERO),
            "transactionsRoot": data(ZERO),
            "receiptsRoot": data(ZERO),
            "logsBloom": data(b"\x00" * 256),
            "difficulty": quantity(self.difficulty),
            "number": quantity(self.number),
            "gasLimit": quantity(self.gas_limit),
            "gasUsed": quantity(self.gas_used),
            "timestamp": quantity(self.time),
            "extraData": "0x",
            "mixHash": data(self.randao),
            "nonce": data(b"\x00" * 8),
        }
        if self.has("london"):
            out["baseFeePerGas"] = quantity(self.base_fee)
        if self.has("shapella"):
            out["withdrawalsRoot"] = data(ZERO)
        if self.has("dencun"):
            out["blobGasUsed"] = quantity(self.blob_used)
            out["excessBlobGas"] = quantity(self.excess)
            out["parentBeaconBlockRoot"] = data(b"\x22" * 32)
        if self.has("pectra"):
            out["requestsHash"] = data(ZERO)
        return out

    def tx_json(self, index):
        """The object of a transaction of the block, by the schemas of transaction.yaml."""
        tx = self.txs[index]
        n = tx.number
        out = {
            "blockHash": data(self.hash),
            "blockNumber": quantity(self.number),
            "blockTimestamp": quantity(self.time),
            "from": data(tx.sender),
            "hash": data(tx.hash),
            "transactionIndex": quantity(index),
            "type": quantity(tx.kind),
            "nonce": quantity(n["nonce"]),
            "gas": quantity(n["gas"]),
            "value": quantity(n["value"]),
            "input": data(tx.named["input"]),
            "to": data(tx.to) if tx.to else None,
            "gasPrice": quantity(tx.price(self.fee())),
            "r": quantity(n["r"]),
            "s": quantity(n["s"]),
        }
        if tx.kind == 0:
            out["v"] = quantity(n["v"])
            # EIP-155: `v` is `chain * 2 + 35` or `chain * 2 + 36` when it names a chain.
            if n["v"] >= 35:
                out["chainId"] = quantity((n["v"] - 35) // 2)
            return out
        out["chainId"] = quantity(n["chainId"])
        out["yParity"] = quantity(n["yParity"])
        out["v"] = quantity(n["yParity"])
        out["accessList"] = [
            {"address": data(address), "storageKeys": [data(key) for key in keys]}
            for address, keys in tx.named["accessList"]
        ]
        if tx.kind >= 2:
            out["maxPriorityFeePerGas"] = quantity(n["maxPriorityFeePerGas"])
            out["maxFeePerGas"] = quantity(n["maxFeePerGas"])
        if tx.kind == 3:
            out["maxFeePerBlobGas"] = quantity(n["maxFeePerBlobGas"])
            out["blobVersionedHashes"] = [data(h) for h in tx.named["blobVersionedHashes"]]
        if tx.kind == 4:
            out["authorizationList"] = [
                {
                    "chainId": quantity(int.from_bytes(chain, "big")),
                    "address": data(address),
                    "nonce": quantity(int.from_bytes(nonce, "big")),
                    "yParity": quantity(int.from_bytes(parity, "big")),
                    "r": quantity(int.from_bytes(r, "big")),
                    "s": quantity(int.from_bytes(s, "big")),
                }
                for chain, address, nonce, parity, r, s in tx.named["authorizationList"]
            ]
        return out

    def logs_json(self, index):
        """The objects of the logs of a transaction, numbered within the block."""
        first = sum(len(tx.logs) for tx in self.txs[:index])
        tx = self.txs[index]
        return [
            {
                "address": data(address),
                "topics": [data(topic) for topic in topics],
                "data": data(payload),
                "blockNumber": quantity(self.number),
                "transactionHash": data(tx.hash),
                "transactionIndex": quantity(index),
                "blockHash": data(self.hash),
                "blockTimestamp": quantity(self.time),
                "logIndex": quantity(first + i),
                "removed": False,
            }
            for i, (address, topics, payload) in enumerate(tx.logs)
        ]

    def cumulative(self, index):
        return sum(tx.gas_used for tx in self.txs[: index + 1])

    def receipt_json(self, index, blob_fee):
        """The object of a receipt of the block, by the schema of receipt.yaml."""
        tx = self.txs[index]
        created = None
        if tx.to is None:
            # The address of a creation: the hash of the sender and its nonce.
            created = keccak256(rlp.encode([tx.sender, scalar(tx.number["nonce"])]))[12:]
        out = {
            "type": quantity(tx.kind),
            "transactionHash": data(tx.hash),
            "transactionIndex": quantity(index),
            "blockHash": data(self.hash),
            "blockNumber": quantity(self.number),
            "from": data(tx.sender),
            "to": data(tx.to) if tx.to else None,
            "cumulativeGasUsed": quantity(self.cumulative(index)),
            "gasUsed": quantity(tx.gas_used),
            "contractAddress": data(created) if created else None,
            "logs": self.logs_json(index),
            "logsBloom": data(tx.bloom()),
            "effectiveGasPrice": quantity(tx.price(self.fee())),
        }
        if self.has("byzantium"):
            out["status"] = quantity(tx.status)
        else:
            out["root"] = data(ZERO)
        if tx.kind == 3:
            out["blobGasUsed"] = quantity(2**17 * len(tx.named["blobVersionedHashes"]))
            out["blobGasPrice"] = quantity(blob_fee)
        return out

    def receipt_raw(self, index):
        """The bytes of a receipt: its RLP list, behind its type for a typed transaction."""
        tx = self.txs[index]
        outcome = scalar(tx.status) if self.has("byzantium") else ZERO
        logs = [[address, topics, payload] for address, topics, payload in tx.logs]
        body = rlp.encode([outcome, scalar(self.cumulative(index)), tx.bloom(), logs])
        return body if tx.kind == 0 else bytes([tx.kind]) + body


class Chain:
    """The blocks that a node holds, and what it answers."""

    def __init__(self, activations, blocks, side, marks):
        # The timeline is not read: each block names its fork.
        self.activations = activations
        self.blocks = [Block(text) for text in blocks.split(";")]
        self.side = [] if side == "-" else [Block(text) for text in side.split(";")]
        safe, finalized, pending = marks.split("&")
        self.safe = None if safe == "-" else int(safe)
        self.finalized = None if finalized == "-" else int(finalized)
        self.pending = None if pending == "-" else Block(pending)

    def blob_fee(self, block):
        """The base fee per blob gas of a block, by EIP-4844 and the schedule of its fork."""
        if not block.has("dencun"):
            return 0
        return fake_exponential(1, block.excess, SCHEDULES[block.fork][2])

    def by_number(self, number):
        return next((b for b in self.blocks if b.number == number), None)

    def by_hash(self, digest):
        return next((b for b in self.blocks + self.side if b.hash == digest), None)

    def by_tag(self, tag):
        if tag == "latest":
            return self.blocks[-1]
        if tag == "earliest":
            return self.blocks[0]
        if tag == "pending":
            return self.pending
        number = self.safe if tag == "safe" else self.finalized
        return None if number is None else self.by_number(number)

    def find(self, digest):
        """The first block that holds a transaction, canonical blocks first, and its index."""
        for block in self.blocks + self.side:
            for index, tx in enumerate(block.txs):
                if tx.hash == digest:
                    return block, index
        return None, None


CACHE = {}


def chain_of(words):
    key = "\t".join(words)
    if key not in CACHE:
        CACHE.clear()
        CACHE[key] = Chain(*words)
    return CACHE[key]


def chain(*words):
    made = chain_of(words)

    def group(blocks):
        # A group of no block is the empty text, and a block of no transaction is `-`.
        return ";".join(".".join(tx.raw.hex() for tx in b.txs) or "-" for b in blocks)

    pending = [made.pending] if made.pending else []
    hashes = ".".join(b.hash.hex() for b in made.blocks + made.side + pending)
    return "/".join([group(made.blocks), group(made.side), group(pending), hashes])


# What a request holds.

HASH = re.compile(r"^0x[0-9a-f]{64}$")
ADDRESS = re.compile(r"^0x[0-9a-fA-F]{40}$")
UINT = re.compile(r"^0x(0|[1-9a-f][0-9a-f]*)$")
TAGS = ["earliest", "finalized", "safe", "latest", "pending"]


class RefusedError(Exception):
    """A request that a method refuses, with the codes that the source allows."""


def invalid():
    return RefusedError("-32602")


def hash_of(value):
    if not isinstance(value, str) or not HASH.match(value):
        raise invalid()
    return bytes.fromhex(value[2:])


def uint_of(value):
    if not isinstance(value, str) or not UINT.match(value):
        raise invalid()
    return int(value, 16)


def number_or_tag(made, value, tags=TAGS):
    """The block of a number or a tag, or none: the schema `BlockNumberOrTag`."""
    if isinstance(value, str) and value in TAGS:
        if value not in tags:
            raise invalid()
        return made.by_tag(value)
    return made.by_number(uint_of(value))


def number_tag_or_hash(made, value):
    """The block of the schema `BlockNumberOrTagOrHash`, with the objects of EIP-1898."""
    if isinstance(value, dict):
        if set(value) == {"blockNumber"}:
            return made.by_number(uint_of(value["blockNumber"]))
        if "blockHash" in value and set(value) <= {"blockHash", "requireCanonical"}:
            canonical = value.get("requireCanonical", False)
            if not isinstance(canonical, bool):
                raise invalid()
            block = made.by_hash(hash_of(value["blockHash"]))
            if block is not None and canonical and block not in made.blocks:
                # EIP-1898: a block off the canonical chain SHOULD get the code -32000.
                raise RefusedError("-32000")
            return block
        raise invalid()
    if isinstance(value, str) and HASH.match(value):
        return made.by_hash(hash_of(value))
    return number_or_tag(made, value)


def topic_filter(value):
    """What a filter takes at each position of the topics: none for any topic."""
    if value is None:
        return []
    if not isinstance(value, list):
        raise invalid()
    out = []
    for entry in value:
        if entry is None:
            out.append(None)
        elif isinstance(entry, list):
            out.append([hash_of(topic) for topic in entry])
        else:
            out.append([hash_of(entry)])
    return out


def address_filter(value):
    if value is None:
        return None
    entries = value if isinstance(value, list) else [value]
    for entry in entries:
        if not isinstance(entry, str) or not ADDRESS.match(entry):
            raise invalid()
    return [bytes.fromhex(entry[2:]) for entry in entries]


def get_logs(made, filt):
    """The logs of a filter, by the text of eth_getLogs and the schema `Filter`."""
    if not isinstance(filt, dict):
        raise invalid()
    addresses = address_filter(filt.get("address"))
    topics = topic_filter(filt.get("topics"))
    head = made.blocks[-1].number

    def bound(name):
        value = filt.get(name)
        if value is None:
            return None, head
        if isinstance(value, str) and value in TAGS:
            if value == "pending":
                raise invalid()
            return value, None
        return None, uint_of(value)

    from_tag, first = bound("fromBlock")
    to_tag, last = bound("toBlock")
    if filt.get("blockHash") is not None:
        if filt.get("fromBlock") is not None or filt.get("toBlock") is not None:
            raise invalid()
        block = made.by_hash(hash_of(filt["blockHash"]))
        if block is None:
            # No text gives the code of an unknown block.
            raise RefusedError("*")
        blocks = [block]
    else:
        # A number above the head is refused, and so is a tag that names no block.
        beyond = (first is not None and first > head) or (last is not None and last > head)
        for tag in [from_tag, to_tag]:
            if tag is not None and made.by_tag(tag) is None:
                raise RefusedError("-32602" if beyond else "*")
        first = made.by_tag(from_tag).number if from_tag else first
        last = made.by_tag(to_tag).number if to_tag else last
        if first > head or last > head or first > last:
            raise invalid()
        if first < made.blocks[0].number:
            raise RefusedError("4444")
        blocks = [b for b in made.blocks if first <= b.number <= last]
    out = []
    for block in blocks:
        for index in range(len(block.txs)):
            for log, (address, log_topics, _) in zip(
                block.logs_json(index), block.txs[index].logs, strict=True
            ):
                if addresses and address not in addresses:
                    continue
                if len(topics) > len(log_topics):
                    continue
                if all(
                    not want or have in want for want, have in zip(topics, log_topics, strict=False)
                ):
                    out.append(log)
    return out


def receipts(made, block):
    return [block.receipt_json(i, made.blob_fee(block)) for i in range(len(block.txs))]


def block_json(block, full):
    out = block.header_json()
    out["size"] = quantity(len(block.raw()))
    out["uncles"] = []
    if full:
        out["transactions"] = [block.tx_json(i) for i in range(len(block.txs))]
    else:
        out["transactions"] = [data(tx.hash) for tx in block.txs]
    if block.has("shapella"):
        out["withdrawals"] = []
    return out


def need(block):
    """A block, or the error of a method whose result cannot be `null`."""
    if block is None:
        raise RefusedError("*")
    return block


def flag(value):
    if not isinstance(value, bool):
        raise invalid()
    return value


def call(made, method, params):
    """The result of a method, by its text in `src/eth/*.yaml` and `src/debug/getters.yaml`."""
    count = {
        "eth_blockNumber": 0,
        "eth_getBlockByNumber": 2,
        "eth_getBlockByHash": 2,
        "eth_getTransactionByBlockHashAndIndex": 2,
        "eth_getTransactionByBlockNumberAndIndex": 2,
    }.get(method, 1)
    if not isinstance(params, list) or len(params) != count:
        raise invalid()
    if method == "eth_blockNumber":
        return quantity(made.blocks[-1].number)
    if method == "eth_getLogs":
        return get_logs(made, params[0])
    if method == "eth_getTransactionReceipt":
        block, index = made.find(hash_of(params[0]))
        return None if block is None else receipts(made, block)[index]
    if method == "eth_getBlockReceipts":
        block = number_tag_or_hash(made, params[0])
        return None if block is None else receipts(made, block)
    if method == "eth_getTransactionByHash":
        block, index = made.find(hash_of(params[0]))
        return None if block is None else block.tx_json(index)
    if method == "eth_getTransactionByBlockHashAndIndex":
        block = made.by_hash(hash_of(params[0]))
        index = uint_of(params[1])
        return None if block is None or index >= len(block.txs) else block.tx_json(index)
    if method == "eth_getTransactionByBlockNumberAndIndex":
        block = number_or_tag(made, params[0])
        index = uint_of(params[1])
        return None if block is None or index >= len(block.txs) else block.tx_json(index)
    if method == "eth_getBlockByNumber":
        block = number_or_tag(made, params[0])
        return None if block is None else block_json(block, flag(params[1]))
    if method == "eth_getBlockByHash":
        block = made.by_hash(hash_of(params[0]))
        return None if block is None else block_json(block, flag(params[1]))
    if method == "eth_getHeaderByNumber":
        # The method says that the tag `pending` gives `null`.
        block = None if params[0] == "pending" else number_or_tag(made, params[0])
        return None if block is None else block.header_json()
    if method == "eth_getHeaderByHash":
        block = made.by_hash(hash_of(params[0]))
        return None if block is None else block.header_json()
    if method == "eth_getBlockTransactionCountByNumber":
        block = number_or_tag(made, params[0])
        return None if block is None else quantity(len(block.txs))
    if method == "eth_getBlockTransactionCountByHash":
        block = made.by_hash(hash_of(params[0]))
        return None if block is None else quantity(len(block.txs))
    if method == "debug_getRawHeader":
        return data(need(number_or_tag(made, params[0])).header)
    if method == "debug_getRawBlock":
        return data(need(number_or_tag(made, params[0])).raw())
    if method == "debug_getRawReceipts":
        block = need(number_tag_or_hash(made, params[0]))
        return [data(block.receipt_raw(i)) for i in range(len(block.txs))]
    if method == "debug_getRawTransaction":
        block, index = made.find(hash_of(params[0]))
        return data(need(block).txs[index].raw)
    raise RefusedError("-32601")


def rpc(*words):
    made = chain_of(words[:4])
    try:
        result = call(made, words[4], json.loads(words[5]))
    except RefusedError as refused:
        return f"error {refused}"
    return json.dumps(result, separators=(",", ":"))


COMMANDS = {"chain": chain, "rpc": rpc}

"""References for the execution chain: one command per line, one answer per line."""

# The words of a command are separated by tabs, bytes are in hexadecimal and `-`
# is the empty byte string.  Most answers come from execution-specs (EELS), the
# others from py-trie, eth-bloom, eth-account and hashlib.
#
#     tx <fork> <chain> <bytes>        A transaction as bytes: its hash, sender,
#                                      intrinsic gas, floor and validity.
#     signed <chain> <key> <kind> ...  A transaction signed by eth-account.

import importlib
import os
import sys

from ethereum.crypto.hash import keccak256
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes
from ethereum_types.numeric import U64

COMMANDS = {}


def command(function):
    COMMANDS[function.__name__] = function
    return function


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return bytes(data).hex() if len(data) else "-"


def module(fork, name):
    return importlib.import_module(f"ethereum.forks.{fork}.{name}")


TYPED_SINCE = {1: "berlin", 2: "london", 3: "cancun", 4: "prague"}
FORKS = [
    "frontier",
    "homestead",
    "dao_fork",
    "tangerine_whistle",
    "spurious_dragon",
    "byzantium",
    "constantinople",
    "istanbul",
    "muir_glacier",
    "berlin",
    "london",
    "arrow_glacier",
    "gray_glacier",
    "paris",
    "shanghai",
    "cancun",
    "prague",
    "osaka",
    "bpo1",
    "bpo2",
]


def since(fork, other):
    return FORKS.index(fork) >= FORKS.index(other)


def decode_tx(fork, data):
    """The transaction of the bytes at a fork, as EELS reads a block body."""
    txs = module(fork, "transactions")
    if not data:
        raise ValueError("empty")
    if data[0] >= 0xC0:
        legacy = getattr(txs, "LegacyTransaction", None) or txs.Transaction
        return rlp.decode_to(legacy, data)
    if not since(fork, "berlin"):
        raise ValueError("typed transaction before Berlin")
    return txs.decode_transaction(Bytes(data))


def tx_hash(fork, tx):
    txs = module(fork, "transactions")
    if not since(fork, "berlin"):
        return keccak256(rlp.encode(tx))
    encoded = txs.encode_transaction(tx)
    return keccak256(encoded if isinstance(encoded, bytes) else rlp.encode(encoded))


def tx_type(tx):
    names = [
        "AccessListTransaction",
        "FeeMarketTransaction",
        "BlobTransaction",
        "SetCodeTransaction",
    ]
    name = type(tx).__name__
    return names.index(name) + 1 if name in names else 0


def tx_sender(fork, chain, tx):
    """The sender, or None: EELS, and the chain of a typed transaction."""
    txs = module(fork, "transactions")
    try:
        # EIP-2930: "the chainId must match", which EELS leaves to its tests.
        if tx_type(tx) and int(tx.chain_id) != chain:
            return None
        if since(fork, "spurious_dragon"):
            return txs.recover_sender(U64(chain), tx)
        return txs.recover_sender(tx)
    except Exception:
        return None


def tx_valid(fork, tx):
    """Whether the rules that read no state accept the transaction."""
    txs = module(fork, "transactions")
    try:
        txs.validate_transaction(tx)
    except Exception:
        return False
    kind = tx_type(tx)
    # EIP-1559: the priority fee is at most the maximum fee.
    if kind >= 2 and tx.max_fee_per_gas < tx.max_priority_fee_per_gas:
        return False
    if kind == 3:
        # EIP-4844: at least one blob, each hash of version 1.
        hashes = tx.blob_versioned_hashes
        if not hashes or any(h[0] != 1 for h in hashes):
            return False
        # EIP-7594: at most 6 blobs in a transaction.
        if since(fork, "osaka") and len(hashes) > 6:
            return False
    # EIP-7702: the authorization list is not empty.
    if kind == 4 and not tx.authorizations:
        return False
    return True


@command
def tx(fork, chain, data):
    try:
        decoded = decode_tx(fork, unhex(data))
    except Exception:
        return "error"
    # EELS types the gas and the fees as unbounded integers; the Yellow Paper
    # (4.2) bounds each below 2^256, and no balance pays for more.
    names = ("gas", "gas_price", "max_fee_per_gas", "max_priority_fee_per_gas")
    if any(int(getattr(decoded, name, 0)) >= 2**256 for name in names):
        return "error"
    txs = module(fork, "transactions")
    cost = txs.calculate_intrinsic_cost(decoded)
    intrinsic, floor = cost if isinstance(cost, tuple) else (cost, 0)
    sender = tx_sender(fork, int(chain), decoded)
    return " ".join(
        [
            "ok",
            tohex(tx_hash(fork, decoded)),
            tohex(sender) if sender else "badsig",
            str(int(intrinsic)),
            str(int(floor)),
            "true" if tx_valid(fork, decoded) else "false",
        ]
    )


def big(data):
    return int.from_bytes(data, "big")


def access_list(items):
    return [
        {"address": "0x" + address.hex(), "storageKeys": ["0x" + k.hex() for k in keys]}
        for address, keys in items
    ]


@command
def signed(kind, key, fields):
    """A transaction of eth-account from the RLP of its unsigned fields.

    Legacy: nonce, gas price, gas, to, value, data, chain (0 for none).
    Typed: the fields of the type before the signature, in order.
    Each authorization is chain, address, nonce and the key of its authority.
    """
    from eth_account import Account
    from eth_account._utils.legacy_transactions import (
        serializable_unsigned_transaction_from_dict as unsigned,
    )

    import rlp as pyrlp

    kind = int(kind)
    f = pyrlp.decode(unhex(fields))
    authorities = []
    if kind == 0:
        names = ["nonce", "gasPrice", "gas", "to", "value", "data", "chainId"]
        tx = dict(zip(names, f, strict=True))
        if not tx["chainId"]:
            del tx["chainId"]
    else:
        names = ["chainId", "nonce"]
        names += ["gasPrice"] if kind == 1 else ["maxPriorityFeePerGas", "maxFeePerGas"]
        names += ["gas", "to", "value", "data", "accessList"]
        extra = {3: ["maxFeePerBlobGas", "blobVersionedHashes"], 4: ["authorizationList"]}
        names += extra.get(kind, [])
        tx = dict(zip(names, f, strict=True), type=kind)
        tx["accessList"] = access_list(tx["accessList"])
    if kind == 4:
        auths = []
        for chain, address, nonce, authority in tx["authorizationList"]:
            account = Account.from_key(authority.rjust(32, b"\0"))
            authorities.append(account.address[2:].lower())
            auths.append(
                account.sign_authorization(
                    {"chainId": big(chain), "address": address, "nonce": big(nonce)}
                )
            )
        tx["authorizationList"] = auths
    plain = ("to", "data", "accessList", "blobVersionedHashes", "authorizationList", "type")
    for name in tx:
        if name not in plain:
            tx[name] = big(tx[name])
    account = Account.from_key(unhex(key).rjust(32, b"\0"))
    out = account.sign_transaction(tx)
    return " ".join(
        [
            tohex(out.raw_transaction),
            tohex(out.hash),
            account.address[2:].lower(),
            tohex(unsigned(tx).hash()),
            ",".join(authorities) or "-",
        ]
    )


def pairs(words):
    """The key and value of each `key=value` word."""
    return [tuple(unhex(part) for part in word.split("=")) for word in words]


@command
def trieroot(secured, *entries):
    """The root of EELS for the entries, set in order."""
    trie = module("osaka", "trie")
    t = trie.Trie(secured=secured == "1", default=b"")
    for key, value in pairs(entries):
        trie.trie_set(t, key, value)
    return tohex(trie.root(t))


def hexary(entries):
    from trie import HexaryTrie

    t = HexaryTrie(db={})
    for key, value in pairs(entries):
        t[key] = value
    return t


@command
def trieproof(key, *entries):
    """The proof of py-trie: the root node, then each node held by hash."""
    import rlp as pyrlp

    t = hexary(entries)
    nodes = [pyrlp.encode(node) for node in t.get_proof(unhex(key))]
    # The empty trie has no node; its root is the hash of the empty string.
    kept = [n for i, n in enumerate(nodes) if i == 0 or len(n) >= 32] or [b"\x80"]
    return " ".join([tohex(t.root_hash)] + [tohex(n) for n in kept])


@command
def trieverify(root, key, *nodes):
    """The value that py-trie reads from a proof, `absent`, or `error`."""
    import rlp as pyrlp
    from trie import HexaryTrie

    try:
        proof = [pyrlp.decode(unhex(node)) for node in nodes]
        value = HexaryTrie.get_from_proof(unhex(root), unhex(key), proof)
    except Exception:
        return "error"
    return tohex(value) if value else "absent"


MACHINES = {}


@command
def sm_trie(action, *words):
    """A py-trie that lives across commands: `new`, or `set <key> <value>`.

    It answers the root.  An empty value deletes the key.
    """
    from trie import HexaryTrie

    if action == "new":
        MACHINES["trie"] = HexaryTrie(db={})
    else:
        key, value = (unhex(word) for word in words)
        # py-trie deletes a key that is set to the empty value.
        MACHINES["trie"][key] = value
    return tohex(MACHINES["trie"].root_hash)


def parse_log(word):
    """A log from `address:topic,topic:data`."""
    address, topics, data = word.split(":")
    return unhex(address), [unhex(t) for t in topics.split(",") if t], unhex(data)


@command
def bloom(*words):
    """The logs bloom of EELS, which eth-bloom must agree with."""
    from eth_bloom import BloomFilter

    blocks = module("osaka", "blocks")
    logs = []
    other = BloomFilter()
    for address, topics, data in map(parse_log, words):
        logs.append(blocks.Log(address=address, topics=tuple(topics), data=data))
        for entry in [address] + topics:
            other.add(entry)
    result = module("osaka", "bloom").logs_bloom(logs)
    if int(other).to_bytes(256, "big") != bytes(result):
        return "error the references disagree"
    return tohex(result)


@command
def header(fork, data):
    """A header as bytes at a fork: its hash and some of its fields."""
    blocks = module(fork, "blocks")
    try:
        h = rlp.decode_to(blocks.Header, unhex(data))
    except Exception:
        return "error"
    fields = [h.difficulty, h.number, h.gas_limit, h.gas_used, h.timestamp]
    for name in ("base_fee_per_gas", "blob_gas_used", "excess_blob_gas"):
        if hasattr(h, name):
            fields.append(getattr(h, name))
    words = ["ok", tohex(keccak256(rlp.encode(h)))] + [str(int(x)) for x in fields]
    return " ".join(words)


@command
def headerpair(fork, parent, child):
    """Whether EELS accepts a header after its parent, the seal aside."""
    from types import SimpleNamespace

    blocks = module(fork, "blocks")
    rules = module(fork, "fork")
    try:
        p = rlp.decode_to(blocks.Header, unhex(parent))
        c = rlp.decode_to(blocks.Header, unhex(child))
    except Exception:
        return "undecodable"
    if hasattr(rules, "validate_proof_of_work"):
        rules.validate_proof_of_work = lambda header: None
    chain = SimpleNamespace(blocks=[SimpleNamespace(header=p)])
    try:
        rules.validate_header(chain, c)
    except Exception as error:
        return f"error {type(error).__name__}"
    return "ok"


@command
def ommers(fork, header, candidates, *chain):
    """Whether EELS accepts the ommers of a block, the seal aside.

    Each block of the chain is `header:ommer,ommer`, the oldest first.
    """
    from types import SimpleNamespace

    blocks = module(fork, "blocks")
    rules = module(fork, "fork")
    rules.validate_proof_of_work = lambda header: None

    def read(word):
        return rlp.decode_to(blocks.Header, unhex(word))

    def many(word):
        return tuple(read(w) for w in word.split(",") if w and w != "-")

    history = []
    for word in chain:
        head, _, rest = word.partition(":")
        history.append(SimpleNamespace(header=read(head), ommers=many(rest)))
    try:
        rules.validate_ommers(many(candidates), read(header), SimpleNamespace(blocks=history))
    except Exception as error:
        return f"error {type(error).__name__}"
    return "ok"


@command
def receipt(fork, data):
    """A receipt as bytes at a fork: its type, outcome, gas, logs and hash."""
    blocks = module(fork, "blocks")
    data = unhex(data)
    try:
        if not data:
            raise ValueError("empty")
        if data[0] >= 0xC0:
            kind, r = 0, rlp.decode_to(blocks.Receipt, data)
        elif not since(fork, "berlin"):
            raise ValueError("typed receipt before Berlin")
        else:
            kind, r = data[0], blocks.decode_receipt(Bytes(data))
    except Exception:
        return "error"
    if hasattr(r, "succeeded"):
        outcome = "true" if r.succeeded else "false"
    else:
        outcome = tohex(r.post_state)
    words = ["ok", str(kind), outcome, str(int(r.cumulative_gas_used)), str(len(r.logs))]
    return " ".join(words + [tohex(keccak256(rlp.encode(r)))])


@command
def difficulty(fork, number, timestamp, parent_timestamp, parent_difficulty, ommers):
    from ethereum_types.numeric import U256, Uint

    rules = module(fork, "fork")
    args = [Uint(int(number)), U256(int(timestamp)), U256(int(parent_timestamp))]
    args.append(Uint(int(parent_difficulty)))
    if since(fork, "byzantium"):
        args.append(ommers == "true")
    return str(int(rules.calculate_block_difficulty(*args)))


@command
def reward(fork):
    return str(int(module(fork, "fork").BLOCK_REWARD))


@command
def requestshash(*requests):
    """EIP-7685: sha256 of the sha256 of each request longer than its type."""
    import hashlib

    outer = hashlib.sha256()
    for request in map(unhex, requests):
        if len(request) > 1:
            outer.update(hashlib.sha256(request).digest())
    return outer.hexdigest()


@command
def deposit(data):
    """The deposit request of the data of a deposit log, by EELS."""
    try:
        return tohex(module("prague", "requests").extract_deposit_data(unhex(data)))
    except Exception:
        return "error"


@command
def withdrawalsroot(*words):
    """The root of withdrawals `index:validator:address:amount`, by EELS."""
    from ethereum_types.numeric import U64, U256, Uint

    blocks = module("osaka", "blocks")
    trie = module("osaka", "trie")
    t = trie.Trie(secured=False, default=None)
    for i, word in enumerate(words):
        index, validator, address, amount = word.split(":")
        w = blocks.Withdrawal(
            index=U64(int(index)),
            validator_index=U64(int(validator)),
            address=unhex(address),
            amount=U256(int(amount)),
        )
        trie.trie_set(t, rlp.encode(Uint(i)), rlp.encode(w))
    return tohex(trie.root(t))


@command
def indexroot(*values):
    """The root of a list: the plain trie of `rlp(index)` to each value."""
    from ethereum_types.numeric import Uint

    trie = module("osaka", "trie")
    t = trie.Trie(secured=False, default=b"")
    for i, value in enumerate(values):
        trie.trie_set(t, rlp.encode(Uint(i)), unhex(value))
    return tohex(trie.root(t))


@command
def dao(index):
    """The DAO account at an index of EIP-779, the count, and the recovery."""
    d = module("dao_fork", "dao")
    accounts = d.DAO_ACCOUNTS
    i = int(index)
    account = tohex(accounts[i]) if i < len(accounts) else "none"
    return f"{account} {len(accounts)} {tohex(d.DAO_RECOVERY)}"


ADDRESSES = [bytes([b]) * 20 for b in (0, 1, 2, 0xFF)]
SLOTS = [bytes([b]) * 32 for b in (0, 1, 2)]
CODES = [b"", b"\x00", b"\x60\x00"]


class Twin:
    """A state of `state.py` at a fork, driven one operation at a time."""

    def __init__(self, fork):
        self.fork = fork
        self.m = module(fork, "state")
        self.state = self.m.State()
        self.has_transient = hasattr(self.m, "TransientStorage")
        self.transient = self.m.TransientStorage() if self.has_transient else None
        self.begin()

    def begin(self):
        if self.has_transient:
            self.m.begin_transaction(self.state, self.transient)
        else:
            self.m.begin_transaction(self.state)

    def commit(self):
        if self.has_transient:
            self.m.commit_transaction(self.state, self.transient)
        else:
            self.m.commit_transaction(self.state)

    def rollback(self):
        if self.has_transient:
            self.m.rollback_transaction(self.state, self.transient)
        else:
            self.m.rollback_transaction(self.state)

    def run(self, name, *args):
        from ethereum_types.numeric import U256

        m, state = self.m, self.state
        n = [int(a) for a in args]
        a = ADDRESSES[n[0]] if n else None
        if name == "balance":
            m.set_account_balance(state, a, U256(n[1]))
        elif name == "nonce":
            m.increment_nonce(state, a)
        elif name == "code":
            m.set_code(state, a, CODES[n[1]])
        elif name == "move":
            try:
                m.move_ether(state, a, ADDRESSES[n[1]], U256(n[2]))
            except AssertionError:
                pass
        elif name == "create":

            def add(account):
                account.balance += U256(n[1])

            m.modify_state(state, a, add)
        elif name == "storage":
            if m.get_account_optional(state, a) is not None:
                m.set_storage(state, a, SLOTS[n[1]], U256(n[2]))
        elif name == "destroystorage":
            m.destroy_storage(state, a)
        elif name == "destroy":
            m.destroy_account(state, a)
        elif name == "created":
            if hasattr(m, "mark_account_created"):
                m.mark_account_created(state, a)
            elif hasattr(state, "created_accounts"):
                state.created_accounts.add(a)
        elif name == "transient":
            if self.has_transient:
                m.set_transient_storage(self.transient, a, SLOTS[n[1]], U256(n[2]))
        elif name == "touch":
            if not m.account_exists(state, a):
                m.set_account(state, a, module(self.fork, "fork_types").EMPTY_ACCOUNT)
        elif name == "destroytouched":
            if hasattr(m, "destroy_touched_empty_accounts"):
                m.destroy_touched_empty_accounts(state, [ADDRESSES[i] for i in n])
        elif name == "snapshot":
            self.begin()
        elif name == "rollback":
            self.rollback()
        elif name == "commit":
            self.commit()
        elif name == "end":
            # The outer transaction ends, the root is taken, and the next begins.
            self.commit()
            root = m.state_root(state)
            if self.has_transient:
                self.transient = m.TransientStorage()
            self.begin()
            return self.reads() + [tohex(root)]
        else:
            raise ValueError(name)
        return self.reads()

    def reads(self):
        m, state = self.m, self.state
        words = []
        for a in ADDRESSES:
            account = m.get_account_optional(state, a)
            if account is None:
                parts = ["none"]
            else:
                code = CODES.index(bytes(account.code))
                parts = [f"{int(account.nonce)}/{int(account.balance)}/{code}"]
            parts.append("true" if m.account_has_storage(state, a) else "false")
            alive = account is not None and (
                account.nonce != 0 or account.balance != 0 or account.code != b""
            )
            parts.append("true" if alive else "false")
            for key in SLOTS:
                now = int(m.get_storage(state, a, key))
                if hasattr(m, "get_storage_original"):
                    original = int(m.get_storage_original(state, a, key))
                else:
                    original = "x"
                transient = 0
                if self.has_transient:
                    transient = int(m.get_transient_storage(self.transient, a, key))
                parts.append(f"{now},{original},{transient}")
            words.append(";".join(parts))
        return words


@command
def state(name, *args):
    """An operation on the twin state; `new <fork>` starts one."""
    if name == "new":
        MACHINES["state"] = Twin(args[0])
        return "ok"
    return " ".join(MACHINES["state"].run(name, *args))


# With EXECUTION_ORACLE_STATS set, count the answers of each command, to see
# how many inputs of a generator the reference accepts.
STATS = {}

for line in sys.stdin:
    words = line.rstrip("\n").split("\t")
    try:
        answer = COMMANDS[words[0]](*words[1:])
    except Exception as error:
        answer = f"error {type(error).__name__} {error}".replace("\n", " ")
    try:
        print(answer or "-", flush=True)
    except BrokenPipeError:
        break
    kind = (words[0], "error" if answer.startswith("error") else "ok")
    STATS[kind] = STATS.get(kind, 0) + 1

if os.environ.get("EXECUTION_ORACLE_STATS"):
    for kind, count in sorted(STATS.items()):
        print(*kind, count, file=sys.stderr)

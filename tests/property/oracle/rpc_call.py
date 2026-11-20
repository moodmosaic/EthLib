"""A model of eth_call and eth_estimateGas, which runs the message in EELS."""

#     keys
#         The addresses of the eight keys that sign, joined with `,`.
#     call <fork> <headers> <index> <accounts> <request>
#         What eth_call answers: `ok <output>|<gas left>|<logs>`, or `error <codes>|<data>`.
#     estimate <fork> <headers> <index> <accounts> <request> <gas>
#         What eth_estimateGas answers, and what the gas limit `gas` and the one below it do:
#         `ok <estimate>|<completes at gas>|<at gas - 1>|<signed at gas>|<at gas - 1>|<lower>`.
#
# The fork is `<name in EthLib>:<module of EELS>`.
# The headers are those of `rpc_logs.py`, joined with `;`.
# The call runs on the state after the header at the index.
# An account is `address,nonce,balance,code,key=value&key=value`, and they are joined with `;`.
# The request is the JSON text of the call object.
#
# The file execute.yaml fixes few rules of a call.
# EthLib writes down its choices for the others, in `EthLib/Execution/Rpc/Call.lean`.
# This model takes those choices from that text, and what the message does from EELS.
# `process_transaction` of the fork runs without the checks of a signed transaction.
# The sender and the price of the request take their place.
# A request with several faults may be refused for any of them.
# So the model answers the codes of all.

import dataclasses
import importlib
import json
import re

import rpc_txs
from ethereum.exceptions import EthereumException
from ethereum_types.bytes import Bytes0, Bytes20, Bytes32
from ethereum_types.numeric import U64, U256, Uint
from rpc_logs import Block

CHAIN_ID = 1
TYPE_SINCE = {0: "frontier", 1: "berlin", 2: "london", 3: "dencun", 4: "pectra"}
FIELDS = [
    "type",
    "nonce",
    "to",
    "from",
    "gas",
    "value",
    "input",
    "gasPrice",
    "maxPriorityFeePerGas",
    "maxFeePerGas",
    "maxFeePerBlobGas",
    "accessList",
    "blobVersionedHashes",
    "blobs",
    "commitments",
    "proofs",
    "chainId",
    "authorizationList",
]
UINT = re.compile(r"^0x(0|[1-9a-f][0-9a-f]*)$")
BYTE = re.compile(r"^0x[0-9a-f]{1,2}$")
ADDRESS = re.compile(r"^0x[0-9a-fA-F]{40}$")
BYTES = re.compile(r"^0x([0-9a-f]{2})*$")
HASH = re.compile(r"^0x[0-9a-f]{64}$")


class Fork:
    """The modules of one fork of the reference, with a hook on the message of a transaction."""

    def __init__(self, name):
        base = "ethereum.forks." + name
        self.name = name
        self.vm = importlib.import_module(base + ".vm")
        self.state = importlib.import_module(base + ".state")
        self.types = importlib.import_module(base + ".fork_types")
        self.fork = importlib.import_module(base + ".fork")
        self.tx = importlib.import_module(base + ".transactions")
        self.exceptions = importlib.import_module(base + ".vm.exceptions")
        mapping = importlib.import_module(base + ".vm.precompiled_contracts.mapping")
        self.precompiles = {bytes(address) for address in mapping.PRE_COMPILED_CONTRACTS}
        self.last = None
        run_message = self.fork.process_message_call

        def message_call(message):
            self.last = run_message(message)
            return self.last

        self.fork.process_message_call = message_call
        # The output of the first message: only the latest forks give it with the result.
        self.top = None
        interpreter = importlib.import_module(base + ".vm.interpreter")
        for name in ("process_message", "process_create_message"):
            setattr(interpreter, name, self.recording(getattr(interpreter, name)))
        self.check = self.fork.check_transaction
        self.validate = self.fork.validate_transaction
        self.data_fee = getattr(self.fork, "calculate_data_fee", None)

    def recording(self, run):
        def recorded(message):
            evm = run(message)
            if int(message.depth) == 0:
                self.top = evm
            return evm

        return recorded


FORKS = {}


def fork_of(name):
    if name not in FORKS:
        FORKS[name] = Fork(name)
    return FORKS[name]


def build(cls, values):
    """An instance of a dataclass from the values it has fields for."""
    return cls(**{f.name: values[f.name] for f in dataclasses.fields(cls)})


def make_state(fork, word):
    state = fork.state.State()
    if word == "-":
        return state
    for entry in word.split(";"):
        address, nonce, balance, code, storage = entry.split(",")
        code = b"" if code == "-" else bytes.fromhex(code)
        account = fork.types.Account(Uint(int(nonce)), U256(int(balance)), code)
        fork.state.set_account(state, Bytes20(bytes.fromhex(address)), account)
        if storage != "-":
            for slot in storage.split("&"):
                key, value = slot.split("=")
                fork.state.set_storage(
                    state,
                    Bytes20(bytes.fromhex(address)),
                    Bytes32(bytes.fromhex(key)),
                    U256(int(value, 16)),
                )
    return state


class RefusedError(Exception):
    """A request that is refused before its message runs, with the codes of its faults."""


class Request:
    """A call object, read by the schema `GenericTransaction`."""

    def __init__(self, text):
        obj = json.loads(text)
        if not isinstance(obj, dict) or any(name not in FIELDS for name in obj):
            raise RefusedError("-32602")
        # Only the recipient may be `null` by the schema, and EthLib reads any `null` as absent.
        obj = {name: value for name, value in obj.items() if value is not None}

        def read(name, pattern, convert):
            if name not in obj:
                return None
            value = obj[name]
            if not isinstance(value, str) or not pattern.match(value):
                raise RefusedError("-32602")
            return convert(value)

        def number(value):
            return int(value, 16)

        def raw(value):
            return bytes.fromhex(value[2:])

        self.type = read("type", BYTE, number)
        self.nonce = read("nonce", UINT, number)
        self.to = read("to", ADDRESS, raw)
        self.sender = read("from", ADDRESS, raw)
        self.gas = read("gas", UINT, number)
        self.value = read("value", UINT, number)
        self.input = read("input", BYTES, raw)
        self.gas_price = read("gasPrice", UINT, number)
        self.priority = read("maxPriorityFeePerGas", UINT, number)
        self.max_fee = read("maxFeePerGas", UINT, number)
        self.blob_fee = read("maxFeePerBlobGas", UINT, number)
        self.chain = read("chainId", UINT, number)
        self.access = None
        if "accessList" in obj:
            self.access = []
            entries = obj["accessList"]
            if not isinstance(entries, list):
                raise RefusedError("-32602")
            for entry in entries:
                if not isinstance(entry, dict) or set(entry) != {"address", "storageKeys"}:
                    raise RefusedError("-32602")
                keys = entry["storageKeys"]
                address = entry["address"]
                if not isinstance(address, str) or not ADDRESS.match(address):
                    raise RefusedError("-32602")
                if not isinstance(keys, list):
                    raise RefusedError("-32602")
                if any(not isinstance(k, str) or not HASH.match(k) for k in keys):
                    raise RefusedError("-32602")
                self.access.append((raw(address), [raw(k) for k in keys]))
        self.blobs = None
        if "blobVersionedHashes" in obj:
            hashes = obj["blobVersionedHashes"]
            if not isinstance(hashes, list):
                raise RefusedError("-32602")
            if any(not isinstance(h, str) or not HASH.match(h) for h in hashes):
                raise RefusedError("-32602")
            self.blobs = [raw(h) for h in hashes]

    def names_fee(self):
        return any(x is not None for x in (self.gas_price, self.max_fee, self.priority))

    def kind(self):
        """The type of the request, else the latest type whose own fields it has."""
        if self.type is not None:
            return self.type
        if self.blobs is not None or self.blob_fee is not None:
            return 3
        if self.max_fee is not None or self.priority is not None:
            return 2
        return 1 if self.access is not None else 0


class Call:
    """A request on the state after a block, as `Call.lean` says a call runs."""

    def __init__(self, fork, headers, index, accounts, request):
        self.ethlib, eels = fork.split(":")
        self.fork = fork_of(eels)
        self.blocks = [Block(f"{self.ethlib}|{h}|-") for h in headers.split(";")]
        self.block = self.blocks[int(index)]
        self.accounts = accounts
        self.request = Request(request)

    def has(self, fork):
        return self.block.has(fork)

    def environment(self, state, base_fee):
        block = self.block
        before = [Bytes32(b.hash) for b in self.blocks if b.number < block.number][-256:]
        # A block that the node does not hold has no hash, and BLOCKHASH then gives zero.
        missing = min(block.number, 256) - len(before)
        before = [Bytes32(b"\x00" * 32)] * missing + before
        values = {
            "chain_id": U64(CHAIN_ID),
            "state": state,
            "block_gas_limit": Uint(block.gas_limit),
            "block_hashes": before,
            "coinbase": Bytes20(block.coinbase),
            "number": Uint(block.number),
            "time": U256(block.time),
            "difficulty": Uint(block.difficulty),
            "base_fee_per_gas": Uint(base_fee),
            "prev_randao": Bytes32(block.randao),
            "excess_blob_gas": U64(block.excess),
            "parent_beacon_block_root": Bytes32(b"\x22" * 32),
        }
        return build(self.fork.vm.BlockEnvironment, values)

    def transaction(self, kind, nonce, gas, key=None):
        """The transaction of the request: unsigned, or signed with a key."""
        r = self.request
        fields = {
            "nonce": U256(nonce),
            "gas": Uint(gas),
            "to": Bytes0(b"") if r.to is None else Bytes20(r.to),
            "value": U256(r.value or 0),
            "data": r.input or b"",
            "r": U256(0),
            "s": U256(0),
        }
        tx = self.fork.tx
        if kind == 0:
            cls = getattr(tx, "LegacyTransaction", None) or tx.Transaction
            return cls(gas_price=Uint(r.gas_price or 0), v=U256(0), **fields)
        fields["chain_id"] = U64(CHAIN_ID)
        fields["y_parity"] = U256(0)
        fields["access_list"] = tuple(
            tx.Access(account=Bytes20(address), slots=tuple(Bytes32(k) for k in keys))
            for address, keys in (r.access or [])
        )
        if kind == 1:
            return tx.AccessListTransaction(gas_price=Uint(r.gas_price or 0), **fields)
        fields["max_priority_fee_per_gas"] = Uint(r.priority or 0)
        fields["max_fee_per_gas"] = Uint(self.max_fee())
        if kind == 2:
            return tx.FeeMarketTransaction(**fields)
        if kind == 4:
            fields["nonce"] = U64(nonce)
            return tx.SetCodeTransaction(authorizations=(), **fields)
        return tx.BlobTransaction(
            max_fee_per_blob_gas=U256(r.blob_fee or 0),
            blob_versioned_hashes=tuple(Bytes32(h) for h in (r.blobs or [])),
            **fields,
        )

    def base_fee(self):
        return self.block.fee()

    def max_fee(self):
        """The fee cap: a missing one is the base fee plus the priority fee, and 0 with no fee."""
        r = self.request
        if not r.names_fee():
            return 0
        return r.max_fee if r.max_fee is not None else self.base_fee() + (r.priority or 0)

    def price(self):
        """What the request pays per gas, by EIP-1559, and 0 when it names no fee."""
        r = self.request
        if not r.names_fee():
            return 0
        if r.kind() < 2:
            return r.gas_price or 0
        return min(self.max_fee(), self.base_fee() + (r.priority or 0))

    def run(self, gas):
        """Run the call with a gas limit, or with the default one.

        It gives the output of the message, or raises the codes of the faults of the request.
        """
        r = self.request
        kind = r.kind()
        fork = self.fork
        state = make_state(fork, self.accounts)
        sender = Bytes20(r.sender or b"\x00" * 20)
        account = fork.state.get_account(state, sender)
        gas = self.block.gas_limit if gas is None else gas
        faults = set()
        # The fields that the kind of the request cannot carry, and the chain.
        if kind > 4:
            raise RefusedError("-32602")
        if kind <= 1 and (r.max_fee is not None or r.priority is not None):
            faults.add("-32602")
        if kind >= 2 and r.gas_price is not None:
            faults.add("-32602")
        if kind == 0 and r.access is not None:
            faults.add("-32602")
        if kind != 3 and (r.blobs is not None or r.blob_fee is not None):
            faults.add("-32602")
        if r.chain is not None and r.chain != CHAIN_ID:
            faults.add("-32602")
        if kind >= 3 and r.to is None:
            faults.add("-32602")
        if not self.has(TYPE_SINCE[kind]):
            faults.add("-32602")
        numbers = [gas, r.value, r.gas_price, r.max_fee, r.priority, r.blob_fee]
        if any(n is not None and n >= 2**256 for n in numbers) or self.max_fee() >= 2**256:
            raise RefusedError("-32602")
        names_fee = r.names_fee()
        base_fee = self.base_fee() if names_fee else 0
        if kind >= 2 and names_fee and (r.priority or 0) > self.max_fee():
            faults.add("804")
        cap = self.max_fee() if kind >= 2 else (r.gas_price or 0)
        if names_fee and cap < self.base_fee():
            faults.add("806")
        price = self.price()
        value = r.value or 0
        blob_fee = 0
        cost = None
        if self.has(TYPE_SINCE[kind]) and not (kind >= 3 and r.to is None):
            tx = self.transaction(kind, int(account.nonce), gas)
            if kind == 3 and names_fee:
                blob_fee = int(fork.data_fee(U64(self.block.excess), tx))
            cost = fork.tx.calculate_intrinsic_cost(tx)
            intrinsic = max(int(c) for c in cost) if isinstance(cost, tuple) else int(cost)
            self.intrinsic = intrinsic
            if gas < intrinsic:
                faults.add("800")
        if value > int(account.balance) or gas * price + blob_fee + value > int(account.balance):
            faults.add("809")
        if faults:
            raise RefusedError(",".join(sorted(faults)))
        hashes = tuple(Bytes32(h) for h in (r.blobs or []))

        def check(block_env, block_output, tx):
            names = str(fork.check.__annotations__["return"])
            if "Tuple" not in names:
                return sender
            if "Bytes32" not in names:
                return sender, Uint(price)
            return sender, Uint(price), hashes, fork.vm.gas.calculate_total_blob_gas(tx)

        fork.fork.check_transaction = check
        fork.fork.validate_transaction = lambda tx: cost
        if fork.data_fee is not None:
            fork.fork.calculate_data_fee = lambda excess, tx: Uint(blob_fee)
        try:
            env = self.environment(state, base_fee)
            fork.last = None
            fork.top = None
            fork.fork.process_transaction(env, fork.vm.BlockOutput(), tx, Uint(0))
        except OverflowError:
            # A balance above `2^256 - 1`: the reference has no rule, and EthLib aborts the call.
            raise RefusedError("-32603") from None
        finally:
            fork.fork.check_transaction = fork.check
            fork.fork.validate_transaction = fork.validate
            if fork.data_fee is not None:
                fork.fork.calculate_data_fee = fork.data_fee
        return fork.last

    def answer(self, gas):
        """What eth_call answers with a gas limit, and whether the call completes."""
        try:
            out = self.run(gas)
        except RefusedError as refused:
            return f"error {refused}|-", False
        error = out.error
        data = b"" if self.fork.top is None else bytes(self.fork.top.output)
        # The latest forks give the output with the result, and the two agree.
        assert bytes(getattr(out, "return_data", data)) == data
        output = data.hex() or "-"
        if error is None:
            return f"ok {output}|{int(out.gas_left)}|{len(out.logs)}", True
        if isinstance(error, getattr(self.fork.exceptions, "Revert", ())):
            return f"error 3|{output}", False
        if isinstance(error, self.fork.exceptions.OutOfGasError):
            # EthLib has one error for a precompile that rejects its input or lacks gas.
            if self.request.to in self.fork.precompiles:
                return "error 801,-32000|-", False
            return "error 801|-", False
        if isinstance(error, self.fork.exceptions.InvalidOpcode):
            return "error 4|-", False
        return "error -32000|-", False

    def real(self, gas):
        """What a signed transaction of the request with a gas limit does in the block."""
        r = self.request
        keys = [bytes(rpc_txs.address_of(i)) for i in range(8)]
        if r.sender not in keys or not r.names_fee() or r.kind() == 4:
            return "-"
        fork = self.fork
        state = make_state(fork, self.accounts)
        nonce = int(fork.state.get_account(state, Bytes20(r.sender)).nonce)
        access = "/".join(
            f"{address.hex()}:{'.'.join(k.hex() for k in keys)}" for address, keys in r.access or []
        )
        spec = [
            r.kind(),
            keys.index(r.sender),
            CHAIN_ID,
            nonce,
            r.gas_price or 0,
            r.priority or 0,
            self.max_fee(),
            gas,
            r.to.hex() if r.to else "-",
            r.value or 0,
            (r.input or b"").hex() or "-",
            access or "-",
            r.blob_fee or 0,
            ".".join(h.hex() for h in r.blobs or []) or "-",
            "-",
            0,
        ]
        raw = rpc_txs.make(",".join(str(word) for word in spec))
        try:
            if raw[0] >= 0xC0:
                legacy = getattr(fork.tx, "LegacyTransaction", None) or fork.tx.Transaction
                tx = importlib.import_module("ethereum_rlp.rlp").decode_to(legacy, raw)
            else:
                tx = fork.tx.decode_transaction(raw)
            fork.last = None
            env = self.environment(state, self.base_fee())
            fork.fork.process_transaction(env, fork.vm.BlockOutput(), tx, Uint(0))
        except EthereumException as error:
            return "invalid:" + type(error).__name__
        return "success" if fork.last.error is None else "failed"


def call(fork, headers, index, accounts, request):
    try:
        made = Call(fork, headers, index, accounts, request)
    except RefusedError as refused:
        return f"error {refused}|-"
    return made.answer(made.request.gas)[0]


def estimate(fork, headers, index, accounts, request, gas):
    """The estimate of the model, and what the gas limit of EthLib and the one below it do."""
    # The search is the one that the text of the method describes.
    # It is a binary search between 0 and the gas limit of the request, or the default one.
    try:
        made = Call(fork, headers, index, accounts, request)
    except RefusedError as refused:
        return f"error {refused}|-"
    high = made.block.gas_limit if made.request.gas is None else made.request.gas
    first, completes = made.answer(high)
    if not completes:
        return first
    low = 0
    while low + 1 < high:
        middle = (low + high) // 2
        if made.answer(middle)[1]:
            high = middle
        else:
            low = middle
    fields = [str(high)]
    if gas != "-":
        gas = int(gas)
        below = made.answer(gas - 1)[1] if gas > 0 else False
        fields += [str(int(made.answer(gas)[1])), str(int(below)), made.real(gas)]
        fields.append(made.real(gas - 1) if gas > 0 else "-")
        # Some limits well below: one that completes says that the limits form no interval.
        probes = [made.intrinsic + more for more in (0, 1, 100, 1000, 5000, 20000, 39000)]
        fields.append(str(int(any(p < gas - 1 and made.answer(p)[1] for p in probes))))
    return "ok " + "|".join(fields)


def keys():
    return ",".join(bytes(rpc_txs.address_of(i)).hex() for i in range(8))


COMMANDS = {"call": call, "estimate": estimate, "keys": keys}

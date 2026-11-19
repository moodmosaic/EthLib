"""References for the EVM: the Python execution-specs (EELS), one command per line.

    run <fork> <kind> <static> <gas> <value> <data> <code> <accounts>
        Run a message with `process_message` (kind call) or
        `process_create_message` (kind create), and print what it left.
    frame <fork> <gas> <static>    Start a frame that the next commands step.
    op <code>                      Run `code` in it, from its first byte.
    pre <fork> <address> <gas> <data>   Call a precompile.
    mk <kind> <a> <b> <c> <mutation> <cut>   Call data from a recipe.
    basefee <fork> <limit> <used> <fee>          The base fee of the child.
    excess <fork> <excess> <used> <base fee>     Its excess blob gas.
    blobfee <fork> <excess>                      The blob gas price.
    jumpdests <fork> <code>                      The valid jump destinations.
    create <fork> <sender> <nonce>               The address of a creation.
    create2 <fork> <sender> <salt> <code>        The address of CREATE2.
    extend <fork> <size> <start:size>...         The price and size of a memory growth.
    gaslimit <fork> <limit> <parent limit>       Whether the limit may follow.
    taylor <factor> <numerator> <denominator>    `fake_exponential` of EIP-4844.

Bytes are in hexadecimal, `-` for none.  An account is
`address,nonce,balance,code,key=value&key=value`, and accounts are joined
with `;`.
"""

import dataclasses
import importlib
import os
import signal
import sys

# The interpreter runs isolated, so the directory of this file is not on the path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import evm_inputs  # noqa: E402
from ethereum.crypto.hash import keccak256
from ethereum.exceptions import EthereumException
from ethereum_types.bytes import Bytes0, Bytes20, Bytes32
from ethereum_types.numeric import U64, U256, Uint

CALLER = bytes.fromhex("ca" * 20)
TARGET = bytes.fromhex("c0de" * 10)
COINBASE = bytes.fromhex("ba5e" * 10)
BLOB_HASHES = (b"\x01" + b"\xb1" * 31, b"\x01" + b"\xb2" * 31)


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return bytes(data).hex() if data else "-"


class Fork:
    """The modules of one fork of the reference."""

    def __init__(self, name):
        base = "ethereum.forks." + name
        self.name = name
        self.vm = importlib.import_module(base + ".vm")
        self.interpreter = importlib.import_module(base + ".vm.interpreter")
        self.state = importlib.import_module(base + ".state")
        self.types = importlib.import_module(base + ".fork_types")
        self.fork = importlib.import_module(base + ".fork")
        self.gas = importlib.import_module(base + ".vm.gas")
        self.ops = importlib.import_module(base + ".vm.instructions")
        self.exceptions = importlib.import_module(base + ".vm.exceptions")
        self.blocks = importlib.import_module(base + ".blocks")


FORKS = {}


def fork_of(name):
    if name not in FORKS:
        FORKS[name] = Fork(name)
    return FORKS[name]


def build(cls, values):
    """An instance of a dataclass from the values it has fields for."""
    names = [f.name for f in dataclasses.fields(cls)]
    missing = [n for n in names if n not in values]
    if missing:
        raise KeyError(f"{cls.__name__} lacks {missing}")
    return cls(**{n: values[n] for n in names})


def parse_accounts(word):
    accounts = []
    if word == "-":
        return accounts
    for entry in word.split(";"):
        address, nonce, balance, code, storage = entry.split(",")
        slots = []
        if storage != "-":
            for slot in storage.split("&"):
                key, value = slot.split("=")
                slots.append((bytes.fromhex(key), int(value, 16)))
        accounts.append((bytes.fromhex(address), int(nonce), int(balance), unhex(code), slots))
    return accounts


def make_state(fork, accounts):
    state = fork.state.State()
    for address, nonce, balance, code, slots in accounts:
        account = fork.types.Account(Uint(nonce), U256(balance), code)
        fork.state.set_account(state, Bytes20(address), account)
        for key, value in slots:
            fork.state.set_storage(state, Bytes20(address), Bytes32(key), U256(value))
    return state


def make_message(fork, state, kind, static, gas, value, data, code):
    hashes = [Bytes32((i + 1).to_bytes(32, "big")) for i in range(256)]
    transient = getattr(fork.state, "TransientStorage", lambda: None)()
    block_env = build(
        fork.vm.BlockEnvironment,
        {
            "chain_id": U64(1),
            "state": state,
            "block_gas_limit": Uint(30_000_000),
            "block_hashes": hashes,
            "coinbase": Bytes20(COINBASE),
            "number": Uint(1000),
            "time": U256(1_700_000_000),
            "difficulty": Uint(0x20000),
            "base_fee_per_gas": Uint(7),
            "prev_randao": Bytes32(b"\x11" * 32),
            "excess_blob_gas": U64(10 * 2**17),
            "parent_beacon_block_root": Bytes32(b"\x22" * 32),
        },
    )
    tx_env = build(
        fork.vm.TransactionEnvironment,
        {
            "origin": Bytes20(CALLER),
            "gas_price": Uint(10),
            "gas": Uint(gas),
            "access_list_addresses": set(),
            "access_list_storage_keys": set(),
            "transient_storage": transient,
            "blob_versioned_hashes": tuple(Bytes32(h) for h in BLOB_HASHES),
            "authorizations": (),
            "index_in_block": Uint(0),
            "tx_hash": None,
            "traces": [],
        },
    )
    create = kind == "create"
    return build(
        fork.vm.Message,
        {
            "block_env": block_env,
            "tx_env": tx_env,
            "caller": Bytes20(CALLER),
            "target": Bytes0() if create else Bytes20(TARGET),
            "current_target": Bytes20(TARGET),
            "gas": Uint(gas),
            "value": U256(value),
            "data": data,
            "code_address": None if create else Bytes20(TARGET),
            "code": code,
            "depth": Uint(0),
            "should_transfer_value": True,
            "is_static": static,
            "accessed_addresses": {Bytes20(CALLER), Bytes20(TARGET)},
            "accessed_storage_keys": set(),
            "disable_precompiles": False,
            "parent_evm": None,
        },
    )


def status_of(fork, evm):
    if evm.error is None:
        return "ok"
    if isinstance(evm.error, getattr(fork.exceptions, "Revert", ())):
        return "revert"
    return "halt"


def show_logs(logs):
    return (
        ";".join(
            f"{tohex(log.address)},"
            f"{'.'.join(tohex(t) for t in log.topics) or '-'},{tohex(log.data)}"
            for log in logs
        )
        or "-"
    )


def show_state(state):
    out = []
    for address in sorted(state._main_trie._data):
        account = state._main_trie._data[address]
        if account is None:
            continue
        trie = state._storage_tries.get(address)
        slots = sorted(trie._data.items()) if trie else []
        storage = "&".join(f"{tohex(k)}={int(v):x}" for k, v in slots if int(v) != 0)
        out.append(
            f"{tohex(address)},{int(account.nonce)},{int(account.balance)},"
            f"{tohex(keccak256(account.code))},{storage or '-'}"
        )
    return ";".join(out) or "-"


def run(name, kind, static, gas, value, data, code, accounts):
    fork = fork_of(name)
    state = make_state(fork, parse_accounts(accounts))
    message = make_message(
        fork,
        state,
        kind,
        static == "1",
        int(gas),
        int(value),
        unhex(data),
        unhex(code),
    )
    if kind == "create":
        evm = fork.interpreter.process_create_message(message)
    else:
        evm = fork.interpreter.process_message(message)
    status = status_of(fork, evm)
    words = [status, str(int(evm.gas_left)), tohex(evm.output)]
    if status == "ok":
        words += [str(int(evm.refund_counter)), show_logs(evm.logs)]
        words.append(",".join(sorted(tohex(a) for a in evm.accounts_to_delete)) or "-")
        if hasattr(evm, "touched_accounts"):
            touched = sorted(tohex(a) for a in evm.touched_accounts)
            words.append(",".join(touched) or "-")
        else:
            words.append("n/a")
    else:
        words += ["0", "-", "-", "n/a"]
    words.append(show_state(state))
    transient = getattr(message.tx_env, "transient_storage", None)
    shown = []
    if transient is not None:
        for address, trie in transient._tries.items():
            for key, value in trie._data.items():
                if int(value) != 0:
                    shown.append(f"{tohex(address)}:{tohex(key)}={int(value):x}")
    words.append(",".join(sorted(shown)) or "-")
    error = type(evm.error).__name__ if evm.error else "-"
    return " ".join(words), error


class Frame:
    """A frame that runs one instruction at a time."""

    def __init__(self, name, gas, static):
        self.fork = fork_of(name)
        accounts = [
            (CALLER, 0, 10**18, b"", []),
            (TARGET, 1, 10**9, b"", [(b"\x00" * 31 + b"\x01", 1)]),
        ]
        state = make_state(self.fork, accounts)
        message = make_message(self.fork, state, "call", static, gas, 5, b"\xaa" * 40, b"")
        fields = {
            "pc": Uint(0),
            "stack": [],
            "memory": bytearray(),
            "code": b"",
            "gas_left": Uint(gas),
            "valid_jump_destinations": set(),
            "logs": (),
            "refund_counter": 0,
            "running": True,
            "message": message,
            "output": b"",
            "accounts_to_delete": set(),
            "touched_accounts": set(),
            "return_data": b"",
            "error": None,
            "accessed_addresses": message.__dict__.get("accessed_addresses", set()),
            "accessed_storage_keys": set(),
        }
        self.evm = build(self.fork.vm.Evm, fields)
        # The original value of a slot is read from the snapshot of the transaction.
        begin = self.fork.state.begin_transaction
        if hasattr(self.fork.state, "TransientStorage"):
            begin(state, message.tx_env.transient_storage)
        else:
            begin(state)

    def step(self, code):
        fork, evm = self.fork, self.evm
        evm.code = code
        evm.pc = Uint(0)
        jumpdests = importlib.import_module(
            "ethereum.forks." + fork.name + ".vm.runtime"
        ).get_valid_jump_destinations
        evm.valid_jump_destinations = jumpdests(code)
        before = (list(evm.stack), bytearray(evm.memory), evm.gas_left, evm.output)
        try:
            steps = 0
            while evm.running and int(evm.pc) < len(code) and steps < 100:
                steps += 1
                try:
                    op = fork.ops.Ops(code[int(evm.pc)])
                except ValueError:
                    raise fork.exceptions.InvalidOpcode(code[int(evm.pc)]) from None
                fork.ops.op_implementation[op](evm)
        except EthereumException as error:
            # The driver goes on from the frame before the failed code.
            evm.stack, evm.memory, evm.gas_left, evm.output = before
            evm.running = True
            revert = getattr(fork.exceptions, "Revert", ())
            kind = "revert" if isinstance(error, revert) else "halt"
            return f"{kind} {type(error).__name__}"
        running = evm.running
        evm.running = True
        return " ".join(
            [
                "ok",
                str(int(evm.gas_left)),
                str(int(evm.pc)),
                str(len(evm.memory)),
                tohex(keccak256(bytes(evm.memory))),
                ",".join(f"{int(x):x}" for x in reversed(evm.stack)) or "-",
                str(int(evm.refund_counter)),
                show_logs(evm.logs),
                "1" if running else "0",
                tohex(evm.output),
            ]
        )


FRAME = [None]


def precompile(name, address, gas, data):
    fork_of(name)
    mapping = importlib.import_module(
        "ethereum.forks." + name + ".vm.precompiled_contracts.mapping"
    ).PRE_COMPILED_CONTRACTS
    target = Bytes20(int(address).to_bytes(20, "big"))
    if target not in mapping:
        return "none"
    frame = Frame(name, int(gas), False)
    evm = frame.evm
    evm.message.data = unhex(data)
    try:
        mapping[target](evm)
    except EthereumException as error:
        return f"halt {type(error).__name__}"
    return f"ok {int(evm.gas_left)} {tohex(evm.output)}"


def header(fork, **fields):
    """A header with the given fields, and zero in the others."""
    cls = fork.blocks.Header
    values = {}
    for f in dataclasses.fields(cls):
        values[f.name] = fields.get(f.name, None)
    return cls(**values)


def base_fee(name, limit, used, fee):
    fork = fork_of(name)
    return str(
        int(
            fork.fork.calculate_base_fee_per_gas(
                Uint(int(limit)), Uint(int(limit)), Uint(int(used)), Uint(int(fee))
            )
        )
    )


def excess(name, parent_excess, used, fee):
    fork = fork_of(name)
    parent = header(
        fork,
        excess_blob_gas=U64(int(parent_excess)),
        blob_gas_used=U64(int(used)),
        base_fee_per_gas=Uint(int(fee)),
    )
    return str(int(fork.gas.calculate_excess_blob_gas(parent)))


def answer(words):
    match words:
        case ["run", *rest]:
            result, error = run(*rest)
            return result + "\t" + error
        case ["frame", name, gas, static]:
            FRAME[0] = Frame(name, int(gas), static == "1")
            return "ok"
        case ["op", code]:
            return FRAME[0].step(unhex(code))
        case ["mk", kind, a, b, c, mutation, cut]:
            return tohex(evm_inputs.make(kind, a, b, c, mutation, cut))
        case ["pre", name, address, gas, data]:
            return precompile(name, address, gas, data)
        case ["basefee", name, limit, used, fee]:
            return base_fee(name, limit, used, fee)
        case ["excess", name, parent_excess, used, fee]:
            return excess(name, parent_excess, used, fee)
        case ["jumpdests", name, code]:
            runtime = importlib.import_module("ethereum.forks." + name + ".vm.runtime")
            found = runtime.get_valid_jump_destinations(unhex(code))
            return ",".join(str(int(d)) for d in sorted(found)) or "-"
        case ["create", name, sender, nonce]:
            utils = importlib.import_module("ethereum.forks." + name + ".utils.address")
            return tohex(utils.compute_contract_address(Bytes20(unhex(sender)), Uint(int(nonce))))
        case ["create2", name, sender, salt, code]:
            utils = importlib.import_module("ethereum.forks." + name + ".utils.address")
            return tohex(
                utils.compute_create2_contract_address(
                    Bytes20(unhex(sender)), Bytes32(unhex(salt)), bytearray(unhex(code))
                )
            )
        case ["extend", name, size, *ranges]:
            gas = fork_of(name).gas
            pairs = [tuple(U256(int(n)) for n in r.split(":")) for r in ranges]
            result = gas.calculate_gas_extend_memory(bytearray(int(size)), pairs)
            return f"{int(result.cost)} {int(result.expand_by)}"
        case ["gaslimit", name, limit, parent]:
            check = fork_of(name).fork.check_gas_limit
            return "1" if check(Uint(int(limit)), Uint(int(parent))) else "0"
        case ["taylor", factor, numerator, denominator]:
            from ethereum.utils.numeric import taylor_exponential

            return str(
                int(
                    taylor_exponential(
                        Uint(int(factor)), Uint(int(numerator)), Uint(int(denominator))
                    )
                )
            )
        case ["blobfee", name, parent_excess]:
            fork = fork_of(name)
            return str(int(fork.gas.calculate_blob_gas_price(U64(int(parent_excess)))))
    return "error unknown command"


class Slow(BaseException):
    """The reference took too long on one command."""


SLOW_SECONDS = 10


def too_slow(signum, frame):
    raise Slow()


def main():
    sys.setrecursionlimit(20000)
    signal.signal(signal.SIGALRM, too_slow)
    for line in sys.stdin:
        words = line.rstrip("\n").split("\t")
        signal.alarm(SLOW_SECONDS)
        try:
            print(answer(words), flush=True)
        except Slow:
            print(f"slow {line[:300]}", file=sys.stderr, flush=True)
            print("crash slow", flush=True)
        except Exception as error:  # A crash of the reference is an answer.
            print(f"crash {type(error).__name__}: {error}".replace("\n", " "), flush=True)
        signal.alarm(0)


if __name__ == "__main__":
    main()

"""References for a whole transaction and a whole block: the Python execution-specs (EELS)."""

#     setup                               The addresses of the senders, joined with `,`.
#     tx <fork> <env> <accounts> <tx>     One transaction on a state: `process_transaction`.
#     block <fork> <chain> <accounts> <txs> <withdrawals> <ommers> <mutation>
#         Build a block over a chain and check it with `state_transition`.
#     open <fork> <chain> <accounts>      Start a chain that the next commands extend.
#     add <tx>                            One transaction in the open block.
#     seal <withdrawals>                  End the open block, check it whole, open the next.
#
# Bytes are in hexadecimal, `-` for none.
# An account is `address,nonce,balance,code,key=value&key=value`.
# Accounts are joined with `;`.
# An environment is eleven fields joined with `,`:
#     number,time,gas limit,base fee,coinbase,difficulty,randao,excess blob gas,beacon root,
#     gas used,blob gas used
# A chain is twelve fields joined with `,`:
#     number,gas limit,parent base fee,parent gas used,parent excess blob gas,
#     parent blob gas used,coinbase,randao,beacon root,recent blocks,extra data,seconds
# Transactions are those of `transition_txs.py`, joined with `;`.
# A withdrawal is `index:validator:address:amount`, and an ommer is `age:coinbase:fault`.
# Both are joined with `/`.

import dataclasses
import importlib
import inspect
import os
import signal
import sys
import traceback

# The interpreter runs isolated, so the directory of this file is not on the path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import transition_txs  # noqa: E402
from ethereum.crypto.hash import keccak256
from ethereum.exceptions import EthereumException
from ethereum_rlp import rlp
from ethereum_rlp.exceptions import RLPException
from ethereum_types.bytes import Bytes8, Bytes20, Bytes32, Bytes256
from ethereum_types.numeric import U64, U256, Uint

CHAIN_ID = 1
EMPTY_OMMERS = keccak256(rlp.encode([]))


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return bytes(data).hex() if data else "-"


class Fork:
    """The modules of one fork of the reference, with the hooks that the oracle needs."""

    def __init__(self, name):
        base = "ethereum.forks." + name
        self.name = name
        self.vm = importlib.import_module(base + ".vm")
        self.state = importlib.import_module(base + ".state")
        self.types = importlib.import_module(base + ".fork_types")
        self.fork = importlib.import_module(base + ".fork")
        self.blocks = importlib.import_module(base + ".blocks")
        self.tx = importlib.import_module(base + ".transactions")
        self.trie = importlib.import_module(base + ".trie")
        self.exceptions = importlib.import_module(base + ".vm.exceptions")
        # What the last message of a transaction left, and the index of the last transaction.
        self.last = None
        self.index = None
        # The seal of a header is another layer's, and no generated header has one.
        if hasattr(self.fork, "validate_proof_of_work"):
            self.fork.validate_proof_of_work = lambda header: None
        run_message = self.fork.process_message_call
        run_transaction = self.fork.process_transaction

        def message_call(message):
            self.last = run_message(message)
            return self.last

        def transaction(block_env, block_output, tx, index):
            self.index = int(index)
            return run_transaction(block_env, block_output, tx, index)

        self.fork.process_message_call = message_call
        self.fork.process_transaction = transaction


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


def make_state(fork, word):
    state = fork.state.State()
    if word == "-":
        return state
    for entry in word.split(";"):
        address, nonce, balance, code, storage = entry.split(",")
        account = fork.types.Account(Uint(int(nonce)), U256(int(balance)), unhex(code))
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


def copy_state(fork, state):
    """A state that later writes to the first leave alone: the accounts are frozen values."""
    copy_trie = fork.trie.copy_trie
    made = fork.state.State()
    made._main_trie = copy_trie(state._main_trie)
    made._storage_tries = {k: copy_trie(t) for k, t in state._storage_tries.items()}
    if hasattr(state, "created_accounts"):
        made.created_accounts = set(state.created_accounts)
    return made


def copy_chain(fork, chain):
    return fork.fork.BlockChain(
        blocks=list(chain.blocks), state=copy_state(fork, chain.state), chain_id=chain.chain_id
    )


def copy_output(fork, output):
    """The output of a block so far, with its tries and lists copied."""
    made = fork.vm.BlockOutput()
    for field in dataclasses.fields(output):
        value = getattr(output, field.name)
        if isinstance(value, fork.trie.Trie):
            value = fork.trie.copy_trie(value)
        elif isinstance(value, list):
            value = list(value)
        setattr(made, field.name, value)
    return made


class RefusedError(Exception):
    """A transaction or a block that the reference cannot read at the fork."""


def decode_tx(fork, raw):
    """The transaction of some bytes at a fork, as `process_transaction` takes it."""
    legacy = getattr(fork.tx, "LegacyTransaction", None) or fork.tx.Transaction
    try:
        if raw[0] >= 0xC0:
            return rlp.decode_to(legacy, raw)
        if not hasattr(fork.tx, "decode_transaction"):
            raise RefusedError("typed transaction")
        tx = fork.tx.decode_transaction(raw)
    except (EthereumException, RLPException) as error:
        raise RefusedError(type(error).__name__) from None
    # EIP-2930 asks that a typed transaction names the chain, which `recover_sender` leaves out.
    if int(tx.chain_id) != CHAIN_ID:
        raise RefusedError("chain")
    return tx


def outcome_of(fork):
    """How the message of the last transaction ended: ok, revert, oog or halt, and its error."""
    error = fork.last.error
    if error is None:
        return "ok -"
    name = type(error).__name__
    if isinstance(error, getattr(fork.exceptions, "Revert", ())):
        return "revert " + name
    if isinstance(error, fork.exceptions.OutOfGasError):
        return "oog " + name
    return "halt " + name


def run_tx(fork, env, output, raw, index):
    """Run a transaction, and say what it left: the verdict, then the fields of a valid one."""
    saved = copy_output(fork, output)
    try:
        tx = decode_tx(fork, raw)
        fork.fork.process_transaction(env, output, tx, Uint(index))
    except (RefusedError, EthereumException) as error:
        # A refused transaction leaves the block as it was.
        for field in dataclasses.fields(output):
            setattr(output, field.name, getattr(saved, field.name))
        reason = str(error) if isinstance(error, RefusedError) else type(error).__name__
        return ["invalid " + reason, "-", "-", "-", "-", show_state(env.state)]
    receipt = output.receipts_trie._data[rlp.encode(Uint(index))]
    receipt = receipt if isinstance(receipt, bytes) else rlp.encode(receipt)
    return [
        "valid",
        outcome_of(fork),
        str(int(output.block_gas_used)),
        str(int(getattr(output, "blob_gas_used", 0))),
        tohex(receipt),
        show_state(env.state),
    ]


def block_env(fork, state, hashes, fields):
    return build(
        fork.vm.BlockEnvironment,
        {"chain_id": U64(CHAIN_ID), "state": state, "block_hashes": hashes, **fields},
    )


def one_tx(name, env, accounts, spec):
    fork = fork_of(name)
    state = make_state(fork, accounts)
    number, time, limit, base_fee, coinbase, difficulty, randao, excess, beacon, used, blob = (
        env.split(",")
    )
    hashes = [Bytes32((i + 1).to_bytes(32, "big")) for i in range(256)]
    fields = {
        "block_gas_limit": Uint(int(limit)),
        "coinbase": Bytes20(bytes.fromhex(coinbase)),
        "number": Uint(int(number)),
        "time": U256(int(time)),
        "difficulty": Uint(int(difficulty)),
        "base_fee_per_gas": Uint(int(base_fee)),
        "prev_randao": Bytes32(bytes.fromhex(randao)),
        "excess_blob_gas": U64(int(excess)),
        "parent_beacon_block_root": Bytes32(bytes.fromhex(beacon)),
    }
    output = fork.vm.BlockOutput()
    output.block_gas_used = Uint(int(used))
    if hasattr(output, "blob_gas_used"):
        output.blob_gas_used = U64(int(blob))
    raw = transition_txs.make(spec)
    return [tohex(raw)] + run_tx(fork, block_env(fork, state, hashes, fields), output, raw, 0)


# The chain and its blocks.


def header_of(fork, values):
    """A header of a fork from the fields it has, with empty roots where none is given."""
    zero = Bytes32(b"\x00" * 32)
    defaults = {
        "ommers_hash": EMPTY_OMMERS,
        "state_root": zero,
        "transactions_root": zero,
        "receipt_root": zero,
        "bloom": Bytes256(b"\x00" * 256),
        "gas_used": Uint(0),
        "extra_data": b"",
        "nonce": Bytes8(b"\x00" * 8),
        "withdrawals_root": zero,
        "blob_gas_used": U64(0),
        "requests_hash": zero,
    }
    values = {**defaults, **values}
    values["mix_digest"] = values["prev_randao"]
    return build(fork.blocks.Header, values)


def difficulty_after(fork, number, time, parent):
    """The difficulty that a parent gives, or 0 from Paris."""
    rule = getattr(fork.fork, "calculate_block_difficulty", None)
    if rule is None:
        return Uint(0)
    args = [Uint(number), U256(time), parent.timestamp, parent.difficulty]
    if len(inspect.signature(rule).parameters) == 5:
        args.append(parent.ommers_hash != EMPTY_OMMERS)
    return rule(*args)


def child_fields(fork, parent, limit, time):
    """The fields that a parent decides for a header after it."""
    fields = {
        "parent_hash": keccak256(rlp.encode(parent)),
        "number": parent.number + Uint(1),
        "gas_limit": Uint(limit),
        "timestamp": U256(time),
        "difficulty": difficulty_after(fork, int(parent.number) + 1, time, parent),
    }
    if hasattr(parent, "base_fee_per_gas"):
        fields["base_fee_per_gas"] = fork.fork.calculate_base_fee_per_gas(
            Uint(limit), parent.gas_limit, parent.gas_used, parent.base_fee_per_gas
        )
    if hasattr(parent, "excess_blob_gas"):
        fields["excess_blob_gas"] = fork.vm.gas.calculate_excess_blob_gas(parent)
    return fields


class Chain:
    """A chain of the reference, and the block that is open on it."""

    def __init__(self, name, word, accounts):
        fork = fork_of(name)
        self.fork = fork
        (
            number,
            limit,
            base_fee,
            parent_used,
            parent_excess,
            parent_blob,
            coinbase,
            randao,
            beacon,
            recent,
            extra,
            seconds,
        ) = word.split(",")
        number, self.limit, recent = int(number), int(limit), int(recent)
        self.seconds = int(seconds)
        self.common = {
            "coinbase": Bytes20(bytes.fromhex(coinbase)),
            "prev_randao": Bytes32(bytes.fromhex(randao)),
            "parent_beacon_block_root": Bytes32(bytes.fromhex(beacon)),
            "extra_data": unhex(extra),
        }
        # The oldest recent block has no parent to follow.
        first = {
            "parent_hash": Bytes32(b"\x77" * 32),
            "number": Uint(number - recent),
            "gas_limit": Uint(self.limit),
            "gas_used": Uint(self.limit // 2),
            "timestamp": U256(1_000_000),
            "difficulty": Uint(131072 if hasattr(fork.fork, "pay_rewards") else 0),
            "base_fee_per_gas": Uint(int(base_fee)),
            "excess_blob_gas": U64(0),
            "extra_data": b"",
        }
        headers = [header_of(fork, {**self.common, **first})]
        for _ in range(recent - 1):
            parent = headers[-1]
            fields = child_fields(fork, parent, self.limit, int(parent.timestamp) + 13)
            fields["gas_used"] = Uint(self.limit // 2)
            headers.append(header_of(fork, {**self.common, **fields, "extra_data": b""}))
        # The parent of the block: its gas used and its blob gas decide the fees of the block.
        last = dataclasses.asdict(headers[-1])
        last["prev_randao"] = self.common["prev_randao"]
        last["gas_used"] = Uint(int(parent_used))
        last["excess_blob_gas"] = U64(int(parent_excess))
        last["blob_gas_used"] = U64(int(parent_blob))
        headers[-1] = header_of(fork, last)
        blocks = [self.block_of(h, (), (), ()) for h in headers]
        self.chain = fork.fork.BlockChain(
            blocks=blocks, state=make_state(fork, accounts), chain_id=U64(CHAIN_ID)
        )
        self.open_block()

    def block_of(self, header, transactions, ommers, withdrawals):
        values = {
            "header": header,
            "transactions": transactions,
            "ommers": ommers,
            "withdrawals": withdrawals,
        }
        return build(self.fork.blocks.Block, values)

    def template(self):
        """The header of the next block, before its body gives the roots."""
        parent = self.chain.blocks[-1].header
        time = int(parent.timestamp) + self.seconds
        return header_of(
            self.fork, {**self.common, **child_fields(self.fork, parent, self.limit, time)}
        )

    def environment(self, chain, header):
        """The environment of a block on a chain, as `state_transition` builds it."""
        fields = {
            "block_gas_limit": header.gas_limit,
            "coinbase": header.coinbase,
            "number": header.number,
            "time": header.timestamp,
            "difficulty": header.difficulty,
            "base_fee_per_gas": getattr(header, "base_fee_per_gas", None),
            "prev_randao": getattr(header, "prev_randao", None),
            "excess_blob_gas": getattr(header, "excess_blob_gas", None),
            "parent_beacon_block_root": getattr(header, "parent_beacon_block_root", None),
        }
        hashes = self.fork.fork.get_last_256_block_hashes(chain)
        return block_env(self.fork, chain.state, hashes, fields)

    def open_block(self):
        """Open the next block: a copy of the chain runs its transactions one by one."""
        fork = self.fork.fork
        self.raws = []
        self.working = copy_chain(self.fork, self.chain)
        if self.fork.name == "dao_fork" and int(self.template().number) == 1920000:
            fork.apply_fork(self.working)
        self.env = self.environment(self.working, self.template())
        self.output = self.fork.vm.BlockOutput()
        # The system calls at the start of a block, as `apply_body` makes them.
        if hasattr(fork, "BEACON_ROOTS_ADDRESS"):
            fork.process_unchecked_system_transaction(
                block_env=self.env,
                target_address=fork.BEACON_ROOTS_ADDRESS,
                data=self.env.parent_beacon_block_root,
            )
        if hasattr(fork, "HISTORY_STORAGE_ADDRESS"):
            fork.process_unchecked_system_transaction(
                block_env=self.env,
                target_address=fork.HISTORY_STORAGE_ADDRESS,
                data=self.env.block_hashes[-1],
            )

    def add(self, spec):
        raw = transition_txs.make(spec)
        result = run_tx(self.fork, self.env, self.output, raw, len(self.raws))
        if result[0] == "valid":
            self.raws.append(raw)
        return [tohex(raw)] + result

    def ommers(self, word):
        """The ommers of a specification: siblings of recent blocks, each valid unless asked."""
        made = []
        if word == "-":
            return ()
        blocks = self.chain.blocks
        for entry in word.split("/"):
            age, coinbase, fault = entry.split(":")
            age, fault = int(age), int(fault)
            if fault == 1:
                # A block of the chain is no ommer.
                made.append(blocks[-age].header)
                continue
            parent = blocks[-age - 1].header
            fields = child_fields(self.fork, parent, self.limit, int(parent.timestamp) + 7)
            fields["coinbase"] = Bytes20(bytes.fromhex(coinbase))
            if fault == 2:
                fields["difficulty"] = fields["difficulty"] + Uint(1)
            made.append(header_of(self.fork, {**self.common, **fields, "extra_data": b"ommer"}))
        return tuple(made)

    def withdrawals(self, word):
        if word == "-" or not hasattr(self.fork.blocks, "Withdrawal"):
            return ()
        made = []
        for entry in word.split("/"):
            index, validator, address, amount = entry.split(":")
            made.append(
                self.fork.blocks.Withdrawal(
                    index=U64(int(index)),
                    validator_index=U64(int(validator)),
                    address=Bytes20(bytes.fromhex(address)),
                    amount=U256(int(amount)),
                )
            )
        return tuple(made)

    def encode(self, header, raws, ommers, withdrawals):
        """The bytes of a block: a typed transaction is a byte string, a legacy one a list."""
        items = [rlp.decode(raw) if raw[0] >= 0xC0 else raw for raw in raws]
        parts = [header, items, list(ommers)]
        if hasattr(header, "withdrawals_root"):
            parts.append(list(withdrawals))
        return rlp.encode(parts)

    def body(self, chain, block):
        """Run the body of a block on a chain, and give the header that it decides."""
        fork = self.fork.fork
        if self.fork.name == "dao_fork" and int(block.header.number) == 1920000:
            fork.apply_fork(chain)
        env = self.environment(chain, block.header)
        arguments = {"block_env": env, "transactions": block.transactions}
        wanted = inspect.signature(fork.apply_body).parameters
        if "ommers" in wanted:
            arguments["ommers"] = block.ommers
        if "withdrawals" in wanted:
            arguments["withdrawals"] = block.withdrawals
        out = fork.apply_body(**arguments)
        fields = dataclasses.asdict(block.header)
        fields["prev_randao"] = fields.get("prev_randao", fields.get("mix_digest"))
        fields["gas_used"] = out.block_gas_used
        fields["state_root"] = self.fork.state.state_root(chain.state)
        fields["transactions_root"] = self.fork.trie.root(out.transactions_trie)
        fields["receipt_root"] = self.fork.trie.root(out.receipts_trie)
        fields["bloom"] = fork.logs_bloom(out.block_logs)
        if hasattr(out, "withdrawals_trie"):
            fields["withdrawals_root"] = self.fork.trie.root(out.withdrawals_trie)
        if hasattr(out, "blob_gas_used"):
            fields["blob_gas_used"] = out.blob_gas_used
        if hasattr(out, "requests"):
            fields["requests_hash"] = fork.compute_requests_hash(out.requests)
        return header_of(self.fork, fields)

    def seal(self, raws, withdrawals, ommers, mutation):
        """Build a block from its parts and check it whole.

        It gives the verdict, the bytes of the block and the state after a valid block.
        """
        ommers = self.ommers(ommers)
        withdrawals = self.withdrawals(withdrawals)
        template = dataclasses.asdict(self.template())
        template["prev_randao"] = self.common["prev_randao"]
        # From Paris the hash is that of no ommers, so that only the rule on the body refuses them.
        if hasattr(self.fork.fork, "validate_ommers"):
            template["ommers_hash"] = keccak256(rlp.encode(list(ommers)))
        header = header_of(self.fork, template)
        encoded = self.encode(header, raws, ommers, withdrawals)
        try:
            block = rlp.decode_to(self.fork.blocks.Block, encoded)
            for raw in raws:
                decode_tx(self.fork, raw)
        except (RefusedError, EthereumException, RLPException):
            return ["invalid decode -", tohex(encoded), "-"]
        self.fork.index = None
        try:
            # The reference checks the header and the ommers before the body.
            self.fork.fork.validate_header(self.chain, block.header)
            if hasattr(self.fork.fork, "validate_ommers"):
                self.fork.fork.validate_ommers(block.ommers, block.header, self.chain)
            elif block.ommers:
                return ["invalid ommers InvalidBlock", tohex(encoded), "-"]
            header = self.body(copy_chain(self.fork, self.chain), block)
        except EthereumException as error:
            return [f"invalid {kind_of(self.fork, error)}", tohex(encoded), "-"]
        header = mutate(header, mutation)
        encoded = self.encode(header, raws, ommers, withdrawals)
        block = rlp.decode_to(self.fork.blocks.Block, encoded)
        after = copy_chain(self.fork, self.chain)
        if self.fork.name == "dao_fork" and int(block.header.number) == 1920000:
            self.fork.fork.apply_fork(after)
        try:
            self.fork.fork.state_transition(after, block)
        except EthereumException as error:
            names = [frame.name for frame in traceback.extract_tb(error.__traceback__)]
            where = "header" if "validate_header" in names else "output"
            return [f"invalid {where} {mutation}", tohex(encoded), "-"]
        self.chain = after
        return ["valid", tohex(encoded), show_state(after.state)]


def kind_of(fork, error):
    """Where the body of a block failed, and the name of the error."""
    names = [frame.name for frame in traceback.extract_tb(error.__traceback__)]
    name = type(error).__name__
    if "process_transaction" in names or "transaction" in names:
        return f"tx:{fork.index} {name}"
    for function, kind in [
        ("parse_deposit_requests", "deposit"),
        ("process_checked_system_transaction", "system"),
        ("validate_ommers", "ommers"),
        ("validate_header", "header"),
    ]:
        if function in names:
            return f"{kind} {name}"
    return f"other {name}"


def mutate(header, mutation):
    """A header with one of the fields that the body decides changed, if the fork has it."""
    names = {
        "gas": "gas_used",
        "state": "state_root",
        "transactions": "transactions_root",
        "receipts": "receipt_root",
        "bloom": "bloom",
        "withdrawals": "withdrawals_root",
        "blobgas": "blob_gas_used",
        "requests": "requests_hash",
    }
    name = names.get(mutation)
    if name is None or not hasattr(header, name):
        return header
    value = getattr(header, name)
    if isinstance(value, (Uint, U64)):
        changed = type(value)(int(value) + 1)
    else:
        changed = type(value)(bytes([value[0] ^ 1]) + bytes(value[1:]))
    return dataclasses.replace(header, **{name: changed})


def recent_of(chain):
    return ".".join(tohex(rlp.encode(block.header)) for block in chain.chain.blocks)


OPEN = [None]


def answer(words):
    match words:
        case ["setup"]:
            return ",".join(tohex(transition_txs.address_of(i)) for i in range(8))
        case ["tx", name, env, accounts, spec]:
            return "\t".join(one_tx(name, env, accounts, spec))
        case ["block", name, word, accounts, specs, withdrawals, ommers, mutation]:
            chain = Chain(name, word, accounts)
            recent = recent_of(chain)
            raws = [transition_txs.make(spec) for spec in specs.split(";")] if specs != "-" else []
            return "\t".join([recent] + chain.seal(raws, withdrawals, ommers, mutation))
        case ["open", name, word, accounts]:
            OPEN[0] = Chain(name, word, accounts)
            return recent_of(OPEN[0]) + "\t" + tohex(rlp.encode(OPEN[0].template()))
        case ["add", spec]:
            return "\t".join(OPEN[0].add(spec))
        case ["seal", withdrawals]:
            chain = OPEN[0]
            result = chain.seal(chain.raws, withdrawals, "-", "-")
            chain.open_block()
            return "\t".join(result + [tohex(rlp.encode(chain.template()))])
    return "error unknown command"


class Slow(BaseException):
    """The reference took too long on one command."""


SLOW_SECONDS = 20


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
            where = traceback.extract_tb(error.__traceback__)[-1]
            print(
                f"crash {type(error).__name__}: {error} at {where.name}:{where.lineno}".replace(
                    "\n", " "
                ),
                flush=True,
            )
        signal.alarm(0)


if __name__ == "__main__":
    main()

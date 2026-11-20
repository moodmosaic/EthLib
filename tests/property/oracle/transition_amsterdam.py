"""References for a transaction and a block at Glamsterdam: the branch `forks/amsterdam` of EELS."""

# No release has this fork, so the branch is installed apart from the released package.
# `requirements-evm.txt` names its revision, and `ETHLIB_AMSTERDAM_SPECS` another directory.
#
#     setup                               The addresses of the senders, joined with `,`.
#     tx <fork> <env> <accounts> <tx>     One transaction on a state: `process_transaction`.
#     block <fork> <chain> <accounts> <txs> <withdrawals> <ommers> <mutation>
#         Build a block over a chain and check it with `execute_block`.
#
# The words are those of `transition.py`, and the name of the fork is not read.

import dataclasses
import os
import signal
import sys
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
SPECS = os.environ.get("ETHLIB_AMSTERDAM_SPECS", os.path.join(HERE, "..", ".venv", "evm-amsterdam"))
sys.path.insert(0, SPECS)
# The interpreter runs isolated, so the directory of this file is not on the path.
sys.path.insert(0, HERE)

import transition_txs  # noqa: E402
from ethereum import state_mpt  # noqa: E402
from ethereum.crypto.hash import keccak256  # noqa: E402
from ethereum.exceptions import EthereumException  # noqa: E402
from ethereum.forks.amsterdam import (  # noqa: E402
    blocks,
    fork as spec,  # noqa: E402
    transactions as txs,  # noqa: E402
    vm,
)
from ethereum.forks.amsterdam.block_access_lists import (  # noqa: E402
    BlockAccessListBuilder,
    hash_block_access_list,
)
from ethereum.forks.amsterdam.state_tracker import BlockState, extract_block_diff  # noqa: E402
from ethereum.forks.amsterdam.vm.exceptions import OutOfGasError, Revert  # noqa: E402
from ethereum.forks.amsterdam.vm.gas import calculate_excess_blob_gas  # noqa: E402
from ethereum.merkle_patricia_trie import copy_trie, root  # noqa: E402
from ethereum.state import Account  # noqa: E402
from ethereum_rlp import rlp  # noqa: E402
from ethereum_rlp.exceptions import RLPException  # noqa: E402
from ethereum_types.bytes import Bytes8, Bytes20, Bytes32, Bytes256  # noqa: E402
from ethereum_types.numeric import U64, U256, Uint  # noqa: E402

CHAIN_ID = 1
EMPTY_OMMERS = keccak256(rlp.encode([]))

# What the last message of a transaction left, and the index of the last transaction.
LAST = [None]
INDEX = [None]
run_top_level = spec.process_top_level
run_transaction = spec.process_transaction


def top_level(block_env, tx_env):
    LAST[0] = run_top_level(block_env, tx_env)
    return LAST[0]


def transaction(block_env, block_output, tx, index):
    INDEX[0] = int(index)
    return run_transaction(block_env, block_output, tx, index)


spec.process_top_level = top_level
spec.process_transaction = transaction


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return bytes(data).hex() if data else "-"


def make_state(word):
    state = state_mpt.State()
    if word == "-":
        return state
    for entry in word.split(";"):
        address, nonce, balance, code, storage = entry.split(",")
        address = Bytes20(bytes.fromhex(address))
        code_hash = state_mpt.store_code(state, unhex(code))
        account = Account(Uint(int(nonce)), U256(int(balance)), code_hash)
        state_mpt.set_account(state, address, account)
        if storage != "-":
            for slot in storage.split("&"):
                key, value = slot.split("=")
                state_mpt.set_storage(
                    state, address, Bytes32(bytes.fromhex(key)), U256(int(value, 16))
                )
    return state


def copy_state(state):
    made = state_mpt.State()
    made._main_trie = copy_trie(state._main_trie)
    made._storage_tries = {k: copy_trie(t) for k, t in state._storage_tries.items()}
    made._code_store = dict(state._code_store)
    return made


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
            f"{tohex(account.code_hash)},{storage or '-'}"
        )
    return ";".join(out) or "-"


def show_after(state, block_state):
    """The accounts of a state with the writes of a block so far."""
    after = copy_state(state)
    state_mpt.apply_changes_to_state(after, extract_block_diff(block_state))
    return show_state(after)


class RefusedError(Exception):
    """A transaction that the reference cannot read."""


def decode_tx(raw):
    try:
        if raw[0] >= 0xC0:
            return rlp.decode_to(txs.LegacyTransaction, raw)
        return txs.decode_transaction(raw)
    except (EthereumException, RLPException) as error:
        raise RefusedError(type(error).__name__) from None


def outcome():
    error = LAST[0].error
    if error is None:
        return "ok -"
    name = type(error).__name__
    if isinstance(error, Revert):
        return "revert " + name
    if isinstance(error, OutOfGasError):
        return "oog " + name
    return "halt " + name


def environment(block_state, hashes, fields):
    return vm.BlockEnvironment(
        chain_id=U64(CHAIN_ID),
        state=block_state,
        block_hashes=hashes,
        block_access_list_builder=BlockAccessListBuilder(),
        **fields,
    )


def one_tx(env, accounts, tx_spec):
    state = make_state(accounts)
    number, time, limit, base_fee, coinbase, _, randao, excess, beacon, used, blob = env.split(",")
    hashes = [Bytes32((i + 1).to_bytes(32, "big")) for i in range(256)]
    fields = {
        "block_gas_limit": Uint(int(limit)),
        "coinbase": Bytes20(bytes.fromhex(coinbase)),
        "number": Uint(int(number)),
        "time": U256(int(time)),
        "base_fee_per_gas": Uint(int(base_fee)),
        "prev_randao": Bytes32(bytes.fromhex(randao)),
        "excess_blob_gas": U64(int(excess)),
        "parent_beacon_block_root": Bytes32(bytes.fromhex(beacon)),
        "slot_number": U64(0),
    }
    block_state = BlockState(pre_state=state)
    block_env = environment(block_state, hashes, fields)
    output = vm.BlockOutput()
    output.block_gas_used = type(output.block_gas_used)(Uint(int(used)))
    output.cumulative_gas_used = Uint(int(used))
    output.blob_gas_used = U64(int(blob))
    raw = transition_txs.make(tx_spec)
    try:
        spec.process_transaction(block_env, output, decode_tx(raw), Uint(0))
    except (RefusedError, EthereumException) as error:
        reason = str(error) if isinstance(error, RefusedError) else type(error).__name__
        return [tohex(raw), "invalid " + reason, "-", "-", "-", "-", show_state(state)]
    receipt = output.receipts_trie._data[rlp.encode(Uint(0))]
    receipt = receipt if isinstance(receipt, bytes) else rlp.encode(receipt)
    return [
        tohex(raw),
        "valid",
        outcome(),
        f"{int(output.block_gas_used)}/{int(output.block_state_gas_used)}",
        str(int(output.blob_gas_used)),
        tohex(receipt),
        show_after(state, block_state),
    ]


def header_of(values):
    zero = Bytes32(b"\x00" * 32)
    defaults = {
        "ommers_hash": EMPTY_OMMERS,
        "state_root": zero,
        "transactions_root": zero,
        "receipt_root": zero,
        "bloom": Bytes256(b"\x00" * 256),
        "difficulty": Uint(0),
        "gas_used": Uint(0),
        "extra_data": b"",
        "nonce": Bytes8(b"\x00" * 8),
        "withdrawals_root": zero,
        "blob_gas_used": U64(0),
        "requests_hash": zero,
        "block_access_list_hash": zero,
    }
    values = {**defaults, **values}
    names = [f.name for f in dataclasses.fields(blocks.Header)]
    return blocks.Header(**{n: values[n] for n in names})


def child_fields(parent, limit, time):
    return {
        "parent_hash": keccak256(rlp.encode(parent)),
        "number": parent.number + Uint(1),
        "gas_limit": Uint(limit),
        "timestamp": U256(time),
        "base_fee_per_gas": spec.calculate_base_fee_per_gas(
            Uint(limit), parent.gas_limit, parent.gas_used, parent.base_fee_per_gas
        ),
        "excess_blob_gas": calculate_excess_blob_gas(parent),
        "slot_number": parent.slot_number + U64(1),
    }


def encode(header, raws, withdrawals):
    items = [rlp.decode(raw) if raw[0] >= 0xC0 else raw for raw in raws]
    return rlp.encode([header, items, [], list(withdrawals)])


def kind_of(error):
    names = [frame.name for frame in traceback.extract_tb(error.__traceback__)]
    name = type(error).__name__
    if "transaction" in names:
        return f"tx:{INDEX[0]} {name}"
    for function, kind in [
        ("parse_deposit_requests", "deposit"),
        ("process_checked_system_transaction", "system"),
        ("validate_block_access_list_gas_limit", "accesslist"),
        ("validate_header", "header"),
    ]:
        if function in names:
            return f"{kind} {name}"
    return f"other {name}"


MUTATIONS = {
    "gas": "gas_used",
    "state": "state_root",
    "transactions": "transactions_root",
    "receipts": "receipt_root",
    "bloom": "bloom",
    "withdrawals": "withdrawals_root",
    "blobgas": "blob_gas_used",
    "requests": "requests_hash",
    "accesslist": "block_access_list_hash",
}


def mutate(header, mutation):
    name = MUTATIONS.get(mutation)
    if name is None:
        return header
    value = getattr(header, name)
    if isinstance(value, (Uint, U64)):
        changed = type(value)(int(value) + 1)
    else:
        changed = type(value)(bytes([value[0] ^ 1]) + bytes(value[1:]))
    return dataclasses.replace(header, **{name: changed})


def one_block(word, accounts, tx_specs, withdrawal_specs, mutation):
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
    number, limit, recent = int(number), int(limit), int(recent)
    common = {
        "coinbase": Bytes20(bytes.fromhex(coinbase)),
        "prev_randao": Bytes32(bytes.fromhex(randao)),
        "parent_beacon_block_root": Bytes32(bytes.fromhex(beacon)),
    }
    first = {
        "parent_hash": Bytes32(b"\x77" * 32),
        "number": Uint(number - recent),
        "gas_limit": Uint(limit),
        "gas_used": Uint(limit // 2),
        "timestamp": U256(1_000_000),
        "base_fee_per_gas": Uint(int(base_fee)),
        "excess_blob_gas": U64(0),
        "slot_number": U64(number - recent),
    }
    headers = [header_of({**common, **first})]
    for _ in range(recent - 1):
        parent = headers[-1]
        fields = child_fields(parent, limit, int(parent.timestamp) + 13)
        headers.append(header_of({**common, **fields, "gas_used": Uint(limit // 2)}))
    headers[-1] = dataclasses.replace(
        headers[-1],
        gas_used=Uint(int(parent_used)),
        excess_blob_gas=U64(int(parent_excess)),
        blob_gas_used=U64(int(parent_blob)),
    )
    state = make_state(accounts)
    chain = spec.BlockChain(
        blocks=[
            blocks.Block(header=h, transactions=(), ommers=(), withdrawals=()) for h in headers
        ],
        state=state,
        chain_id=U64(CHAIN_ID),
    )
    recent_word = ".".join(tohex(rlp.encode(h)) for h in headers)
    parent = headers[-1]
    template = header_of(
        {
            **common,
            **child_fields(parent, limit, int(parent.timestamp) + int(seconds)),
            "extra_data": unhex(extra),
        }
    )
    raws = [transition_txs.make(s) for s in tx_specs.split(";")] if tx_specs != "-" else []
    withdrawals = []
    if withdrawal_specs != "-":
        for entry in withdrawal_specs.split("/"):
            index, validator, address, amount = entry.split(":")
            withdrawals.append(
                blocks.Withdrawal(
                    index=U64(int(index)),
                    validator_index=U64(int(validator)),
                    address=Bytes20(bytes.fromhex(address)),
                    amount=U256(int(amount)),
                )
            )
    encoded = encode(template, raws, withdrawals)
    try:
        block = rlp.decode_to(blocks.Block, encoded)
        for raw in raws:
            decode_tx(raw)
    except (RefusedError, EthereumException, RLPException):
        return [recent_word, "invalid decode -", tohex(encoded), "-"]
    context = spec.ChainContext(
        chain_id=chain.chain_id,
        block_hashes=spec.get_last_256_block_hashes(chain),
        parent_header=parent,
    )
    INDEX[0] = None
    try:
        # The body gives the header, as `execute_block` runs it.
        spec.validate_header(parent, block.header)
        block_state = BlockState(pre_state=state)
        header = block.header
        fields = {
            "block_gas_limit": header.gas_limit,
            "coinbase": header.coinbase,
            "number": header.number,
            "base_fee_per_gas": header.base_fee_per_gas,
            "time": header.timestamp,
            "prev_randao": header.prev_randao,
            "excess_blob_gas": header.excess_blob_gas,
            "parent_beacon_block_root": header.parent_beacon_block_root,
            "slot_number": header.slot_number,
        }
        out = spec.apply_body(
            block_env=environment(block_state, context.block_hashes, fields),
            transactions=block.transactions,
            withdrawals=block.withdrawals,
        )
    except EthereumException as error:
        return [recent_word, f"invalid {kind_of(error)}", tohex(encoded), "-"]
    diff = extract_block_diff(block_state)
    header = dataclasses.replace(
        template,
        gas_used=Uint(max(int(out.block_gas_used), int(out.block_state_gas_used))),
        state_root=state.compute_state_root(diff),
        transactions_root=root(out.transactions_trie),
        receipt_root=root(out.receipts_trie),
        bloom=spec.logs_bloom(out.block_logs),
        withdrawals_root=root(out.withdrawals_trie),
        blob_gas_used=out.blob_gas_used,
        requests_hash=spec.compute_requests_hash(out.requests),
        block_access_list_hash=hash_block_access_list(out.block_access_list),
    )
    encoded = encode(mutate(header, mutation), raws, withdrawals)
    block = rlp.decode_to(blocks.Block, encoded)
    try:
        diff = spec.execute_block(block, state, context)
    except EthereumException as error:
        names = [frame.name for frame in traceback.extract_tb(error.__traceback__)]
        where = "header" if "validate_header" in names else "output"
        return [recent_word, f"invalid {where} {mutation}", tohex(encoded), "-"]
    state_mpt.apply_changes_to_state(state, diff)
    return [recent_word, "valid", tohex(encoded), show_state(state)]


def answer(words):
    match words:
        case ["setup"]:
            return ",".join(tohex(transition_txs.address_of(i)) for i in range(8))
        case ["tx", _, env, accounts, tx_spec]:
            return "\t".join(one_tx(env, accounts, tx_spec))
        case ["block", _, word, accounts, tx_specs, withdrawals, _, mutation]:
            return "\t".join(one_block(word, accounts, tx_specs, withdrawals, mutation))
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

"""The reference of the EVM at Glamsterdam: the branch `forks/amsterdam` of EELS."""

# No release has this fork, so the branch is installed apart from the released
# package, at the commit that `requirements-evm.txt` names:
#
#     .venv/bin/pip install --no-deps --target .venv/evm-amsterdam         git+https://github.com/ethereum/execution-specs@<commit>
#
# `ETHLIB_AMSTERDAM_SPECS` names another directory.  One command per line:
#
#     run <static> <gas> <reservoir> <value> <data> <code> <accounts>
#     reads <the same>     Only the accounts that the frame read.
#
# It runs `process_call` on a frame from the caller to the target, and prints
# what the frame left, in the form of `oracle/evm.py` with the state gas left
# after the gas left.

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SPECS = os.environ.get("ETHLIB_AMSTERDAM_SPECS", os.path.join(HERE, "..", ".venv", "evm-amsterdam"))
sys.path.insert(0, SPECS)

from ethereum.crypto.hash import keccak256  # noqa: E402
from ethereum.forks.amsterdam import state_tracker  # noqa: E402
from ethereum.forks.amsterdam.block_access_lists import (  # noqa: E402
    BlockAccessListBuilder,
)
from ethereum.forks.amsterdam.vm import (  # noqa: E402
    BlockEnvironment,
    Evm,
    TransactionEnvironment,
)
from ethereum.forks.amsterdam.vm.exceptions import Revert  # noqa: E402
from ethereum.forks.amsterdam.vm.gas import GasMeter  # noqa: E402
from ethereum.forks.amsterdam.vm.interpreter import process_call  # noqa: E402
from ethereum.forks.amsterdam.vm.runtime import (  # noqa: E402
    get_valid_jump_destinations,
)
from ethereum.state import Account  # noqa: E402
from ethereum_types.bytes import Bytes20, Bytes32  # noqa: E402
from ethereum_types.numeric import U64, U256, Uint  # noqa: E402

CALLER = Bytes20(bytes.fromhex("ca" * 20))
TARGET = Bytes20(bytes.fromhex("c0de" * 10))
COINBASE = Bytes20(bytes.fromhex("ba5e" * 10))
BLOB_HASHES = (b"\x01" + b"\xb1" * 31, b"\x01" + b"\xb2" * 31)
EMPTY_HASH = keccak256(b"")


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    return bytes(data).hex() if data else "-"


class Pre:
    """The state before the block: accounts, storage and code in dictionaries."""

    def __init__(self, word):
        self.accounts, self.storage, self.code = {}, {}, {}
        if word == "-":
            return
        for entry in word.split(";"):
            address, nonce, balance, code, storage = entry.split(",")
            address, code = Bytes20(bytes.fromhex(address)), unhex(code)
            code_hash = keccak256(code)
            self.code[code_hash] = code
            self.accounts[address] = Account(Uint(int(nonce)), U256(int(balance)), code_hash)
            if storage != "-":
                for slot in storage.split("&"):
                    key, value = slot.split("=")
                    key = Bytes32(bytes.fromhex(key))
                    self.storage[(address, key)] = U256(int(value, 16))

    def get_account_optional(self, address):
        return self.accounts.get(address)

    def get_storage(self, address, key):
        return self.storage.get((address, key), U256(0))

    def get_code(self, code_hash):
        return self.code.get(code_hash, b"")

    def compute_state_root(self, block_diff):
        raise NotImplementedError


def show_logs(logs):
    return (
        ";".join(
            f"{tohex(log.address)},"
            f"{'.'.join(tohex(t) for t in log.topics) or '-'},{tohex(log.data)}"
            for log in logs
        )
        or "-"
    )


def show_state(pre, tx_state):
    addresses = set(pre.accounts) | set(tx_state.account_writes)
    out = []
    for address in sorted(addresses):
        account = state_tracker.get_account_optional(tx_state, address)
        if account is None:
            continue
        keys = {k for (a, k) in pre.storage if a == address}
        keys |= set(tx_state.storage_writes.get(address, {}))
        slots = []
        for key in sorted(keys):
            value = int(state_tracker.get_storage(tx_state, address, key))
            if value != 0:
                slots.append(f"{tohex(key)}={value:x}")
        out.append(
            f"{tohex(address)},{int(account.nonce)},{int(account.balance)},"
            f"{tohex(account.code_hash)},{'&'.join(slots) or '-'}"
        )
    return ";".join(out) or "-"


def run(static, gas, reservoir, value, data, code, accounts, raw=False):
    pre = Pre(accounts)
    block_state = state_tracker.BlockState(pre_state=pre)
    tx_state = state_tracker.TransactionState(parent=block_state)
    block_env = BlockEnvironment(
        chain_id=U64(1),
        state=block_state,
        block_gas_limit=Uint(30_000_000),
        block_hashes=[Bytes32((i + 1).to_bytes(32, "big")) for i in range(256)],
        coinbase=COINBASE,
        number=Uint(1000),
        base_fee_per_gas=Uint(7),
        time=U256(1_700_000_000),
        prev_randao=Bytes32(b"\x11" * 32),
        excess_blob_gas=U64(10 * 2**17),
        parent_beacon_block_root=Bytes32(b"\x22" * 32),
        block_access_list_builder=BlockAccessListBuilder(),
        slot_number=U64(0),
    )
    tx_env = TransactionEnvironment(
        origin=CALLER,
        recipient=TARGET,
        is_create=False,
        data=unhex(data),
        value=U256(int(value)),
        gas_limit=Uint(int(gas) + int(reservoir)),
        effective_gas_price=Uint(10),
        execution_gas_grant=Uint(int(gas)),
        state_gas_reservoir=Uint(int(reservoir)),
        calldata_floor=Uint(0),
        access_list_addresses=set(),
        access_list_storage_keys=set(),
        accounts_with_paid_writes=set(),
        state=tx_state,
        blob_versioned_hashes=tuple(Bytes32(h) for h in BLOB_HASHES),
        authorizations=(),
        index_in_block=Uint(0),
        tx_hash=None,
    )
    meter = GasMeter(
        gas_left=Uint(int(gas)),
        state_gas_left=Uint(int(reservoir)),
        state_gas_baseline=Uint(int(reservoir)),
    )
    code = unhex(code)
    evm = Evm(
        block_env=block_env,
        tx_env=tx_env,
        parent_evm=None,
        depth=Uint(0),
        caller=CALLER,
        current_target=TARGET,
        value=U256(int(value)),
        call_data=unhex(data),
        should_transfer_value=True,
        is_static=static == "1",
        disable_precompiles=False,
        code_address=TARGET,
        code=code,
        valid_jump_destinations=get_valid_jump_destinations(code),
        gas_meter=meter,
        pc=Uint(0),
        stack=[],
        memory=bytearray(),
        return_data=b"",
        logs=(),
        accounts_to_delete=set(),
        accessed_addresses={CALLER, TARGET},
        accessed_storage_keys=set(),
        running=True,
        output=b"",
        error=None,
    )
    process_call(evm)
    if evm.error is None:
        status = "ok"
    elif isinstance(evm.error, Revert):
        status = "revert"
    else:
        status = "halt"
    words = [
        status,
        str(int(meter.gas_left)),
        str(int(meter.state_gas_left)),
        tohex(evm.output),
    ]
    if status == "ok":
        words += [str(int(meter.refund_counter)), show_logs(evm.logs)]
        words.append(",".join(sorted(tohex(a) for a in evm.accounts_to_delete)) or "-")
    else:
        words += ["0", "-", "-"]
    # The reads of EIP-7928, which a rollback keeps: taken before this script reads the state.
    # A transaction reads its sender and its recipient before the frame starts.
    before = set() if raw else {CALLER, TARGET}
    account_reads = sorted(tohex(a) for a in tx_state.account_reads | before)
    reads = sorted(f"{tohex(a)}:{tohex(k)}" for a, k in tx_state.storage_reads)
    words.append(show_state(pre, tx_state))
    words.append(",".join(account_reads) or "-")
    words.append(",".join(reads) or "-")
    transient = sorted(
        f"{tohex(a)}:{tohex(k)}={int(v):x}"
        for (a, k), v in tx_state.transient_storage.items()
        if int(v) != 0
    )
    words.append(",".join(transient) or "-")
    error = type(evm.error).__name__ if evm.error else "-"
    return " ".join(words) + "\t" + error


def main():
    sys.setrecursionlimit(20000)
    for line in sys.stdin:
        words = line.rstrip("\n").split("\t")
        try:
            if words[0] == "run":
                print(run(*words[1:]), flush=True)
            elif words[0] == "reads":
                # The account reads of the frame alone.
                fields = run(*words[1:], raw=True).split("\t")[0].split(" ")
                print(fields[8], flush=True)
            else:
                print("error unknown command", flush=True)
        except Exception as error:  # A crash of the reference is an answer.
            print(f"crash {type(error).__name__}: {error}".replace("\n", " "), flush=True)


if __name__ == "__main__":
    main()

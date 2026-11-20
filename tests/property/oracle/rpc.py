"""References for the RPC, the wire messages and the history files of the execution layer."""

# One command per line, its words separated by tabs, and one answer per line.
# Bytes are in hexadecimal, `-` for none.  The commands are those of the modules below:
#     rpc_fees.py     eth_feeHistory on a view of plain fields.
#     rpc_logs.py     eth_getLogs, the receipts and the blocks of a view as JSON.
#     rpc_call.py     eth_call and eth_estimateGas on a state, with EELS.
#     rpc_state.py    The state getters and eth_getProof, with py-trie.
#     rpc_wire.py     The eth and snap messages, with the `rlp` package and py-trie.
#     rpc_era.py      Era1 files, with cramjam and eth-remerkleable.
# An answer that starts with `crash` says that the reference itself failed.

import importlib
import os
import signal
import sys
import traceback

# The interpreter runs isolated, so the directory of this file is not on the path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

MODULES = ["rpc_fees", "rpc_logs", "rpc_call", "rpc_state", "rpc_wire", "rpc_era"]
COMMANDS = {}
# A module that is not there yet leaves its commands out.
for name in MODULES:
    if os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), name + ".py")):
        COMMANDS.update(importlib.import_module(name).COMMANDS)


class Slow(BaseException):
    """The reference took too long on one command."""


SLOW_SECONDS = 60


def too_slow(signum, frame):
    raise Slow()


def main():
    sys.setrecursionlimit(20000)
    signal.signal(signal.SIGALRM, too_slow)
    for line in sys.stdin:
        words = line.rstrip("\n").split("\t")
        signal.alarm(SLOW_SECONDS)
        try:
            print(COMMANDS[words[0]](*words[1:]) or "-", flush=True)
        except Slow:
            print(f"slow {line[:300]}", file=sys.stderr, flush=True)
            print("crash slow", flush=True)
        except Exception as error:  # A crash of the reference is an answer.
            where = traceback.extract_tb(error.__traceback__)[-1]
            text = f"crash {type(error).__name__}: {error} at {where.name}:{where.lineno}"
            print(text.replace("\n", " ").replace("\t", " "), flush=True)
        signal.alarm(0)


if __name__ == "__main__":
    main()

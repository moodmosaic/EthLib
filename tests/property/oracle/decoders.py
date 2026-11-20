"""References for the decoders driver: one command per line, one answer per line."""

# Words are separated by tabs; bytes are in hexadecimal, `-` for none.
# An answer that starts with `error` says the reference refused the input.
# Each command is documented at its handler, in the module that holds it.

import importlib
import os
import resource
import sys

# A reference must never take the memory that a length in its input asks for.
resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))

# The interpreter runs isolated (-I), so the directory of the script is added by hand.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

MODULES = ("protobuf", "quic", "tls", "libp2p", "devp2p", "snappy")

HANDLERS = {}
for name in MODULES:
    HANDLERS.update(importlib.import_module("decoders_" + name).HANDLERS)


def main():
    for line in sys.stdin:
        words = line.rstrip("\n").split("\t")
        try:
            out = HANDLERS[words[0]](*words[1:])
        except Exception as e:  # The reference refused: say why, on one line.
            out = "error " + type(e).__name__ + " " + str(e).replace("\n", " ")[:120]
        print(out or "-", flush=True)


if __name__ == "__main__":
    main()

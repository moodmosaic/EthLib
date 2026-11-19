"""References for the networking layer: one command per line, one answer per line."""

# Words are separated by tabs; bytes are in hexadecimal, `-` for none.
# An answer that starts with `error` says the reference refused the input.
# Each command is documented at its handler.

import os
import sys

# The interpreter runs isolated (-I), so the directory of the script is added by hand.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import networking_codecs  # noqa: E402
import networking_crypto  # noqa: E402
import networking_snappy  # noqa: E402
import networking_wire  # noqa: E402

HANDLERS = {}
for module in (networking_snappy, networking_codecs, networking_crypto, networking_wire):
    HANDLERS.update(module.HANDLERS)


def main():
    for line in sys.stdin:
        words = line.rstrip("\n").split("\t")
        try:
            out = HANDLERS[words[0]](*words[1:])
        except Exception as e:  # The reference refused: say why, on one line.
            out = "error " + type(e).__name__ + " " + str(e).replace("\n", " ")[:120]
        print(out, flush=True)


if __name__ == "__main__":
    main()

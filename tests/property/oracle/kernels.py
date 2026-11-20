"""References for the kernels: one command per line, one answer per line."""

# Words are separated by tabs.  Integers are decimal, bytes are hexadecimal
# (`-` for none).  Each module lists its commands in its `answer`.

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import kernels_chain  # noqa: E402
import kernels_hash  # noqa: E402
import kernels_tables  # noqa: E402
import kernels_tower  # noqa: E402
import kernels_unicode  # noqa: E402


def answer(words):
    return (
        kernels_chain.answer(words)
        or kernels_tables.answer(words)
        or kernels_hash.answer(words)
        or kernels_tower.answer(words)
        or kernels_unicode.answer(words)
        or "error unknown command"
    )


if __name__ == "__main__":
    for line in sys.stdin:
        try:
            out = answer(line.rstrip("\n").split("\t"))
        except AssertionError as failure:
            out = f"references disagree: {failure}"
        print(out or "-", flush=True)

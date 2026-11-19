"""References for the consensus protocols around the state transition.

One command per line, words separated by tabs, one answer line.

    fc_*     The fork choice of the pyspec (see forkchoice_store.py).
    lc_init, lc_update, lc_force
             The light client store of the pyspec (see forkchoice_lightclient.py).
    others   Pure helpers of the pyspec (see forkchoice_helpers.py).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import forkchoice_helpers  # noqa: E402
import forkchoice_lightclient  # noqa: E402
import forkchoice_store  # noqa: E402


def answer(words):
    if words[0].startswith("fc_"):
        return forkchoice_store.answer(words)
    if words[0] in ("lc_init", "lc_update", "lc_force"):
        return forkchoice_lightclient.answer(words)
    return forkchoice_helpers.answer(words)


# FC_LOG names a file that takes every command, to run a failure again by hand.
LOG = open(os.environ["FC_LOG"], "a") if os.environ.get("FC_LOG") else None

for line in sys.stdin:
    if LOG:
        LOG.write(line)
        LOG.flush()
    try:
        reply = answer(line.rstrip("\n").split("\t"))
    except Exception as error:
        reply = f"error {type(error).__name__} {error}".replace("\n", " ")
    print(reply or "-", flush=True)

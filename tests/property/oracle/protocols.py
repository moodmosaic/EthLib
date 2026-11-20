"""References for the consensus protocols: consensus-specs at any preset, with real BLS."""

# One command per line, words separated by tabs, one answer line.
#
#     st <fork> <preset> <config> <signatures> <call> <state words> [| <argument words>]
#         Build a state at the preset from the words, apply the call, and answer
#         "<state hex> <argument hex> <result>".  The result is "ok:<state root>",
#         "val:<text>" or "error:<reason>".
#     on <fork> <preset> <config> <signatures> <call> <state hex> <argument words>
#         The same, on a state given by its SSZ bytes.
#     diff <fork> <preset> <state hex>
#         The fields in which a state differs from the last post-state.
#     stats
#         "<call>:<accepted>/<unchanged>/<refused>/<skipped>" for each call.
#     fc_*, px_*
#         The fork choice store, with fast confirmation: see `protocols_forkchoice.py`.
#     po_*
#         The optimistic store: see `protocols_optimistic.py`.
#     pi_*
#         The store of inclusion lists: see `protocols_lists.py`.
#     pp_*
#         Helpers that need no state: see `protocols_pure.py`.
#
# A preset is `minimal` or `mainnet`, then `;NAME=value` for each constant that differs.
# A configuration is `-` or `NAME=value;...`.
# See `protocols_spec.py`.
#
# <signatures> is `standin` or `real`.
# With `standin` a signature is valid when its first 32 bytes are a hash, as in `consensus.py`.
# The hash is the SHA-256 of the public keys followed by the message.
# With `real` every signature is a BLS signature by the secret keys of the validators.
# With `real` the checks are those of consensus-specs.
#
# The states and the operations are built by `consensus.py` and `consensus_ops.py`.
# This program reads those two and does not change them.
# It gives them the module of the preset and the signer.

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# `protocols_real` keeps the checks of consensus-specs, which `consensus` then replaces.
import protocols_real as real  # noqa: E402, I001
import consensus as base  # noqa: E402
import consensus_ops as ops  # noqa: E402
import protocols_blocks as blocks  # noqa: E402
import protocols_duties as duties  # noqa: E402
import protocols_forkchoice as forkchoice  # noqa: E402
import protocols_gossip as gossip  # noqa: E402
import protocols_light as light  # noqa: E402
import protocols_lists as lists  # noqa: E402
import protocols_optimistic as optimistic  # noqa: E402
import protocols_pure as pure  # noqa: E402
import protocols_spec as presets  # noqa: E402

CASE = {}
STAND_IN = {
    "signed": ops.signed,
    "fake_signature": ops.fake_signature,
    "sync_participant_keys": ops.sync_participant_keys,
    "pubkey": ops.pubkey,
    "prepare": ops.prepare,
}


def prepare(spec, fork, state, call, words):
    """The argument and the function of a call, with an upgrade at the preset of the case."""
    if call.startswith("upgrade_to_"):
        target = presets.configure_chain(call[11:], CASE["preset"], CASE["config"])
        return "-", lambda: getattr(target, call)(state)
    light.PRESETS["chain"] = lambda target: presets.configure_chain(
        target, CASE["preset"], CASE["config"]
    )
    duties.PRESETS["chain"] = light.PRESETS["chain"]
    for module in (blocks, duties, light, gossip):
        made = module.prepare(spec, fork, state, call, words)
        if made is not None:
            return made
    return STAND_IN["prepare"](spec, fork, state, call, words)


ops.prepare = prepare


def enter(fork, preset, config, signatures):
    """The module of a case, with its configuration and its signatures in force."""
    real.use(signatures, ops, base, STAND_IN)
    spec = presets.configure_chain(fork, preset, config)
    CASE.update(preset=preset, config=config, spec=spec)
    base.spec_of = lambda _fork: spec
    return spec


def extras(spec, fork, state, words):
    """The words of a state that `consensus.py` does not know.

    `dup=i,j` gives validator `j` the key of validator `i`.
    `fill=seed` sets the fields that the other words leave at their default.
    `ptc` gives the state the window of payload committees that its registry has.
    """
    for word in words:
        key, _, text = word.partition("=")
        if key == "dup" and len(state.validators) > 0:
            source, target = (int(n) % len(state.validators) for n in text.split(","))
            state.validators[target].pubkey = state.validators[source].pubkey
        elif key == "fill":
            blocks.fill(spec, fork, state, int(text))
        elif key == "ptc" and hasattr(spec, "initialize_ptc_window"):
            try:
                state.ptc_window = spec.initialize_ptc_window(state)
            except Exception:
                continue


def st(fork, preset, config, signatures, call, words):
    spec = enter(fork, preset, config, signatures)
    split = words.index("|") if "|" in words else len(words)
    _, state = base.build_state(fork, words[:split])
    extras(spec, fork, state, words[:split])
    return base.run(spec, fork, state, call, words[split + 1 :])


def on(fork, preset, config, signatures, call, data, words):
    spec = enter(fork, preset, config, signatures)
    state = spec.BeaconState.decode_bytes(bytes.fromhex(data))
    return base.run(spec, fork, state, call, words)


def answer(words):
    if words[0].startswith("pp_"):
        return pure.answer(words)
    if words[0].startswith("pi_"):
        return lists.answer(words)
    if words[0].startswith("po_"):
        real.use("off", ops, base, STAND_IN)
        if words[0] == "po_init":
            presets.configure_chain(words[1], "minimal", "-")
        return optimistic.answer(words)
    if words[0].startswith(("fc_", "px_")):
        real.use("off", ops, base, STAND_IN)
        return forkchoice.answer(words, lambda fork: presets.configure_chain(fork, "minimal", "-"))
    match words:
        case ["st", fork, preset, config, signatures, call, *rest]:
            return st(fork, preset, config, signatures, call, rest)
        case ["on", fork, preset, config, signatures, call, data, *rest]:
            return on(fork, preset, config, signatures, call, data, rest)
        case ["stats"]:
            return base.stats()
        case ["diff", fork, _preset, data]:
            return base.diff(fork, data)
    return "error unknown command"


if __name__ == "__main__":
    # `PROTOCOLS_LOG` names a file that gets every command, to run one again by hand.
    log = open(os.environ["PROTOCOLS_LOG"], "a") if os.environ.get("PROTOCOLS_LOG") else None
    for line in sys.stdin:
        if log:
            log.write(line)
            log.flush()
        try:
            out = answer(line.rstrip("\n").split("\t"))
        except Exception as e:
            out = f"oracle-failure:{type(e).__name__}:{e}".replace("\n", " ")
        print(out or "-", flush=True)

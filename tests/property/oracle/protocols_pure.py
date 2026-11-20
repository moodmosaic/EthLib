"""Helpers of consensus-specs that need no state, at any value of the constants they read."""

#     pp_shuffle <rounds> <count> <seed> <indices>
#         The shuffled position of each index, or `error`.  consensus-specs shuffles the whole
#         list, which a count of 2^40 does not allow, so the position of one index is computed
#         by the same steps on that index alone; on a small count the two are compared here.
#     pp_time <slots per epoch> <max seed lookahead> <epochs per period> <slot ms> <name> <a> <b>
#         A function of slots, epochs and time, with those four constants set.
#     pp_requests <fork> <preset> <item> ...
#         The root of `get_execution_requests` of the items, or `error`.

import hashlib

import protocols_spec as presets


def sha(data):
    return hashlib.sha256(data).digest()


def shuffled_index(index, count, seed, rounds):
    """`compute_shuffled_permutation` of the specification, followed for one index."""
    assert index < count
    for current_round in range(rounds):
        round_bytes = current_round.to_bytes(1, "little")
        pivot = int.from_bytes(sha(seed + round_bytes)[0:8], "little") % count
        flip = (pivot + count - index) % count
        position = max(index, flip)
        source = sha(seed + round_bytes + (position // 256).to_bytes(4, "little"))
        byte_val = source[(position % 256) // 8]
        bit = (byte_val >> (position % 8)) % 2
        index = flip if bit else index
    return index


def shuffle(rounds, count, seed, indices):
    spec = presets.spec_of("phase0", "minimal")
    saved = spec.SHUFFLE_ROUND_COUNT
    spec.SHUFFLE_ROUND_COUNT = spec.Uint64(rounds)
    try:
        whole = None
        if 0 < count <= 600:
            # The function before its cache, which does not know the number of rounds.
            whole = [int(p) for p in spec._compute_shuffled_permutation(spec.Uint64(count), seed)]
        out = []
        for index in indices:
            if index >= count:
                return "error"
            position = shuffled_index(index, count, seed, rounds)
            if whole is not None and whole[index] != position:
                raise ValueError("the two shuffles of the reference differ")
            out.append(str(position))
        return ",".join(out) or "-"
    finally:
        spec.SHUFFLE_ROUND_COUNT = saved


def time(slots, lookahead, period, duration, name, a, b):
    spec = presets.spec_of("heze", "minimal")
    saved = (spec.SLOTS_PER_EPOCH, spec.MAX_SEED_LOOKAHEAD, spec.EPOCHS_PER_SYNC_COMMITTEE_PERIOD)
    config = spec.config
    spec.SLOTS_PER_EPOCH = spec.Slot(slots)
    spec.MAX_SEED_LOOKAHEAD = spec.Epoch(lookahead)
    spec.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = spec.Epoch(period)
    spec.config = config._replace(SLOT_DURATION_MS=spec.Uint64(duration))
    try:
        function = getattr(spec, name)
        two = name in (
            "compute_time_at_slot",
            "compute_slot_at_time",
            "compute_time_at_slot_ms",
            "compute_slot_at_time_ms",
        )
        arguments = (spec.Uint64(a), spec.Uint64(b)) if two else (spec.Uint64(a),)
        return str(int(function(*arguments)))
    except Exception:
        return "error"
    finally:
        spec.SLOTS_PER_EPOCH, spec.MAX_SEED_LOOKAHEAD, spec.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = saved
        spec.config = config


def requests(fork, preset, items):
    spec = presets.spec_of(fork, preset)
    try:
        made = spec.get_execution_requests([bytes.fromhex(i) if i != "-" else b"" for i in items])
        return bytes(made.hash_tree_root()).hex()
    except Exception:
        return "error"


def answer(words):
    match words:
        case ["pp_requests", fork, preset, *items]:
            return requests(fork, preset, items)
        case ["pp_shuffle", rounds, count, seed, indices]:
            wanted = [int(i) for i in indices.split(",")] if indices != "-" else []
            return shuffle(int(rounds), int(count), bytes.fromhex(seed), wanted)
        case ["pp_time", slots, lookahead, period, duration, name, a, b]:
            return time(
                int(slots), int(lookahead), int(period), int(duration), name, int(a), int(b)
            )
    raise ValueError(words[0])

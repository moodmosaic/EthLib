"""The duties of a validator for the consensus oracle: calls that take a state and numbers."""

# `consensus_ops.py` knows a call by its name in one of four sets.
# The calls of `validator.md` and of the committees of Gloas and Heze have the same shapes.
# Each shape is a state, then numbers.
# A call that takes a slot gets it as an epoch and a place in the epoch, as there.
#
#     is_aggregator <epoch,offset,committee> <proof hex>
#     is_sync_committee_aggregator <proof hex>
#     get_validators_custody_requirement <indices>
#     process_payload_attestation <seed,kind>
#     process_slots_across <count>
#         Slots one at a time, with the upgrade to the next fork whenever a slot starts the
#         epoch of that fork in the configuration, as the `fork.md` of each fork says.

import consensus_ops as ops

NUMBER_READERS = {
    "get_committee_assignment",
    "is_proposer",
    "is_assigned_to_sync_committee",
    "compute_subnets_for_sync_committee",
    "get_ptc_assignment",
    "get_upcoming_proposal_slots",
    "get_inclusion_list_committee_assignment",
}
READERS = {"compute_weak_subjectivity_period"}
SLOT_READERS = {"get_ptc", "get_inclusion_list_committee"}

ops.READERS |= READERS


def shown(value):
    """A value that may be none, which `consensus.py` would take for a change of the state."""
    return "None" if value is None else value


def across(chain, fork, state, count):
    """The state some slots later, upgraded on the way, of whatever fork it then is."""
    target = int(state.slot) + count
    assert target < 2**64
    order = ops.ORDER
    while state.slot < target:
        spec = chain(fork)
        spec.process_slots(state, state.slot + 1)
        while fork != order[-1]:
            later = order[order.index(fork) + 1]
            after = chain(later)
            first = getattr(after.config, f"{later.upper()}_FORK_EPOCH")
            starts = state.slot % spec.SLOTS_PER_EPOCH == 0
            if not (starts and spec.compute_epoch_at_slot(state.slot) == first):
                break
            state = getattr(after, f"upgrade_to_{later}")(state)
            fork = later
    return state


# `protocols.py` sets how to get the module of another fork at the preset of the case.
PRESETS = {}


def prepare(spec, fork, state, call, words):
    """The argument and the function of a call of this module, or none for another call."""
    if call == "process_slots_across":
        (count,) = ops.numbers(words[0])
        return "-", lambda: across(PRESETS["chain"], fork, state, count)
    if call in NUMBER_READERS and hasattr(spec, call):
        f = ops.words64(spec, words[0])
        return "-", lambda: shown(getattr(spec, call)(state, *f))
    if call in SLOT_READERS and hasattr(spec, call):
        epoch, offset = ops.numbers(words[0])
        slot = spec.Slot((epoch * int(spec.SLOTS_PER_EPOCH) + offset) % 2**64)
        return "-", lambda: getattr(spec, call)(state, slot)
    if call == "is_aggregator":
        epoch, offset, index = ops.numbers(words[0])
        slot = spec.Slot((epoch * int(spec.SLOTS_PER_EPOCH) + offset) % 2**64)
        proof = spec.BLSSignature(bytes.fromhex(words[1]))
        return "-", lambda: spec.is_aggregator(state, slot, spec.CommitteeIndex(index), proof)
    if call == "is_sync_committee_aggregator" and hasattr(spec, call):
        proof = spec.BLSSignature(bytes.fromhex(words[0]))
        return "-", lambda: spec.is_sync_committee_aggregator(proof)
    if call == "get_validators_custody_requirement" and hasattr(spec, call):
        indices = [spec.ValidatorIndex(i) for i in ops.numbers(words[0])] if words else []
        return "-", lambda: spec.get_validators_custody_requirement(state, indices)
    if call == "process_payload_attestation" and hasattr(spec, call):
        seed, kind = ops.numbers(words[0])
        parent = state.latest_block_header.parent_root
        made = ops.payload_attestation(spec, state, parent, seed, kind)
        if made is None:
            raise ops.SkipError()
        return ops.hexof(made), lambda: spec.process_payload_attestation(state, made)
    return None

"""Fast confirmation and optimistic sync, on the fork choice store of `forkchoice_store.py`."""

# The store, its blocks and its votes are those of `forkchoice_store.py`.
# Every `fc_*` command goes there unchanged.
# This module adds what that oracle never ran:
#
#     px_view              the view of the fast confirmation store
#     px_confirm           on_fast_confirmation, then that view
#     px_restart <index>   get_restart_resilient_confirmed_root, for a block confirmed before
#     px_optimistic ...    the optimistic store (see `Optimistic` below)
#
# EthLib's fast confirmation rule differs from the pinned consensus-specs in three ways.
# Its CHANGELOG states them.
# So the reference here is the rule of consensus-specs with those three changes.
# The reference is written from the CHANGELOG and the docstrings, not from EthLib's code:
#
# 1. The weight of the committees of a range of slots is exact (issue 1828).
#    It is the active members of those committees, each once, in place of an average per slot.
# 2. The discount for empty slots may exceed the weight of the committees since the parent.
#    Then the safety threshold fails, in place of answering zero (issue 1832).
# 3. The discount for empty slots also counts the votes for the pending node of the parent.
#    This holds from Gloas (issue 1368).
#
# Every other function of the rule is that of consensus-specs.

import os

import forkchoice_store as fcs

EXTRA = {}
CONTEXT = {}


def short(root):
    return bytes(root).hex()[:8]


def checkpoint(c):
    return f"{int(c.epoch)}:{short(c.root)}"


def patch(spec):
    """Give a module of consensus-specs the three changes of EthLib's rule, once."""
    if getattr(spec, "protocols_patched", False):
        return
    spec.protocols_patched = True
    gloas = hasattr(spec, "PAYLOAD_STATUS_PENDING")

    def committee_weight(store, balance_source, start_slot, end_slot):
        if start_slot > end_slot:
            return spec.Gwei(0)
        if spec.is_full_validator_set_covered(start_slot, end_slot):
            return spec.get_total_active_balance(balance_source)
        members = set()
        for slot in range(int(start_slot), int(end_slot) + 1):
            members.update(spec.get_slot_committee(store, spec.Slot(slot)))
        epoch = spec.get_current_epoch(balance_source)
        active = [
            i for i in members if spec.is_active_validator(balance_source.validators[i], epoch)
        ]
        return spec.get_total_balance(balance_source, set(active))

    def estimate(total_active_balance, start_slot, end_slot):
        return committee_weight(CONTEXT["store"], CONTEXT["source"], start_slot, end_slot)

    def with_context(function, source_of):
        def wrapped(store, *rest):
            saved = dict(CONTEXT)
            CONTEXT.update(store=store, source=source_of(store, *rest))
            try:
                return function(store, *rest)
            finally:
                CONTEXT.clear()
                CONTEXT.update(saved)

        return wrapped

    def compute_safety_threshold(store, block_root, balance_source):
        current_slot = spec.get_current_slot(store)
        block = store.blocks[block_root]
        parent_block = store.blocks[block.parent_root]
        proposer_score = spec.compute_proposer_score(balance_source)
        maximum_support = committee_weight(
            store, balance_source, parent_block.slot + 1, current_slot - 1
        )
        support_discount = spec.get_support_discount(store, balance_source, block_root)
        adversarial_weight = spec.get_adversarial_weight(store, balance_source, block_root)
        assert support_discount <= maximum_support
        return (maximum_support + proposer_score + 2 * adversarial_weight - support_discount) // 2

    def node_support(store, balance_source, nodes, start_slot, end_slot):
        members = set()
        for slot in range(int(start_slot), int(end_slot) + 1):
            members.update(spec.get_slot_committee(store, spec.Slot(slot)))
        epoch = spec.get_current_epoch(balance_source)
        total = 0
        for index in members:
            validator = balance_source.validators[index]
            if validator.slashed or not spec.is_active_validator(validator, epoch):
                continue
            if index not in store.latest_messages or index in store.equivocating_indices:
                continue
            if spec.get_supported_node(store, store.latest_messages[index]) in nodes:
                total += int(validator.effective_balance)
        return spec.Gwei(total)

    def compute_empty_slot_support_discount(store, balance_source, block_root):
        block = store.blocks[block_root]
        parent_block = store.blocks[block.parent_root]
        if parent_block.slot + 1 == block.slot:
            return spec.Gwei(0)
        pending = spec.get_node_for_root(block.parent_root)
        built_on = spec.get_ancestor(store, spec.get_node_for_root(block_root), parent_block.slot)
        support = node_support(
            store, balance_source, [pending, built_on], parent_block.slot + 1, block.slot - 1
        )
        adversarial = spec.compute_adversarial_weight(
            store, balance_source, parent_block.slot + 1, block.slot - 1
        )
        return support - adversarial if support > adversarial else spec.Gwei(0)

    spec.estimate_committee_weight_between_slots = estimate
    spec.compute_adversarial_weight = with_context(
        spec.compute_adversarial_weight, lambda store, source, *_: source
    )
    spec.compute_honest_ffg_support_for_current_target = with_context(
        spec.compute_honest_ffg_support_for_current_target,
        lambda store: spec.get_pulled_up_head_state(store),
    )
    spec.compute_safety_threshold = compute_safety_threshold
    if gloas:
        spec.compute_empty_slot_support_discount = compute_empty_slot_support_discount


def value(compute, show=str):
    try:
        return show(compute())
    except Exception:
        return "e"


def flag(compute):
    return value(compute, lambda b: "t" if b else "f")


def view(extra):
    """What the driver compares of the fast confirmation rule after every command."""
    spec, fcr = extra["spec"], extra["fcr"]
    store = fcr.store
    try:
        head = spec.get_head(store).root
    except Exception:
        head = None
    chain = []
    if head is not None:
        root = head
        # The last blocks of the chain of the head, where the rule decides.
        while root in store.blocks and len(chain) < 5:
            chain.append(root)
            root = store.blocks[root].parent_root
    try:
        source = spec.get_current_balance_source(fcr)
    except Exception:
        source = None
    safety = []
    for root in chain:
        if source is None or store.blocks[root].parent_root not in store.blocks:
            safety.append(f"{short(root)}:e:e:e")
            continue
        safety.append(
            ":".join(
                [
                    short(root),
                    value(lambda r=root: int(spec.compute_safety_threshold(store, r, source))),
                    value(lambda r=root: int(spec.get_adversarial_weight(store, source, r))),
                    flag(lambda r=root: spec.is_one_confirmed(store, source, r)),
                ]
            )
        )
    words = [
        f"c={short(fcr.confirmed_root)}",
        f"po={checkpoint(fcr.previous_epoch_observed_justified_checkpoint)}",
        f"co={checkpoint(fcr.current_epoch_observed_justified_checkpoint)}",
        f"pg={checkpoint(fcr.previous_epoch_greatest_unrealized_checkpoint)}",
        f"ph={short(fcr.previous_slot_head)}",
        f"ch={short(fcr.current_slot_head)}",
        "nc=" + flag(lambda: spec.will_no_conflicting_checkpoint_be_justified(store)),
        "tj=" + flag(lambda: spec.will_current_target_be_justified(store)),
        "ts=" + value(lambda: int(spec.get_current_target_score(store))),
        "hs=" + value(lambda: int(spec.compute_honest_ffg_support_for_current_target(store))),
        "sf=" + flag(lambda: spec.is_confirmed_chain_safe(fcr, fcr.confirmed_root)),
        "bf=" + flag(lambda: spec.block_should_be_finalized(store, fcr.confirmed_root)),
        "st=" + ",".join(safety),
    ]
    if hasattr(spec, "get_safe_execution_block_hash"):
        words.append("se=" + value(lambda: short(spec.get_safe_execution_block_hash(fcr))))
    return " ".join(words)


def confirm(extra):
    spec, fcr = extra["spec"], extra["fcr"]
    saved = spec.FastConfirmationStore(**{k: getattr(fcr, k) for k in fcr.__dataclass_fields__})
    try:
        spec.on_fast_confirmation(fcr)
        status = "ok"
    except Exception:
        # A handler that fails leaves the store of the rule as it was.
        for name in fcr.__dataclass_fields__:
            setattr(fcr, name, getattr(saved, name))
        status = "error"
    return status


def restart(extra, index):
    spec, fcr = extra["spec"], extra["fcr"]
    entry = fcs.CURRENT.blocks[int(index)]
    if entry is None or entry.root not in fcr.store.blocks:
        return "skip"
    spec.get_root_confirmed_before_restart = lambda: entry.root
    return (
        bytes(entry.root).hex()
        + "\t"
        + value(lambda: short(spec.get_restart_resilient_confirmed_root(fcr)))
    )


def extra():
    """The fast confirmation store that goes with the fork choice store of the run."""
    if EXTRA.get("of") is not fcs.CURRENT:
        spec = fcs.CURRENT.spec
        patch(spec)
        if os.environ.get("PROTOCOLS_MUTANT") == "byzantine":
            # A mutant of the reference: one percent more of Byzantine stake, which must fail.
            share = spec.config.CONFIRMATION_BYZANTINE_THRESHOLD
            spec.config = spec.config._replace(CONFIRMATION_BYZANTINE_THRESHOLD=share + 1)
        EXTRA.clear()
        EXTRA.update(
            of=fcs.CURRENT, spec=spec, fcr=spec.get_fast_confirmation_store(fcs.CURRENT.store)
        )
    return EXTRA


def answer(words, reset):
    if words[0] == "fc_init":
        # An earlier command may have left another configuration on the module.
        reset(words[1])
    if words[0].startswith("fc_"):
        return fcs.answer(words)
    if words[0] == "px_view":
        return view(extra())
    if words[0] == "px_confirm":
        return confirm(extra()) + "\t" + view(extra())
    if words[0] == "px_restart":
        return restart(extra(), words[1])
    raise ValueError(words[0])

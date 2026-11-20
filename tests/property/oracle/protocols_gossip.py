"""Gossip rules of operations and sync committee messages, on a store made of one state."""

#     gossip <kind,time,subnet,...> [<indices> <indices>]
#
# The state of the case is the anchor of a fork choice store, so it is the state of the head.
# The oracle builds a message for that state and checks it with the gossip rule of consensus-specs.
# Then it checks the message once more with what the first check recorded.
#
# The first kinds are 0 a voluntary exit, 1 a proposer slashing and 2 an attester slashing.
# The other kinds are 3 a change of BLS credentials and 4 a sync committee message.
# `time` moves the clock of the check by that many slots.
# The other numbers are those of the builder of the operation.
#
# The argument is the anchor block and the message, each after its length in four bytes.
# The answer is the two verdicts: accept, ignore, reject, or error.

import dataclasses

import consensus_ops as ops
import protocols_light as light


def fresh_seen(spec):
    return spec.Seen(
        **{
            f.name: ({} if str(f.type).startswith("dict") else set())
            for f in dataclasses.fields(spec.Seen)
        }
    )


def message_of(spec, fork, state, kind, f, words, root):
    """A message of a kind, with the rule that checks it and the subnet it travels on."""
    if kind == 0:
        made = ops.voluntary_exit(spec, fork, state, f[:3])
        return made, spec.validate_voluntary_exit_gossip, None
    if kind == 1:
        made = ops.proposer_slashing(spec, fork, state, f[:7])
        return made, spec.validate_proposer_slashing_gossip, None
    if kind == 2:
        head = ",".join(str(n) for n in f[:5])
        made = ops.attester_slashing(spec, fork, state, [head] + list(words[1:3]))
        return made, spec.validate_attester_slashing_gossip, None
    if kind == 3 and hasattr(spec, "validate_bls_to_execution_change_gossip"):
        made = ops.bls_change(spec, fork, state, f[:4])
        return made, spec.validate_bls_to_execution_change_gossip, None
    if kind == 4 and hasattr(spec, "validate_sync_committee_message_gossip"):
        index, slot_delta, ok, root_ok = f[:4]
        slot = (int(state.slot) + slot_delta) % 2**64
        voted = root if root_ok else ops.sha(b"another block")
        domain = spec.get_domain(
            state, spec.DOMAIN_SYNC_COMMITTEE, spec.compute_epoch_at_slot(spec.Slot(slot))
        )
        signature = ops.signed(spec, [ops.key_at(state, index)], spec.Root(voted), domain, ok)
        made = spec.SyncCommitteeMessage(
            slot=slot, beacon_block_root=voted, validator_index=index, signature=signature
        )
        return made, spec.validate_sync_committee_message_gossip, f[4]
    raise ops.SkipError()


def verdict(spec, check, seen, store, message, time_ms, subnet):
    arguments = [seen, store, message]
    names = check.__code__.co_varnames[: check.__code__.co_argcount]
    if "current_time_ms" in names:
        arguments.append(spec.Uint64(time_ms))
    if "subnet_id" in names:
        arguments.append(spec.SubnetID(subnet))
    try:
        check(*arguments)
        return "accept"
    except spec.GossipIgnore:
        return "ignore"
    except spec.GossipReject:
        return "reject"
    except Exception:
        return "error"


def prepare(spec, fork, state, call, words):
    """The argument and the function of a call of this module, or none for another call."""
    if call != "gossip":
        return None
    kind, ahead, subnet, *f = ops.numbers(words[0])
    # The head of a store is found from the block of its checkpoint, at the start of an epoch.
    start = spec.compute_start_slot_at_epoch(spec.get_current_epoch(state))
    anchor = spec.BeaconBlock(slot=start, state_root=state.hash_tree_root())
    if hasattr(anchor.body, "signed_execution_payload_bid"):
        anchor.body.signed_execution_payload_bid.message = state.latest_execution_payload_bid
        anchor.state_root = state.hash_tree_root()
    try:
        store = spec.get_forkchoice_store(state, anchor)
    except Exception as e:
        raise ops.SkipError() from e
    message, check, own_subnet = message_of(
        spec, fork, state, kind, f, words, anchor.hash_tree_root()
    )
    if own_subnet is not None:
        subnet = own_subnet
    time_ms = int(store.time_ms) + ahead * int(spec.config.SLOT_DURATION_MS)

    def apply():
        seen = fresh_seen(spec)
        first = verdict(spec, check, seen, store, message, time_ms, subnet)
        second = verdict(spec, check, seen, store, message, time_ms, subnet)
        return f"{first},{second}"

    return light.parts(anchor, message), apply

"""Light client updates as a full node makes them, for the consensus oracle."""

#     create_light_client_update <seed,finalized,break,gap>
#
# The state of the case is the attested state.
# The oracle gives it a block, a child block with a sync aggregate and the state after that child.
# It gives it a finalized block too.
# It gives them so that the headers and roots agree as `create_light_client_update` asks.
# `finalized` is 0 for no finalized block, 1 for one, 2 for the genesis block.
# `break` undoes one of the agreements.
#
# The argument is four SSZ values, each after its length in four bytes.
# The first three are the state after the child, the child and the attested block.
# The fourth is the finalized block or nothing.
# The answer is the roots of the update, of its finality update and of its optimistic update.
# Then the root of the update upgraded to the next fork that changes it, or `-` where there is none.

import consensus_ops as ops
import protocols_blocks as blocks

NEXT = {
    "altair": "capella",
    "bellatrix": "capella",
    "capella": "deneb",
    "deneb": "electra",
    "electra": "gloas",
    "fulu": "gloas",
}


def header_of(spec, block):
    return spec.BeaconBlockHeader(
        slot=block.slot,
        proposer_index=block.proposer_index,
        parent_root=block.parent_root,
        body_root=block.body.hash_tree_root(),
    )


def a_block(spec, fork, state, slot, seed, label):
    """A block of a slot with a filled body, which no state transition has to accept."""
    block = spec.BeaconBlock(
        slot=slot,
        proposer_index=blocks.number(seed, label, 2**20),
        parent_root=blocks.blob(seed, label + " parent", 32),
        state_root=blocks.blob(seed, label + " state", 32),
    )
    block.body.graffiti = blocks.blob(seed, label + " graffiti", 32)
    if hasattr(block.body, "execution_payload"):
        payload = block.body.execution_payload
        blocks.fill_payload(spec, fork, state, payload, seed + len(label), seed % 3)
        payload.timestamp = blocks.number(seed, label + " time", 2**40)
        payload.parent_hash = blocks.blob(seed, label + " parent hash", 32)
    return block


def parts(*values):
    """SSZ values one after another, each after its length in four bytes."""
    out = b""
    for value in values:
        raw = bytes(value.encode_bytes()) if value is not None else b""
        out += len(raw).to_bytes(4, "little") + raw
    return out.hex()


def prepare(spec, fork, state, call, words):
    """The argument and the function of a call of this module, or none for another call."""
    if call != "create_light_client_update" or not hasattr(spec, call):
        return None
    seed, finalized_kind, broken, gap = ops.numbers(words[0])
    finalized = None
    if finalized_kind:
        slot = 0 if finalized_kind == 2 else max(int(state.slot) // 2, 1)
        made = a_block(spec, fork, state, slot, seed, "finalized")
        finalized = spec.SignedBeaconBlock(message=made)
        root = made.hash_tree_root() if finalized_kind == 1 else spec.Root()
        state.finalized_checkpoint.root = root if broken != 3 else blocks.blob(seed, "other", 32)
    attested = a_block(spec, fork, state, int(state.slot), seed, "attested")
    state.latest_block_header = header_of(spec, attested)
    attested.state_root = state.hash_tree_root()
    if broken == 2:
        attested.state_root = blocks.blob(seed, "another attested state", 32)
    after = state.copy()
    after.slot = (int(state.slot) + 1 + gap) % 2**64
    child = a_block(spec, fork, after, int(after.slot), seed, "child")
    child.parent_root = attested.hash_tree_root()
    size = int(spec.SYNC_COMMITTEE_SIZE)
    bits = ops.seeded_bits(seed if broken != 4 else 7, size)
    child.body.sync_aggregate.sync_committee_bits = ops.field_of(
        spec.SyncAggregate, "sync_committee_bits", bits
    )
    child.body.sync_aggregate.sync_committee_signature = blocks.blob(seed, "sync", 96)
    after.latest_block_header = header_of(spec, child)
    child.state_root = after.hash_tree_root()
    if broken == 1:
        child.state_root = blocks.blob(seed, "another state", 32)
    signed = spec.SignedBeaconBlock(message=child)
    signed_attested = spec.SignedBeaconBlock(message=attested)

    def apply():
        update = spec.create_light_client_update(after, signed, state, signed_attested, finalized)
        roots = [
            update.hash_tree_root(),
            spec.create_light_client_finality_update(update).hash_tree_root(),
            spec.create_light_client_optimistic_update(update).hash_tree_root(),
        ]
        shown = [bytes(r).hex() for r in roots]
        target = NEXT.get(fork)
        if target is None:
            return " ".join(shown + ["-"]).replace(" ", ",")
        later = PRESETS["chain"](target)
        upgraded = getattr(later, f"upgrade_lc_update_to_{target}")(update)
        return ",".join(shown + [bytes(upgraded.hash_tree_root()).hex()])

    return parts(after, signed, signed_attested, finalized), apply


# `protocols.py` sets how to get the module of another fork at the preset of the case.
PRESETS = {}

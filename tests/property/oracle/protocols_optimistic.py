"""Optimistic sync: the functions of consensus-specs, and a model of the guide's transitions."""

# The guide `optimistic-sync.md` defines four functions, which consensus-specs runs.
# It states the transitions of a block in prose, which this module writes out:
#
# - A block is imported optimistically only when it is an optimistic candidate.
# - NOT_VALIDATED -> VALID: the block and its ancestors leave the optimistic set.
# - NOT_VALIDATED -> INVALIDATED: the first invalid block and its descendants leave the fork choice.
#   They leave the optimistic set too.
#   The latest valid hash names the payload of the last valid ancestor.
#   The first invalid block is the child of that ancestor on the chain.
#   Without a hash, or when no known ancestor has that payload, it is the block itself.
#
#     po_init <fork>                         the anchor state and block, then the view
#     po_import <parent> <gap> <payload> <clock> <optimistic>
#                                            a block and whether it is a candidate, then the view
#     po_valid <index>                       the root, then the view
#     po_invalid <index> <kind>              the block, the latest valid hash, then the view
#
# The view is the optimistic roots and the roots that the fork choice still holds.
# Then the latest verified ancestor of each of those, and the head with whether it is optimistic.

import hashlib

import forkchoice_store as fcs

RUN = {}


def sha(data):
    return hashlib.sha256(data).digest()


def short(root):
    return bytes(root).hex()[:8]


def init(fork):
    made = fcs.ForkChoice(fork, 16, 0, False)
    spec = made.spec
    anchor = made.blocks[0].signed.message
    root = anchor.hash_tree_root()
    RUN.clear()
    RUN.update(
        spec=spec,
        blocks=[anchor],
        roots=[root],
        held={bytes(root)},
        store=spec.OptimisticStore(
            optimistic_roots=set(), head_block_root=root, blocks={root: anchor}, block_states={}
        ),
    )
    state = made.anchor_state
    return "\t".join([state.encode_bytes().hex(), anchor.encode_bytes().hex(), view()])


def head():
    """The head of the model: the deepest block that the fork choice holds."""
    store = RUN["store"]
    held = [r for r in RUN["roots"] if bytes(r) in RUN["held"]]
    return max(held, key=lambda r: (int(store.blocks[r].slot), bytes(r)))


def view():
    spec, store = RUN["spec"], RUN["store"]
    held = sorted(RUN["held"])
    ancestors = []
    for raw in held:
        block = store.blocks[spec.Root(raw)]
        try:
            found = short(spec.latest_verified_ancestor(store, block).hash_tree_root())
        except Exception:
            found = "e"
        ancestors.append(f"{raw.hex()[:8]}:{found}")
    top = head()
    optimistic = spec.is_optimistic(store, store.blocks[top])
    return " ".join(
        [
            "o=" + ",".join(sorted(short(r) for r in store.optimistic_roots)),
            "k=" + ",".join(r.hex()[:8] for r in held),
            "a=" + ",".join(ancestors),
            f"h={short(top)}:{'t' if optimistic else 'f'}",
        ]
    )


def valid(root):
    """The block and its ancestors leave the optimistic set."""
    store = RUN["store"]
    while root in store.blocks:
        store.optimistic_roots.discard(root)
        root = store.blocks[root].parent_root


def is_candidate(spec, store, clock, block):
    """`is_optimistic_candidate_block`: of consensus-specs at Bellatrix, of the guide after it.

    The modules after Bellatrix do not carry the function, so its three lines are written here.
    """
    if hasattr(spec, "is_optimistic_candidate_block"):
        return spec.is_optimistic_candidate_block(store, spec.Slot(clock), block)
    parent = store.blocks[block.parent_root]
    if parent.body.execution_payload != type(parent.body.execution_payload)():
        return True
    return block.slot + spec.SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY <= spec.Slot(clock)


def import_block(parent, gap, payload, clock, optimistic):
    spec, store = RUN["spec"], RUN["store"]
    above = RUN["blocks"][parent]
    block = spec.BeaconBlock(
        slot=int(above.slot) + 1 + gap,
        parent_root=RUN["roots"][parent],
        state_root=sha(b"state" + len(RUN["blocks"]).to_bytes(4, "little")),
    )
    if payload:
        made = block.body.execution_payload
        made.block_hash = sha(b"payload" + len(RUN["blocks"]).to_bytes(4, "little"))
        made.parent_hash = above.body.execution_payload.block_hash
        made.block_number = len(RUN["blocks"])
    root = block.hash_tree_root()
    RUN["blocks"].append(block)
    RUN["roots"].append(root)
    try:
        candidate = is_candidate(spec, store, clock, block)
        verdict = "t" if candidate else "f"
    except Exception:
        candidate, verdict = False, "e"
    # A block on a parent that the fork choice dropped is not imported.
    known = bytes(RUN["roots"][parent]) in RUN["held"]
    if known and (not optimistic or candidate):
        store.blocks[root] = block
        RUN["held"].add(bytes(root))
        if optimistic:
            store.optimistic_roots.add(root)
        else:
            valid(root)
    return "\t".join([block.encode_bytes().hex(), verdict, view()])


def names_latest_valid(spec, latest, block):
    """Whether a hash names the payload of a block; the zero hash names the empty payload."""
    payload = block.body.execution_payload
    empty = payload == type(payload)()
    if latest == bytes(32):
        return empty
    return not empty and bytes(payload.block_hash) == latest


def invalid(index, kind):
    spec, store = RUN["spec"], RUN["store"]
    block, root = RUN["blocks"][index], RUN["roots"][index]
    chain = []
    walk = block.parent_root
    while walk in store.blocks and bytes(walk) in RUN["held"]:
        chain.append(walk)
        walk = store.blocks[walk].parent_root
    if kind == 0:
        latest = None
    elif kind == 100:
        latest = bytes(block.body.execution_payload.block_hash)
    elif kind == 101:
        latest = sha(b"a hash that no block has")
    elif kind == 102:
        latest = bytes(32)
    else:
        named = store.blocks[chain[min(kind, len(chain)) - 1]] if chain else block
        latest = bytes(named.body.execution_payload.block_hash)
    shown = latest.hex() if latest is not None else "-"
    first = root
    if latest is not None:
        if names_latest_valid(spec, latest, block):
            first = None
        else:
            child = root
            for ancestor in chain:
                if names_latest_valid(spec, latest, store.blocks[ancestor]):
                    first = child
                    break
                child = ancestor
    if first is not None and bytes(first) in RUN["held"]:
        dropped = set()
        for raw in RUN["held"]:
            walk = spec.Root(raw)
            while walk in store.blocks:
                if walk == first:
                    dropped.add(raw)
                    break
                walk = store.blocks[walk].parent_root
        RUN["held"] -= dropped
        store.optimistic_roots -= {spec.Root(raw) for raw in dropped}
    return "\t".join([block.encode_bytes().hex(), shown, view()])


def answer(words):
    match words:
        case ["po_init", fork]:
            return init(fork)
        case ["po_import", parent, gap, payload, clock, optimistic]:
            return import_block(
                int(parent), int(gap), payload == "1", int(clock), optimistic == "1"
            )
        case ["po_valid", index]:
            root = RUN["roots"][int(index)]
            if bytes(root) in RUN["held"]:
                valid(root)
            return bytes(root).hex() + "\t" + view()
        case ["po_invalid", index, kind]:
            return invalid(int(index), int(kind))
    raise ValueError(words[0])

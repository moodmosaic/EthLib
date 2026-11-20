"""The store of inclusion lists of Heze (EIP-7805), driven by commands."""

#     pi_init <preset>
#     pi_receive <slot> <root> <member> <transactions> <timely>
#         A signed inclusion list, then the view.  The transactions are numbers of a small
#         pool, separated by commas, so that two lists share some.
#     pi_bits <slot> <root> <committee> <bits>
#         The bits of the store for a committee, and whether the given bits include them, for
#         timely lists and for all: "<bits> <inclusive> <bits> <inclusive>".
#
# For each slot and root that got a list, the view lists the members and the equivocators.
# It also lists the transactions that count, sorted, for timely lists and for all.

import hashlib
from collections import defaultdict

import protocols_spec as presets

RUN = {}


def root_of(number):
    return hashlib.sha256(b"dependent" + bytes([number])).digest()


def transaction(spec, number):
    """A transaction of the pool: a few bytes, the first of them empty."""
    data = bytes([number]) * (number % 5) if number else b""
    return spec.Transactions.ELEMENT_TYPE(data=list(data))


def raw(item):
    """The bytes of a transaction, whose type is a list of bytes."""
    return bytes(int(b) for b in item)


def view():
    spec, store = RUN["spec"], RUN["store"]
    parts = []
    for key in sorted(store.inclusion_lists, key=lambda k: (int(k[0]), bytes(k[1]))):
        slot, root = key
        if not store.inclusion_lists[key]:
            continue
        members = ",".join(str(int(m)) for m in store.inclusion_lists[key])
        equivocators = ",".join(str(int(m)) for m in sorted(store.equivocators[key]))
        shown = []
        for only_timely in (True, False):
            found = spec.get_inclusion_list_transactions(store, slot, root, only_timely)
            shown.append(",".join(sorted(raw(t).hex() or "-" for t in found)))
        parts.append(
            f"{int(slot)}:{bytes(root).hex()[:8]}:{members}:{equivocators}:{shown[0]}:{shown[1]}"
        )
    return " ".join(parts) or "-"


def receive(slot, root, member, numbers, timely):
    spec, store = RUN["spec"], RUN["store"]
    made = [transaction(spec, int(n)) for n in numbers.split(",")] if numbers != "-" else []
    signed = spec.SignedInclusionList(
        message=spec.InclusionList(
            slot=slot,
            validator_index=member,
            dependent_root=root_of(root),
            transactions=spec.Transactions(data=made),
        ),
        signature=hashlib.sha256(numbers.encode()).digest() * 3,
    )
    spec.process_inclusion_list(store, signed, timely)
    return signed.encode_bytes().hex() + "\t" + view()


def bits(slot, root, committee, given):
    spec, store = RUN["spec"], RUN["store"]
    members = spec.InclusionListCommittee(data=[int(m) for m in committee.split(",")])
    wanted = spec.InclusionListBits(data=[b == "1" for b in given.split(",")])
    out = []
    for only_timely in (True, False):
        own = spec.get_inclusion_list_bits(store, members, slot, root_of(root), only_timely)
        inclusive = spec.is_inclusion_list_bits_inclusive(
            store, members, slot, root_of(root), wanted, only_timely
        )
        out.append("".join("1" if b else "0" for b in own))
        out.append("t" if inclusive else "f")
    return " ".join(out)


def answer(words):
    match words:
        case ["pi_init", preset]:
            spec = presets.configure_chain("heze", preset, "-")
            RUN.clear()
            RUN.update(
                spec=spec,
                store=spec.InclusionListStore(
                    inclusion_lists=defaultdict(dict), equivocators=defaultdict(set)
                ),
            )
            return view()
        case ["pi_receive", slot, root, member, numbers, timely]:
            return receive(int(slot), int(root), int(member), numbers, timely == "1")
        case ["pi_bits", slot, root, committee, given]:
            return bits(int(slot), int(root), committee, given)
    raise ValueError(words[0])

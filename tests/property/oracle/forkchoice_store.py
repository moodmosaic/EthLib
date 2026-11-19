"""The fork choice of the pyspec, driven by abstract commands.

The oracle builds every object (blocks, attestations, slashings) with the
pyspec, runs the handler of the pyspec on it, and answers with the steps it
ran and a view of its store.  A step is `<kind>:<argument>:<status>`:

    t:<ms>:<status>       on_tick at an absolute time
    b:<hex>:<status>      on_block of a SignedBeaconBlock
    a:<hex>:<status>      on_attestation from the wire
    A:<hex>:<status>      on_attestation from a block
    s:<hex>:<status>      on_attester_slashing
    e:<hex>:<status>      on_execution_payload_envelope, from Gloas
    p:<hex>:<status>      on_payload_attestation_message, from Gloas
    gb:<hex>:-:<ms>:<verdict>          validate_beacon_block_gossip
    ga:<hex>:<subnet>:<ms>:<verdict>   validate_beacon_attestation_gossip
    gg:<hex>:-:<ms>:<verdict>          validate_beacon_aggregate_and_proof_gossip
    gs:<hex>:-:<ms>:<verdict>          validate_attester_slashing_gossip
    ge:<hex>:-:<ms>:<verdict>          validate_execution_payload_envelope_gossip
    gp:<hex>:-:<ms>:<verdict>          validate_payload_attestation_message_gossip

A verdict is accept, ignore, reject, or error when the pyspec raises
something else.  The gossip checks share one `Seen` for the whole run.

The driver runs the same steps on EthLib and compares each status and the
view.  BLS is off on both sides.
"""

import atexit
import collections
import dataclasses
import hashlib
import importlib
import inspect
import os
import sys
import traceback

from eth_consensus_specs.test.helpers.attestations import get_valid_attestation
from eth_consensus_specs.test.helpers.block import build_empty_block
from eth_consensus_specs.test.helpers.execution_payload import (
    build_signed_execution_payload_envelope,
)
from eth_consensus_specs.test.helpers.genesis import create_genesis_state
from eth_consensus_specs.utils import bls

ETH = 10**9

# What the runs reached, printed at exit when FC_STATS is set: look before you trust.
STATS = collections.Counter()
if os.environ.get("FC_STATS"):
    atexit.register(lambda: print(sorted(STATS.items()), file=sys.stderr))


def tohex(data):
    return data.hex() if data else "-"


class Entry:
    """A block the oracle built: its root, slot, and state if it is valid."""

    def __init__(self, signed, state):
        self.signed = signed
        self.root = signed.message.hash_tree_root()
        self.slot = int(signed.message.slot)
        self.state = state


class ForkChoice:
    def __init__(self, fork, count, variant, loose):
        bls.bls_active = False
        # A loose run keeps the votes whose committee index is out of range.
        self.loose = loose
        self.spec = importlib.import_module(f"eth_consensus_specs.{fork}.minimal")
        spec = self.spec
        # Every fork up to this one is active from genesis, as in the driver.
        order = ["altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas"]
        self.gloas = fork == "gloas"
        active = order[: order.index(fork) + 1] if fork in order else []
        spec.config = spec.config._replace(**{f"{name.upper()}_FORK_EPOCH": 0 for name in active})
        check = getattr(spec, "is_data_available", None)
        names = inspect.signature(check).parameters if check else []
        if "blob_kzg_commitments" in names and not hasattr(spec, "patched"):
            spec.patched = True
            # At Deneb and Electra the KZG wrapper of the pyspec takes no empty batch.
            # No block here has a blob, and the empty batch verifies by definition.
            real = spec.is_data_available
            spec.is_data_available = lambda root, commitments: (
                len(commitments) == 0 or real(root, commitments)
            )
        top = int(spec.MAX_EFFECTIVE_BALANCE)
        balances = [top] * count
        if variant & 1:
            # Unequal weights: a validator below the others, in whole ETH.
            for i in range(0, count, 3):
                balances[i] = top - (1 + i % 7) * ETH
        state = create_genesis_state(spec, balances, 16 * ETH)
        if variant & 2:
            # A validator slashed in the anchor state has no weight.
            state.validators[count - 1].slashed = True
        if variant & 4:
            # A validator that is not active yet has no weight either.
            far = spec.FAR_FUTURE_EPOCH
            state.validators[count - 2].activation_epoch = far
        anchor = spec.BeaconBlock(state_root=state.hash_tree_root())
        if self.gloas:
            # The bid of the anchor is the one that its state commits to.
            anchor.body.signed_execution_payload_bid.message = state.latest_execution_payload_bid
        self.store = spec.get_forkchoice_store(state, anchor)
        self.count = count
        self.seen = spec.Seen(
            **{
                f.name: ({} if str(f.type).startswith("dict") else set())
                for f in dataclasses.fields(spec.Seen)
            }
        )
        # How far the clock of gossip runs ahead of the clock of the store.
        self.ahead = 0
        signed = spec.SignedBeaconBlock(message=anchor)
        self.blocks = [Entry(signed, state)]
        self.anchor_state = state

    def init_answer(self):
        state = self.anchor_state
        block = self.blocks[0].signed.message
        return [tohex(state.encode_bytes()), tohex(block.encode_bytes()), self.view()]

    # Steps: run a handler of the pyspec, and record what it said.

    def run(self, kind, arg, handler):
        try:
            handler()
            status = "ok"
        except Exception:
            status = "error"
        STATS[f"{kind} {status}"] += 1
        return f"{kind}:{arg}:{status}"

    def gossip(self, kind, message, subnet, validate):
        """A gossip check of the pyspec at the clock of gossip, and its verdict."""
        spec = self.spec
        time_ms = int(self.store.time_ms) + self.ahead
        args = {}
        names = list(inspect.signature(validate).parameters)
        if "current_time_ms" in names:
            args["current_time_ms"] = time_ms
        if "block_payload_statuses" in names:
            args["block_payload_statuses"] = {}
        if "subnet_id" in names:
            args["subnet_id"] = subnet
        try:
            validate(self.seen, self.store, message, **args)
            verdict = "accept"
        except spec.GossipIgnore:
            verdict = "ignore"
        except spec.GossipReject:
            verdict = "reject"
        except Exception as error:
            verdict = "error"
            if os.environ.get("FC_DEBUG"):
                frame = traceback.extract_tb(error.__traceback__)[-1]
                print(f"g{kind}: {type(error).__name__} in {frame.name}", file=sys.stderr)
        STATS[f"g{kind} {verdict}"] += 1
        shown = "-" if subnet is None else subnet
        return f"g{kind}:{tohex(message.encode_bytes())}:{shown}:{time_ms}:{verdict}"

    def tick(self, time_ms):
        spec = self.spec
        return self.run("t", time_ms, lambda: spec.on_tick(self.store, time_ms))

    def on_block(self, signed):
        spec = self.spec
        steps = [
            self.gossip("b", signed, None, spec.validate_beacon_block_gossip),
            self.run("b", tohex(signed.encode_bytes()), lambda: spec.on_block(self.store, signed)),
        ]
        if steps[1].endswith(":ok"):
            # A node also runs the operations of a block through their handlers.
            for attestation in signed.message.body.attestations:
                steps.append(self.attestation(attestation, True))
            for slashing in signed.message.body.attester_slashings:
                steps.append(self.slashing(slashing))
        return steps

    def attestation_gossip(self, attestation, state, mask):
        """The gossip of a vote: one attester on its subnet, then the aggregate."""
        spec = self.spec
        data = attestation.data
        steps = []
        try:
            epoch = spec.compute_epoch_at_slot(data.slot)
            per_slot = spec.get_committee_count_per_slot(state, epoch)
            single = hasattr(spec, "SingleAttestation")
            if single:
                committee_index = int(spec.get_committee_indices(attestation.committee_bits)[0])
            else:
                committee_index = int(data.index)
            committee = list(spec.get_beacon_committee(state, data.slot, committee_index))
            members = sorted(int(i) for i in spec.get_attesting_indices(state, attestation))
            subnet = int(spec.compute_subnet_for_attestation(per_slot, data.slot, committee_index))
        except Exception:
            return steps
        variant = (mask >> 4) % 8
        for attester in members[:2] if variant != 7 else members[:1] * 2:
            if variant == 5:
                attester = (attester + 1) % self.count
            if single:
                message = spec.SingleAttestation(
                    committee_index=committee_index + (variant == 6),
                    attester_index=attester,
                    data=data,
                )
            else:
                message = attestation.copy()
                bits = [v == attester for v in committee]
                message.aggregation_bits = type(message.aggregation_bits)(data=bits)
            steps.append(
                self.gossip(
                    "a",
                    message,
                    subnet + (variant == 4),
                    spec.validate_beacon_attestation_gossip,
                )
            )
        aggregator = committee[mask % len(committee)] if variant != 3 else mask % self.count
        proof = spec.AggregateAndProof(
            aggregator_index=aggregator,
            aggregate=attestation,
            selection_proof=spec.BLSSignature(bytes([mask % 256]) * 96),
        )
        signed = spec.SignedAggregateAndProof(message=proof)
        check = spec.validate_beacon_aggregate_and_proof_gossip
        steps.append(self.gossip("g", signed, None, check))
        if variant == 2:
            # The same aggregate again: its bits are covered now, if it was valid.
            steps.append(self.gossip("g", signed, None, check))
        return steps

    def attestation(self, attestation, from_block):
        spec = self.spec
        return self.run(
            "A" if from_block else "a",
            tohex(attestation.encode_bytes()),
            lambda: spec.on_attestation(self.store, attestation, from_block),
        )

    def slashing(self, slashing):
        spec = self.spec
        return self.run(
            "s",
            tohex(slashing.encode_bytes()),
            lambda: spec.on_attester_slashing(self.store, slashing),
        )

    def shape_ok(self, attestation):
        """Whether a vote has the committee shape that `process_attestation` asks.

        EthLib's `onAttestation` asks it of every vote, and `on_attestation`
        of the pyspec of none.  A strict run leaves such votes out.
        """
        spec, store = self.spec, self.store
        data = attestation.data
        if data.target.root not in store.block_states:
            return True
        try:
            state = store.block_states[data.target.root].copy()
            start = spec.compute_start_slot_at_epoch(data.target.epoch)
            if state.slot < start:
                spec.process_slots(state, start)
            count = spec.get_committee_count_per_slot(state, data.target.epoch)
            bits = attestation.aggregation_bits
            if not hasattr(attestation, "committee_bits"):
                if data.index >= count:
                    return False
                committee = spec.get_beacon_committee(state, data.slot, data.index)
                return len(bits) == len(committee)
            if data.index >= (2 if self.gloas else 1):
                return False
            offset = 0
            for index in spec.get_committee_indices(attestation.committee_bits):
                if index >= count:
                    return False
                committee = spec.get_beacon_committee(state, data.slot, index)
                if not any(bits[offset + i] for i in range(len(committee))):
                    return False
                offset += len(committee)
            return len(bits) == offset
        except Exception:
            return False

    # Builders.

    def build_block(self, parent_index, slot, variant, lookback):
        """A block on a parent at a slot, with the votes of the slots before it.

        The entry is appended even when the block cannot be built, so that
        the index of a block does not depend on what the pyspec accepts.
        """
        spec = self.spec
        parent = self.blocks[parent_index]
        self.blocks.append(None)
        if parent is None or parent.state is None or slot <= parent.slot:
            return None
        try:
            state = parent.state.copy()
            spec.process_slots(state, slot)
            block = build_empty_block(spec, state, slot)
            if self.gloas:
                # A payload of its own, on the payload of the parent or without it.
                bid = block.body.signed_execution_payload_bid.message
                seed = b"payload" + slot.to_bytes(8, "little") + bytes(block.parent_root)
                bid.block_hash = spec.Hash32(hashlib.sha256(seed).digest())
                parent_bid = parent.signed.message.body.signed_execution_payload_bid.message
                revealed = parent.root in self.store.payloads
                if variant == 4 or (variant == 0 and revealed and slot % 4 != 3):
                    bid.parent_block_hash = parent_bid.block_hash
            electra = hasattr(block.body, "execution_requests")
            limit = int(spec.MAX_ATTESTATIONS_ELECTRA if electra else spec.MAX_ATTESTATIONS)
            first = max(slot - lookback, parent.slot, 0)
            for vote_slot in range(first, slot):
                if vote_slot + int(spec.MIN_ATTESTATION_INCLUSION_DELAY) > slot:
                    continue
                if vote_slot + int(spec.SLOTS_PER_EPOCH) < slot:
                    continue
                epoch = spec.compute_epoch_at_slot(vote_slot)
                for committee in range(int(spec.get_committee_count_per_slot(state, epoch))):
                    if len(block.body.attestations) < limit:
                        block.body.attestations.append(
                            get_valid_attestation(spec, state, vote_slot, committee)
                        )
            spec.process_block(state, block)
            block.state_root = state.hash_tree_root()
        except Exception:
            return None
        if variant == 1:
            # A wrong state root: the transition refuses the block.
            block.state_root = spec.Root(b"\x13" * 32)
            state = None
        elif variant == 2:
            # A wrong proposer.
            block.proposer_index = (int(block.proposer_index) + 1) % self.count
            state = None
        elif variant == 3:
            # An unknown parent.
            block.parent_root = spec.Root(b"\x17" * 32)
            state = None
        signed = spec.SignedBeaconBlock(message=block)
        self.blocks[-1] = Entry(signed, state)
        return signed

    def build_attestation(self, block_index, delta, committee, mask, mutation):
        spec = self.spec
        entry = self.blocks[block_index]
        if entry is None or entry.state is None:
            return None
        try:
            state = entry.state.copy()
            slot = entry.slot + delta
            if state.slot < slot:
                spec.process_slots(state, slot)
            epoch = spec.compute_epoch_at_slot(slot)
            if not self.loose:
                committee %= int(spec.get_committee_count_per_slot(state, epoch))
            keep = lambda members: {  # noqa: E731
                v for i, v in enumerate(sorted(members)) if mask >> (i % 16) & 1
            }
            attestation = get_valid_attestation(
                spec,
                state,
                slot,
                committee,
                filter_participant_set=keep,
                beacon_block_root=entry.root,
            )
        except Exception:
            return None
        self.vote_state = state
        data = attestation.data
        others = [e for e in self.blocks if e is not None]
        other = others[mask % len(others)]
        try:
            if mutation == 1:
                data.target.root = other.root
            elif mutation == 2:
                data.target.epoch += 1
            elif mutation == 3:
                data.beacon_block_root = spec.Root(b"\x19" * 32)
            elif mutation == 4:
                data.slot = max(int(data.slot), 1) - 1
            elif mutation == 5:
                data.index += 1
            elif mutation == 6:
                bits = list(attestation.aggregation_bits) + [True]
                attestation.aggregation_bits = type(attestation.aggregation_bits)(data=bits)
            elif mutation == 7:
                bits = list(attestation.aggregation_bits)[:-1]
                attestation.aggregation_bits = type(attestation.aggregation_bits)(data=bits)
            elif mutation == 8:
                bits = [False] * len(attestation.aggregation_bits)
                attestation.aggregation_bits = type(attestation.aggregation_bits)(data=bits)
            elif mutation == 9:
                data.source.epoch += 1
            elif mutation == 10:
                data.beacon_block_root = other.root
            elif mutation == 11 and hasattr(attestation, "committee_bits"):
                attestation.committee_bits[1] = not attestation.committee_bits[1]
            elif mutation == 12 and hasattr(attestation, "committee_bits"):
                attestation.committee_bits[0] = False
            elif mutation == 14 and self.gloas:
                data.index = 1
            elif mutation == 13:
                data.target.epoch = max(int(data.target.epoch), 1) - 1
        except Exception:
            return None
        return attestation

    def build_slashing(self, index1, index2, mask, mutation):
        spec = self.spec
        first, second = self.blocks[index1], self.blocks[index2]
        if first is None or second is None or first.state is None or second.state is None:
            return None
        try:
            data1 = get_valid_attestation(spec, first.state, first.slot, 0).data
            data2 = get_valid_attestation(spec, second.state, second.slot, 0).data
        except Exception:
            return None
        indices = [i for i in range(self.count) if mask >> (i % 20) & 1]
        other = list(indices)
        if mutation == 1:
            indices = indices[::-1]
        elif mutation == 2:
            indices = indices + indices[-1:]
        elif mutation == 3:
            indices = []
        elif mutation == 4:
            other = other + [self.count]
        elif mutation == 5:
            # A surround vote: the second surrounds the first.
            data1.source.epoch, data1.target.epoch = 1, 2
            data2.source.epoch, data2.target.epoch = 0, 3
        elif mutation == 6:
            data2 = data1.copy()
        elif mutation == 7:
            # Half of the validators in the second vote only.
            other = other[::2]
        elif mutation == 8:
            data2 = data1.copy()
            data2.source.epoch += 1
        try:
            return spec.AttesterSlashing(
                attestation_1=spec.IndexedAttestation(
                    attesting_indices=spec.AttestingIndices(data=indices), data=data1
                ),
                attestation_2=spec.IndexedAttestation(
                    attesting_indices=spec.AttestingIndices(data=other), data=data2
                ),
            )
        except Exception:
            return None

    # Commands.

    def cmd_tick(self, time_ms):
        return [self.tick(int(time_ms))]

    def cmd_block(self, parent, slot, variant, lookback):
        signed = self.build_block(int(parent), int(slot), int(variant), int(lookback))
        return ["skip"] if signed is None else self.on_block(signed)

    def cmd_again(self, index):
        entry = self.blocks[int(index)]
        return ["skip"] if entry is None else self.on_block(entry.signed)

    def cmd_chain(self, parent, parent_slot, count, gap, late_ms):
        """Blocks one after another, each in its slot, with the votes before it.

        It always ticks and appends `count` times, so that the clock and the
        indices do not depend on what the pyspec accepts.
        """
        spec = self.spec
        steps = []
        index = int(parent)
        now = int(spec.get_current_slot(self.store))
        slot = max(int(parent_slot), now)
        duration = int(spec.config.SLOT_DURATION_MS)
        for _ in range(int(count)):
            slot += 1 + int(gap)
            time_ms = int(self.store.genesis_time_ms) + slot * duration + int(late_ms)
            steps.append(self.tick(time_ms))
            signed = self.build_block(index, slot, 0, 2)
            if signed is not None:
                index = len(self.blocks) - 1
                steps += self.on_block(signed)
                if self.gloas and slot % 5 != 4:
                    steps += self.cmd_envelope(index, 0)
        return steps

    def cmd_attest(self, block, delta, committee, mask, mutation):
        attestation = self.build_attestation(
            int(block), int(delta), int(committee), int(mask), int(mutation)
        )
        if attestation is None:
            return ["skip"]
        steps = self.attestation_gossip(attestation, self.vote_state, int(mask))
        if self.loose or self.shape_ok(attestation):
            steps.append(self.attestation(attestation, False))
        return steps or ["skip"]

    def cmd_slash(self, index1, index2, mask, mutation):
        slashing = self.build_slashing(int(index1), int(index2), int(mask), int(mutation))
        if slashing is None:
            return ["skip"]
        check = self.spec.validate_attester_slashing_gossip
        return [self.gossip("s", slashing, None, check), self.slashing(slashing)]

    def cmd_envelope(self, index, mutation):
        """From Gloas: the envelope that reveals the payload of a block."""
        spec = self.spec
        entry = self.blocks[int(index)]
        if not self.gloas or entry is None or entry.state is None:
            return ["skip"]
        try:
            signed = build_signed_execution_payload_envelope(
                spec, entry.state, entry.root, entry.signed
            )
            mutation = int(mutation)
            if mutation == 1:
                signed.message.payload.block_hash = spec.Hash32(b"\x21" * 32)
            elif mutation == 2:
                signed.message.beacon_block_root = spec.Root(b"\x23" * 32)
            elif mutation == 3:
                signed.message.builder_index = 1
            elif mutation == 4:
                signed.message.payload.gas_limit += 1
            elif mutation == 5:
                signed.message.parent_beacon_block_root = spec.Root(b"\x25" * 32)
        except Exception:
            return ["skip"]
        check = spec.validate_execution_payload_envelope_gossip
        handler = lambda: spec.on_execution_payload_envelope(self.store, signed)  # noqa: E731
        return [
            self.gossip("e", signed, None, check),
            self.run("e", tohex(signed.encode_bytes()), handler),
        ]

    def cmd_ptc(self, index, member, flags, delta):
        """From Gloas: a vote of a member of the payload committee on a block."""
        spec = self.spec
        entry = self.blocks[int(index)]
        if not self.gloas or entry is None or entry.state is None:
            return ["skip"]
        try:
            ptc = list(spec.get_ptc(entry.state, entry.slot))
            member, flags = int(member), int(flags)
            voter = ptc[member % len(ptc)] if member < 100 else member % self.count
            message = spec.PayloadAttestationMessage(
                validator_index=voter,
                data=spec.PayloadAttestationData(
                    beacon_block_root=entry.root if flags < 4 else spec.Root(b"\x27" * 32),
                    slot=entry.slot + int(delta),
                    payload_present=bool(flags & 1),
                    blob_data_available=bool(flags & 2),
                ),
            )
        except Exception:
            return ["skip"]
        check = spec.validate_payload_attestation_message_gossip
        handler = lambda: spec.on_payload_attestation_message(self.store, message, False)  # noqa: E731
        return [
            self.gossip("p", message, None, check),
            self.run("p", tohex(message.encode_bytes()), handler),
        ]

    def cmd_ahead(self, ahead_ms):
        self.ahead = int(ahead_ms)
        return []

    # The view of the store that the driver compares.

    def view(self):
        spec, store = self.spec, self.store

        def checkpoint(c):
            return f"{int(c.epoch)}:{bytes(c.root).hex()}"

        def status(node):
            return int(getattr(node, "payload_status", 2))

        try:
            node = spec.get_head(store)
            head = bytes(node.root).hex()
            head_status = str(status(node))
        except Exception:
            head = head_status = "error"
        weights = []
        for root in sorted(bytes(r) for r in store.blocks):
            # The pending node of each block, and from Gloas its empty and its full node.
            for code in [2, 0, 1] if self.gloas else [2]:
                label = f"{root.hex()[:8]}.{code}"
                try:
                    if self.gloas:
                        node = spec.ForkChoiceNode(root=root, payload_status=code)
                    else:
                        node = spec.ForkChoiceNode(root=root)
                    weights.append(f"{label}:{int(spec.get_weight(store, node))}")
                except Exception:
                    weights.append(f"{label}:error")
        messages = [
            f"{int(i)}:{int(m.slot if self.gloas else m.epoch)}:{bytes(m.root).hex()[:8]}"
            f":{int(getattr(m, 'payload_present', False))}"
            for i, m in sorted(store.latest_messages.items())
        ]

        def flag(test):
            try:
                return "t" if test() else "f"
            except Exception:
                return "e"

        # What a proposer of the current slot builds on, and each test behind that choice.
        slot = spec.get_current_slot(store)
        try:
            node = spec.get_head(store)
            chosen = spec.get_proposer_head(store, node, slot)
            proposer_head = f"{bytes(chosen.root).hex()[:8]}.{status(chosen)}"
        except Exception:
            proposer_head = "error"
        try:
            root = spec.get_head(store).root
            parent = store.blocks[root].parent_root
        except Exception:
            root = parent = None
        tests = "".join(
            [
                flag(lambda: spec.is_head_late(store, root)),
                flag(lambda: spec.is_ffg_competitive(store, root, parent)),
                flag(lambda: spec.is_finalization_ok(store, slot)),
                flag(lambda: spec.is_proposing_on_time(store)),
                flag(lambda: spec.is_head_weak(store, root)),
                flag(lambda: spec.is_parent_strong(store, root)),
                flag(lambda: spec.is_proposer_equivocation(store, root)),
            ]
        )

        # Helpers of a validator and of a full node, on the state after the head.
        def text(compute):
            try:
                return compute()
            except Exception:
                return "error"

        state = store.block_states.get(root)

        def assignment(ahead, validator):
            found = spec.get_committee_assignment(
                state, spec.get_current_epoch(state) + ahead, validator
            )
            if found is None:
                return "none"
            return f"{len(found[0])}/{int(found[1])}/{int(found[2])}"

        def bootstrap():
            block = store.blocks[root]
            made = spec.create_light_client_bootstrap(state, spec.SignedBeaconBlock(message=block))
            spec.initialize_light_client_store(block.hash_tree_root(), made)
            return bytes(made.hash_tree_root()).hex()[:8]

        def weak_subjectivity():
            if hasattr(spec, "get_consolidation_churn_limit"):
                return str(int(spec.compute_weak_subjectivity_period(state)))
            # Before Electra the function of the pyspec mixes its integer types and raises.
            # So this is its text, in plain integers.
            epoch = spec.get_current_epoch(state)
            count = len(spec.get_active_validator_indices(state, epoch))
            average = int(spec.get_total_active_balance(state)) // count // int(spec.ETH_TO_GWEI)
            top = int(spec.MAX_EFFECTIVE_BALANCE) // int(spec.ETH_TO_GWEI)
            churn_limit = int(spec.get_validator_churn_limit(state))
            deposits = int(spec.MAX_DEPOSITS) * int(spec.SLOTS_PER_EPOCH)
            decay = int(spec.SAFETY_DECAY)
            period = int(spec.config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY)
            if average * (200 + 12 * decay) > top * (200 + 3 * decay):
                churn = (
                    count
                    * (average * (200 + 12 * decay) - top * (200 + 3 * decay))
                    // (600 * churn_limit * (2 * average + top))
                )
                top_ups = count * (200 + 3 * decay) // (600 * deposits)
                return str(period + max(churn, top_ups))
            return str(period + 3 * count * decay * average // (200 * deposits * (top - average)))

        period = text(weak_subjectivity)
        duties = ",".join(
            [
                text(lambda: assignment(0, 0)),
                text(lambda: assignment(1, 1)),
                text(lambda: assignment(2, 2)),
                text(lambda: assignment(0, len(store.blocks) % 16)),
                text(lambda: assignment(1, 1000)),
            ]
        )
        light = text(bootstrap)
        STATS["bootstraps"] += light != "error"
        STATS["proposer head is the parent"] += proposer_head[:8] not in ("error", head[:8])
        STATS["head is full"] += head_status == "1"
        STATS["views"] += 1
        STATS["justified > 0"] += store.justified_checkpoint.epoch > 0
        STATS["finalized > 0"] += store.finalized_checkpoint.epoch > 0
        STATS["equivocators"] += len(store.equivocating_indices) > 0
        STATS["boosted"] += store.proposer_boost_root != spec.Root()
        tips = {bytes(r) for r in store.blocks} - {
            bytes(b.parent_root) for b in store.blocks.values()
        }
        STATS["forked"] += len(tips) > 1
        return " ".join(
            [
                f"h={head}",
                f"hs={head_status}",
                f"j={checkpoint(store.justified_checkpoint)}",
                f"f={checkpoint(store.finalized_checkpoint)}",
                f"uj={checkpoint(store.unrealized_justified_checkpoint)}",
                f"uf={checkpoint(store.unrealized_finalized_checkpoint)}",
                f"b={bytes(store.proposer_boost_root).hex()[:8]}",
                f"ph={proposer_head}",
                f"pt={tests}",
                f"ws={period}",
                f"ca={duties}",
                f"lc={light}",
                f"t={int(store.time_ms)}",
                f"n={len(store.blocks)}",
                "eq=" + ",".join(str(int(i)) for i in sorted(store.equivocating_indices)),
                "lm=" + ",".join(messages),
                "w=" + ",".join(weights),
            ]
        )


CURRENT = None


def mutate(spec, mutant):
    """Break the pyspec on purpose, to see that the driver notices."""
    if mutant == "tie":
        # A tie between two children goes to the lesser root.
        def get_head(store):
            nodes = spec.get_filtered_node_tree(store)
            head = spec.ForkChoiceNode(root=store.justified_checkpoint.root)
            while True:
                children = [c for c in spec.get_node_children(store, head) if c in nodes]
                if len(children) == 0:
                    return head
                best = max(spec.get_weight(store, c) for c in children)
                head = min(
                    (c for c in children if spec.get_weight(store, c) == best),
                    key=lambda c: c.root,
                )

        spec.get_head = get_head
    elif mutant == "boost":
        # The boost is a percent less.
        spec.config = spec.config._replace(
            PROPOSER_SCORE_BOOST=spec.config.PROPOSER_SCORE_BOOST - 1
        )
    elif mutant == "newer":
        # A vote of the same epoch replaces the latest one.
        def update_latest_messages(store, attesting_indices, attestation):
            target = attestation.data.target
            root = attestation.data.beacon_block_root
            for i in set(attesting_indices) - store.equivocating_indices:
                if i not in store.latest_messages or target.epoch >= store.latest_messages[i].epoch:
                    store.latest_messages[i] = spec.LatestMessage(epoch=target.epoch, root=root)

        spec.update_latest_messages = update_latest_messages
    elif mutant == "viable":
        # A voting source one epoch older is still viable.
        original = spec.get_voting_source

        def get_voting_source(store, block_root):
            source = original(store, block_root).copy()
            source.epoch += 1
            return source

        spec.get_voting_source = get_voting_source


def answer(words):
    """One fork choice command: the steps that ran, then the view."""
    global CURRENT
    match words:
        case ["fc_init", fork, count, variant, loose]:
            CURRENT = ForkChoice(fork, int(count), int(variant), loose == "1")
            if os.environ.get("FC_MUTANT") and not hasattr(CURRENT.spec, "mutated"):
                CURRENT.spec.mutated = True
                mutate(CURRENT.spec, os.environ["FC_MUTANT"])
            return "\t".join(CURRENT.init_answer())
        case [name, *args]:
            steps = getattr(CURRENT, "cmd_" + name[3:])(*args)
            return "\t".join(steps + [CURRENT.view()])

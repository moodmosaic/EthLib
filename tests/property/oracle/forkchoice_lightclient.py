"""The light client store of the pyspec, driven by abstract commands."""

#     lc_init <fork> <start slot>
#         A store from a bootstrap: the bootstrap, the trusted root, the digest.
#     lc_update <attested> <signature> <finalized or -1> <committee> <signers> <mutation> <now>
#         An update with real branches, processed at slot `now`: its bytes, the
#         verdict and the digest.
#     lc_force <now>
#         process_light_client_store_force_update: the verdict and the digest.
#
# The oracle builds each update from one template state.
# It sets the finalized root and next sync committee of that state.
# It sets them so that the branches of the update are true.
# BLS is off, so the signers are only counted.

import atexit
import collections
import importlib
import os
import sys

from eth_consensus_specs.test.helpers.genesis import create_genesis_state
from eth_consensus_specs.utils import bls

# What the runs reached, printed at exit when FC_STATS is set.
STATS = collections.Counter()
if os.environ.get("FC_STATS"):
    atexit.register(lambda: STATS and print(sorted(STATS.items()), file=sys.stderr))

ORDER = ["altair", "bellatrix", "capella", "deneb", "electra", "fulu"]


class LightClient:
    def __init__(self, fork, start):
        bls.bls_active = False
        self.spec = spec = importlib.import_module(f"eth_consensus_specs.{fork}.minimal")
        active = ORDER[: ORDER.index(fork) + 1]
        spec.config = spec.config._replace(**{f"{name.upper()}_FORK_EPOCH": 0 for name in active})
        if os.environ.get("FC_MUTANT") == "better" and not hasattr(spec, "mutated"):
            # Break the pyspec on purpose, to see that the driver notices.
            spec.mutated = True
            real = spec.is_better_update
            spec.is_better_update = lambda new, old: real(old, new)
        top = int(spec.MAX_EFFECTIVE_BALANCE)
        self.state = create_genesis_state(spec, [top] * 16, top)
        header = self.header(start, self.state)
        gindex = spec.current_sync_committee_gindex_at_slot(start)
        self.bootstrap = spec.LightClientBootstrap(
            header=header,
            current_sync_committee=self.state.current_sync_committee,
            current_sync_committee_branch=spec.CurrentSyncCommitteeBranch(
                data=spec.compute_merkle_proof(self.state, gindex)
            ),
        )
        self.trusted = header.beacon.hash_tree_root()
        self.store = spec.initialize_light_client_store(self.trusted, self.bootstrap)

    def header(self, slot, state):
        """The light client header of an empty block at a slot, after a state."""
        spec = self.spec
        block = spec.BeaconBlock(slot=slot, state_root=state.hash_tree_root())
        return spec.block_to_light_client_header(spec.SignedBeaconBlock(message=block))

    def update(self, attested, signature, finalized, committee, signers, mutation):
        spec = self.spec
        state = self.state.copy()
        if committee == 2:
            # Another committee than the one the store may know.
            other = state.next_sync_committee.copy()
            other.aggregate_pubkey = spec.BLSPubkey(b"\x05" * 48)
            state.next_sync_committee = other
        finalized_header = spec.LightClientHeader()
        if finalized > 0:
            finalized_header = self.header(finalized, self.state)
            state.finalized_checkpoint.root = finalized_header.beacon.hash_tree_root()
        elif finalized == 0:
            state.finalized_checkpoint.root = spec.Root()
        size = int(spec.SYNC_COMMITTEE_SIZE)
        bits = [i < signers for i in range(size)]
        made = spec.LightClientUpdate(
            attested_header=self.header(attested, state),
            sync_aggregate=spec.SyncAggregate(
                sync_committee_bits=spec.SyncCommitteeBits(data=bits)
            ),
            signature_slot=signature,
        )
        if committee:
            made.next_sync_committee = state.next_sync_committee
            gindex = spec.next_sync_committee_gindex_at_slot(attested)
            made.next_sync_committee_branch = spec.NextSyncCommitteeBranch(
                data=spec.compute_merkle_proof(state, gindex)
            )
        if finalized >= 0:
            made.finalized_header = finalized_header
            gindex = spec.finalized_root_gindex_at_slot(attested)
            made.finality_branch = spec.FinalityBranch(
                data=spec.compute_merkle_proof(state, gindex)
            )
        if mutation == 1:
            made.finality_branch.data[0] = spec.Bytes32(b"\x09" * 32)
        elif mutation == 2:
            made.next_sync_committee_branch.data[0] = spec.Bytes32(b"\x09" * 32)
        elif mutation == 3:
            made.finality_branch = spec.FinalityBranch()
        elif mutation == 4:
            made.next_sync_committee_branch = spec.NextSyncCommitteeBranch()
        elif mutation == 5:
            made.attested_header.beacon.body_root = spec.Root(b"\x0b" * 32)
        elif mutation == 6:
            made.finalized_header.beacon.proposer_index += 1
        elif mutation == 7:
            last = len(made.finality_branch.data) - 1
            made.finality_branch.data[last] = spec.Bytes32(b"\x0c" * 32)
        return made

    def digest(self):
        store = self.store

        def root(value):
            return bytes(value.hash_tree_root()).hex()[:8]

        best = "none" if store.best_valid_update is None else root(store.best_valid_update)
        STATS["digests"] += 1
        STATS["finalized moved"] += store.finalized_header.beacon.slot > 10
        STATS["finalized in a later period"] += store.finalized_header.beacon.slot >= 64
        STATS["best update kept"] += store.best_valid_update is not None
        STATS["next committee known"] += self.spec.is_next_sync_committee_known(store)
        return " ".join(
            [
                f"f={int(store.finalized_header.beacon.slot)}:{root(store.finalized_header)}",
                f"o={int(store.optimistic_header.beacon.slot)}:{root(store.optimistic_header)}",
                f"c={root(store.current_sync_committee)}",
                f"n={root(store.next_sync_committee)}",
                f"b={best}",
                f"p={int(store.previous_max_active_participants)}",
                f"a={int(store.current_max_active_participants)}",
            ]
        )


CURRENT = None


def answer(words):
    global CURRENT
    match words:
        case ["lc_init", fork, start]:
            CURRENT = LightClient(fork, int(start))
            return "\t".join(
                [
                    CURRENT.bootstrap.encode_bytes().hex(),
                    bytes(CURRENT.trusted).hex(),
                    bytes(CURRENT.state.genesis_validators_root).hex(),
                    CURRENT.digest(),
                ]
            )
        case ["lc_update", *numbers, now]:
            spec = CURRENT.spec
            try:
                made = CURRENT.update(*[int(n) for n in numbers])
            except Exception:
                return "skip"
            try:
                root = CURRENT.state.genesis_validators_root
                spec.process_light_client_update(CURRENT.store, made, int(now), root)
                verdict = "ok"
            except Exception:
                verdict = "error"
            STATS[f"update {verdict}"] += 1
            return "\t".join([made.encode_bytes().hex(), verdict, CURRENT.digest()])
        case ["lc_force", now]:
            try:
                CURRENT.spec.process_light_client_store_force_update(CURRENT.store, int(now))
                verdict = "ok"
            except Exception:
                verdict = "error"
            return "\t".join([verdict, CURRENT.digest()])

"""References for the consensus layer: the executable consensus-specs (pyspec)."""

# One command per line, words separated by tabs, one answer line.
#
#     on <fork> <call> <state hex> <argument words>
#         The same as `st`, on a state given by its SSZ bytes.
#
#     st <fork> <call> <state words> [| <argument words>]
#         Build a state of the minimal preset from the words, apply the call,
#         and answer "<state hex> <argument hex> <result>".  The result is
#         "ok:<state root>", "val:<text>" or "error:<reason>".
#     diff <state hex>
#         The fields in which a state differs from the last post-state.
#     stats
#         "<call>:<accepted>/<unchanged>/<refused>/<skipped>" for each call.
#     pure <call> <arguments>
#         A helper that needs no state.
#
# A signature is valid when its first 32 bytes are the SHA-256 of the public
# keys followed by the message.  The driver gives EthLib the same check, so
# the test covers domains and signing roots without a pairing.

import importlib
import os
import sys

from eth_consensus_specs.utils import bls

# The interpreter runs isolated, so the directory of the script is not on the path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import consensus_ops as ops  # noqa: E402

FORKS = [
    "phase0",
    "altair",
    "bellatrix",
    "capella",
    "deneb",
    "electra",
    "fulu",
    "gloas",
    "heze",
]
SPECS = {}
FAR = 2**64 - 1


def spec_of(fork):
    if fork not in SPECS:
        SPECS[fork] = importlib.import_module(f"eth_consensus_specs.{fork}.minimal")
    return SPECS[fork]


sha = ops.sha
fake_signature = ops.fake_signature
pubkey = ops.pubkey
credentials = ops.credentials
ints = ops.numbers
CURRENT = ops.CURRENT


def fake_verify(pubkey, message, signature):
    return bytes(signature) == fake_signature([pubkey], message)


def fake_fast_aggregate_verify(pubkeys, message, signature):
    return bytes(signature) == fake_signature(pubkeys, message)


bls.Verify = fake_verify
bls.FastAggregateVerify = fake_fast_aggregate_verify


def block_root(slot):
    return sha(b"block" + slot.to_bytes(8, "little"))


def checkpoint(spec, state, epoch):
    """A checkpoint whose root is the block root of its epoch, where known."""
    start = int(epoch) * int(spec.SLOTS_PER_EPOCH)
    root = bytes(32)
    if start < state.slot <= start + spec.SLOTS_PER_HISTORICAL_ROOT:
        root = state.block_roots[start % spec.SLOTS_PER_HISTORICAL_ROOT]
    return spec.Checkpoint(epoch=epoch, root=root)


def pending_attestation(spec, state, fields):
    """Phase 0: a pending attestation of a committee, or none out of range."""
    current, offset, index, seed, delay, proposer, source_ok, target_ok, head_ok = fields
    epoch = spec.get_current_epoch(state) if current else spec.get_previous_epoch(state)
    slot = spec.compute_start_slot_at_epoch(epoch) + offset % int(spec.SLOTS_PER_EPOCH)
    if slot >= state.slot:
        return None
    try:
        committee = spec.get_beacon_committee(state, slot, index)
        target_root = spec.get_block_root(state, epoch)
        head_root = spec.get_block_root_at_slot(state, slot)
    except Exception:
        return None
    digest = sha(seed.to_bytes(8, "little"))
    bits = [bool(digest[i % 32] >> (i // 32 % 8) & 1) for i in range(len(committee))]
    if seed % 5 == 0:
        bits = [True] * len(committee)
    source = state.current_justified_checkpoint if current else state.previous_justified_checkpoint
    if not source_ok:
        source = spec.Checkpoint(epoch=source.epoch, root=b"\x01" * 32)
    data = spec.AttestationData(
        slot=slot,
        index=index,
        beacon_block_root=head_root if head_ok else b"\x02" * 32,
        source=source,
        target=spec.Checkpoint(epoch=epoch, root=target_root if target_ok else b"\x03" * 32),
    )
    return spec.PendingAttestation(
        aggregation_bits=ops.field_of(spec.PendingAttestation, "aggregation_bits", bits),
        data=data,
        inclusion_delay=delay,
        proposer_index=proposer,
    )


def sync_committee(spec, state, real, shift):
    """A sync committee: the one of the state, or its validators in turn."""
    if real:
        try:
            return spec.get_next_sync_committee(state)
        except Exception:
            pass
    count = len(state.validators)
    size = int(spec.SYNC_COMMITTEE_SIZE)
    keys = [
        state.validators[(i + shift) % count].pubkey if count else pubkey(i) for i in range(size)
    ]
    return spec.SyncCommittee(
        pubkeys=ops.field_of(spec.SyncCommittee, "pubkeys", keys),
        aggregate_pubkey=bls.AggregatePKs(keys),
    )


def build_state(fork, words):
    """The state that the words describe; a word is `key=numbers`."""
    spec = spec_of(fork)
    state = spec.BeaconState()
    has = type(state).model_fields.__contains__
    later = []
    position = FORKS.index(fork)
    # The minimal configuration numbers its fork versions.
    versions = [bytes([i, 0, 0, 1]) for i in range(len(FORKS))]
    state.fork = spec.Fork(
        previous_version=versions[max(position - 1, 0)],
        current_version=versions[position],
        epoch=0,
    )
    state.genesis_validators_root = sha(b"genesis")
    for i in range(spec.SLOTS_PER_HISTORICAL_ROOT):
        state.block_roots[i] = block_root(i)
        state.state_roots[i] = sha(b"state" + i.to_bytes(8, "little"))
    for i in range(spec.EPOCHS_PER_HISTORICAL_VECTOR):
        state.randao_mixes[i] = sha(b"mix" + i.to_bytes(8, "little"))
    for word in words:
        key, _, text = word.partition("=")
        f = ints(text) if text != "same" else [0]
        if key == "slot":
            state.slot = f[0]
            CURRENT[0] = f[0] // int(spec.SLOTS_PER_EPOCH)
            state.latest_block_header = spec.BeaconBlockHeader(
                slot=max(f[0], 1) - 1, parent_root=sha(b"parent"), body_root=sha(b"body")
            )
        elif key == "v":
            prefix, cred_seed, eb, bal, slashed, elig, act, exit_, wd = f[:9]
            state.validators.append(
                spec.Validator(
                    # The key of a validator is that of its position, so keys are distinct.
                    pubkey=pubkey(len(state.validators)),
                    withdrawal_credentials=credentials(prefix, cred_seed),
                    effective_balance=eb,
                    slashed=bool(slashed),
                    activation_eligibility_epoch=elig,
                    activation_epoch=act,
                    exit_epoch=exit_,
                    withdrawable_epoch=wd,
                )
            )
            state.balances.append(bal)
            if has("inactivity_scores"):
                state.previous_epoch_participation.append(f[9])
                state.current_epoch_participation.append(f[10])
                state.inactivity_scores.append(f[11])
        elif key == "forkepoch":
            state.fork.epoch = f[0]
        elif key == "bits":
            for i in range(4):
                state.justification_bits[i] = bool(f[0] >> i & 1)
        elif key in ("fin", "pj", "cj", "pa", "lookahead", "sync"):
            later.append((key, f))
        elif key == "slashings":
            state.slashings[f[0] % spec.EPOCHS_PER_SLASHINGS_VECTOR] = f[1]
        elif key == "eth1" and has("eth1_deposit_index"):
            state.eth1_deposit_index = f[0]
            state.eth1_data.deposit_count = f[1]
        elif key == "votes" and has("eth1_data_votes"):
            for i in range(f[0]):
                state.eth1_data_votes.append(spec.Eth1Data(deposit_count=i % 2))
        elif key == "wd" and has("next_withdrawal_index"):
            state.next_withdrawal_index = f[0]
            state.next_withdrawal_validator_index = f[1]
        elif key == "hist":
            for i in range(f[0]):
                state.historical_roots.append(sha(b"hist" + bytes([i])))
        elif key == "b" and has("builders"):
            state.builders.append(
                spec.Builder(
                    # The key of a builder is that of its position, so keys are distinct.
                    pubkey=pubkey(500 + len(state.builders)),
                    execution_address=bytes([f[1] % 256]) * 20,
                    balance=f[2],
                    deposit_epoch=f[3],
                    withdrawable_epoch=f[4],
                )
            )
        elif key == "bpp" and has("builder_pending_payments"):
            position = f[0] % len(state.builder_pending_payments)
            state.builder_pending_payments[position] = spec.BuilderPendingPayment(
                weight=f[1],
                withdrawal=spec.BuilderPendingWithdrawal(
                    fee_recipient=b"\x0b" * 20, amount=f[2], builder_index=f[3]
                ),
                proposer_index=f[4],
            )
        elif key == "bpw" and has("builder_pending_withdrawals"):
            state.builder_pending_withdrawals.append(
                spec.BuilderPendingWithdrawal(
                    fee_recipient=b"\x0c" * 20, amount=f[0], builder_index=f[1]
                )
            )
        elif key == "gloas" and has("builders"):
            state.next_withdrawal_builder_index = f[0]
            if f[1]:
                # The parent block has no payload: its hash is not that of the bid.
                state.latest_block_hash = b"\x01" * 32
        elif not has("pending_deposits"):
            continue
        elif key == "churn":
            state.deposit_balance_to_consume = f[0]
            state.exit_balance_to_consume = f[1]
            state.earliest_exit_epoch = f[2]
            state.consolidation_balance_to_consume = f[3]
            state.earliest_consolidation_epoch = f[4]
        elif key == "drsi" and has("deposit_requests_start_index"):
            # `drsi=same`: the deposit contract is drained, as an upgrade to Heze needs.
            same = text == "same" and has("eth1_deposit_index")
            state.deposit_requests_start_index = state.eth1_deposit_index if same else f[0]
        elif key == "pd":
            key_seed, prefix, cred_seed, amount, slot, valid = f
            data = spec.PendingDeposit(
                pubkey=pubkey(key_seed),
                withdrawal_credentials=credentials(prefix, cred_seed),
                amount=amount,
                slot=slot,
            )
            message = spec.DepositMessage(
                pubkey=data.pubkey,
                withdrawal_credentials=data.withdrawal_credentials,
                amount=amount,
            )
            domain = spec.compute_domain(spec.DOMAIN_DEPOSIT)
            root = spec.compute_signing_root(message, domain)
            data.signature = fake_signature([data.pubkey], root) if valid else b"\x07" * 96
            state.pending_deposits.append(data)
        elif key == "ppw":
            state.pending_partial_withdrawals.append(
                spec.PendingPartialWithdrawal(
                    validator_index=f[0], amount=f[1], withdrawable_epoch=f[2]
                )
            )
        elif key == "pc":
            state.pending_consolidations.append(
                spec.PendingConsolidation(source_index=f[0], target_index=f[1])
            )
    for key, f in later:
        if key == "fin":
            state.finalized_checkpoint = checkpoint(spec, state, f[0])
        elif key == "pj":
            state.previous_justified_checkpoint = checkpoint(spec, state, f[0])
        elif key == "cj":
            state.current_justified_checkpoint = checkpoint(spec, state, f[0])
    for key, f in later:
        if key == "pa" and fork == "phase0":
            attestation = pending_attestation(spec, state, f)
            if attestation is not None:
                current = attestation.data.target.epoch == spec.get_current_epoch(state)
                (
                    state.current_epoch_attestations
                    if current
                    else state.previous_epoch_attestations
                ).append(attestation)
        elif key == "sync" and has("current_sync_committee"):
            state.current_sync_committee = sync_committee(spec, state, f[0], 0)
            state.next_sync_committee = sync_committee(spec, state, f[0], 1)
        elif key == "lookahead" and has("proposer_lookahead"):
            try:
                state.proposer_lookahead = spec.initialize_proposer_lookahead(state)
            except Exception:
                continue
    return spec, state


def text_of(value):
    """A returned value as one word."""
    if isinstance(value, str):
        return value
    if isinstance(value, bool):
        return "true" if value else "false"
    if hasattr(value, "hash_tree_root") and not isinstance(value, (int, bytes)):
        if list(getattr(type(value), "model_fields", {})) != ["data"]:
            return bytes(value.hash_tree_root()).hex()
    if isinstance(value, int):
        return str(int(value))
    if isinstance(value, (bytes, bytearray)):
        return bytes(value).hex() or "-"
    if isinstance(value, (list, tuple, set)) or hasattr(value, "__iter__"):
        items = sorted(value) if isinstance(value, set) else list(value)
        return "[" + ",".join(text_of(item) for item in items) + "]"
    if hasattr(value, "hash_tree_root"):
        return bytes(value.hash_tree_root()).hex()
    return str(value)


LAST = {}
COUNTS = {}


def count(call, kind):
    COUNTS.setdefault(call, {"ok": 0, "same": 0, "error": 0, "skip": 0})[kind] += 1


REASONS = {}


def stats():
    """How often each call was accepted and refused, then forgotten."""
    out = ";".join(
        f"{call}:{c['ok']}/{c['same']}/{c['error']}/{c['skip']}"
        for call, c in sorted(COUNTS.items())
    )
    COUNTS.clear()
    if os.environ.get("ORACLE_REASONS"):
        # Why the reference refused, for tuning a generator: the main reasons.
        for call, reasons in sorted(REASONS.items()):
            top = sorted(reasons.items(), key=lambda kv: -kv[1])[:12]
            print(call, top, file=sys.stderr)
    REASONS.clear()
    return out or "-"


def run(spec, fork, state, call, words):
    """Apply a call to a state: the state before, the argument, the result."""
    CURRENT[0] = int(state.slot) // int(spec.SLOTS_PER_EPOCH)
    try:
        argument, apply = ops.prepare(spec, fork, state, call, words)
    except ops.SkipError:
        count(call, "skip")
        return "- - skip"
    before = bytes(state.encode_bytes())
    pre = before.hex()
    try:
        value = apply()
    except Exception as e:
        LAST["state"] = None
        count(call, "error")
        where = e.__traceback__
        while where.tb_next:
            where = where.tb_next
        site = f"{where.tb_frame.f_code.co_name}:{where.tb_lineno}"
        REASONS.setdefault(call, {}).setdefault(site, 0)
        REASONS[call][site] += 1
        reason = f"{type(e).__name__}:{e}".replace(" ", "_").replace("\n", "_")
        return f"{pre} {argument} error:{reason[:200]}"
    LAST["state"] = state
    unchanged = value is None and bytes(state.encode_bytes()) == before
    count(call, "same" if unchanged else "ok")
    if value is None:
        return f"{pre} {argument} ok:{bytes(state.hash_tree_root()).hex()}"
    if hasattr(value, "validators"):
        LAST["state"] = value
        return f"{pre} {argument} ok:{bytes(value.hash_tree_root()).hex()}"
    return f"{pre} {argument} val:{text_of(value)}"


def st(fork, call, words):
    split = words.index("|") if "|" in words else len(words)
    spec, state = build_state(fork, words[:split])
    return run(spec, fork, state, call, words[split + 1 :])


def on(fork, call, data, words):
    spec = spec_of(fork)
    state = spec.BeaconState.decode_bytes(bytes.fromhex(data))
    return run(spec, fork, state, call, words)


def differences(a, b, path, out, depth=0):
    """The leaves at which two values differ, as `path:ethlib=..,spec=..`."""
    if len(out) > 12 or depth > 8:
        return
    if isinstance(a, (bytes, bytearray)):
        if bytes(a) != bytes(b):
            out.append(f"{path}:ethlib={bytes(a).hex()},spec={bytes(b).hex()}")
        return
    if isinstance(a, int):
        if int(a) != int(b):
            out.append(f"{path}:ethlib={int(a)},spec={int(b)}")
        return
    fields = list(getattr(type(a), "model_fields", {}))
    if fields and fields != ["data"]:
        for name in fields:
            differences(getattr(a, name), getattr(b, name), f"{path}.{name}", out, depth + 1)
        return
    xs, ys = list(a), list(b)
    if len(xs) != len(ys):
        out.append(f"{path}:length_ethlib={len(xs)},spec={len(ys)}")
    for i, (x, y) in enumerate(zip(xs, ys, strict=False)):
        differences(x, y, f"{path}[{i}]", out, depth + 1)


def diff(fork, data):
    expected = LAST.get("state")
    if expected is None:
        return "the reference has no post-state"
    got = type(expected).decode_bytes(bytes.fromhex(data))
    out = []
    differences(got, expected, "", out)
    return ";".join(out) or "no difference found"


def answer(words):
    match words:
        case ["st", fork, call, *rest]:
            return st(fork, call, rest)
        case ["on", fork, call, data, *rest]:
            return on(fork, call, data, rest)
        case ["stats"]:
            return stats()
        case ["diff", fork, data]:
            return diff(fork, data)
        case ["pure", call, *arguments]:
            try:
                return ops.pure(spec_of, call, arguments)
            except (AssertionError, IndexError, ZeroDivisionError, ValueError) as e:
                return f"error:{type(e).__name__}"
    return "error unknown command"


if __name__ == "__main__":
    for line in sys.stdin:
        try:
            out = answer(line.rstrip("\n").split("\t"))
        except Exception as e:
            out = f"oracle-failure:{type(e).__name__}:{e}".replace("\n", " ")
        print(out or "-", flush=True)

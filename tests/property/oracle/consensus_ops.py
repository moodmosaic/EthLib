"""The calls of the consensus oracle: what to run on a state, and its argument."""

# `prepare` reads the words of an argument and builds the operation with consensus-specs types.
# It returns the SSZ bytes of the operation in hexadecimal with the function that applies the call.
# It may set up the state first (a deposit needs a deposit root).
# So the caller writes the state after it.

import hashlib
import inspect

from eth_consensus_specs.utils import bls

FAR = 2**64 - 1
G2_INFINITY = b"\xc0" + bytes(95)
ORDER = [
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


class SkipError(Exception):
    """The words describe no argument for this state."""


def sha(data):
    return hashlib.sha256(data).digest()


def since(fork, first):
    return ORDER.index(fork) >= ORDER.index(first)


def fake_signature(pubkeys, message):
    """The signature that the test takes as valid for keys and a message."""
    return sha(b"".join(bytes(p) for p in pubkeys) + bytes(message)) + bytes(64)


KEYS = {}


def pubkey(seed):
    """A valid public key for a seed, so that keys aggregate."""
    if seed not in KEYS:
        KEYS[seed] = bytes(bls.SkToPk(seed + 1))
    return KEYS[seed]


def credentials(prefix, seed):
    """Credentials with a prefix: BLS ones commit to the key of the seed."""
    if prefix == 0:
        return b"\x00" + sha(pubkey(seed))[1:]
    return bytes([prefix]) + bytes(11) + bytes([seed % 256]) * 20


def field_of(container, name, values):
    """A value of the type of a field: bit lists and bit vectors need their class."""
    return container.model_fields[name].annotation(data=values)


def hexof(value):
    return bytes(value.encode_bytes()).hex() or "-"


def signed(spec, keys, message, domain, ok):
    """A signature of the keys over a message under a domain, or a wrong one."""
    if not ok:
        return b"\x09" * 96
    return fake_signature(keys, spec.compute_signing_root(message, domain))


def key_at(state, index):
    """The key of a validator, or a key that no validator holds."""
    if index < len(state.validators):
        return state.validators[index].pubkey
    return pubkey(1000 + index % 50)


def address_at(state, index, address):
    """An address: the one of a validator's credentials when asked for it (9)."""
    if address == 9 and index < len(state.validators):
        return bytes(state.validators[index].withdrawal_credentials)[12:]
    return bytes([address]) * 20


def seeded_bits(seed, count):
    """Bits from a seed: every fifth seed sets all, every seventh none."""
    if seed % 5 == 0:
        return [True] * count
    if seed % 7 == 0:
        return [False] * count
    digest = sha(seed.to_bytes(8, "little"))
    return [bool(digest[i % 32] >> (i // 32 % 8) & 1) for i in range(count)]


# Calls that take the state alone and change it.
MUTATORS = {
    "process_justification_and_finalization",
    "process_inactivity_updates",
    "process_rewards_and_penalties",
    "process_registry_updates",
    "process_slashings",
    "process_eth1_data_reset",
    "process_pending_deposits",
    "process_pending_consolidations",
    "process_builder_pending_payments",
    "process_effective_balance_updates",
    "process_slashings_reset",
    "process_randao_mixes_reset",
    "process_historical_roots_update",
    "process_historical_summaries_update",
    "process_participation_record_updates",
    "process_participation_flag_updates",
    "process_sync_committee_updates",
    "process_proposer_lookahead",
    "process_ptc_window",
    "process_epoch",
    "process_slot",
}

# Calls that take the state alone and return a value.
READERS = {
    "get_total_active_balance",
    "get_validator_churn_limit",
    "get_validator_activation_churn_limit",
    "get_balance_churn_limit",
    "get_activation_exit_churn_limit",
    "get_consolidation_churn_limit",
    "get_exit_churn_limit",
    "get_activation_churn_limit",
    "get_beacon_proposer_index",
    "get_finality_delay",
    "is_in_inactivity_leak",
    "get_eligible_validator_indices",
    "get_next_sync_committee_indices",
    "get_next_sync_committee",
    "get_current_epoch",
    "get_previous_epoch",
    "is_valid_genesis_state",
}

# Calls that take numbers and change the state.
NUMBER_MUTATORS = {
    "initiate_validator_exit",
    "compute_exit_epoch_and_update_churn",
    "compute_consolidation_epoch_and_update_churn",
    "switch_to_compounding_validator",
    "queue_excess_active_balance",
    "increase_balance",
    "decrease_balance",
}

# Calls that take numbers and return a value.
NUMBER_READERS = {
    "get_active_validator_indices",
    "get_committee_count_per_slot",
    "get_block_root",
    "get_randao_mix",
    "get_pending_balance_to_withdraw",
    "get_base_reward",
    "get_beacon_proposer_indices",
}

DOMAINS = [
    "DOMAIN_BEACON_PROPOSER",
    "DOMAIN_BEACON_ATTESTER",
    "DOMAIN_RANDAO",
    "DOMAIN_DEPOSIT",
    "DOMAIN_VOLUNTARY_EXIT",
    "DOMAIN_SELECTION_PROOF",
    "DOMAIN_AGGREGATE_AND_PROOF",
]


CURRENT = [0]


def number(word):
    """A number, or an epoch relative to the current one: `c+2`, `c-1`."""
    if word.startswith("c+"):
        return min(CURRENT[0] + int(word[2:]), FAR)
    if word.startswith("c-"):
        return max(CURRENT[0] - int(word[2:]), 0)
    return int(word)


def numbers(word):
    return [number(x) for x in word.split(",")] if word not in ("", "=") else []


def words64(spec, word):
    """The numbers of a word as 64-bit values of the specification."""
    return [spec.Uint64(n) for n in numbers(word)]


def voluntary_exit(spec, fork, state, f):
    index, epoch, ok = f
    message = spec.VoluntaryExit(epoch=epoch, validator_index=index)
    if since(fork, "deneb"):
        domain = spec.compute_domain(
            spec.DOMAIN_VOLUNTARY_EXIT,
            spec.config.CAPELLA_FORK_VERSION,
            state.genesis_validators_root,
        )
    else:
        domain = spec.get_domain(state, spec.DOMAIN_VOLUNTARY_EXIT, epoch)
    signature = signed(spec, [key_at(state, index)], message, domain, ok)
    return spec.SignedVoluntaryExit(message=message, signature=signature)


def signed_header(spec, state, header, key, ok):
    epoch = spec.compute_epoch_at_slot(header.slot)
    domain = spec.get_domain(state, spec.DOMAIN_BEACON_PROPOSER, epoch)
    signature = signed(spec, [key], header, domain, ok)
    return spec.SignedBeaconBlockHeader(message=header, signature=signature)


def proposer_slashing(spec, fork, state, f):
    index, slot, same, ok1, ok2, index_delta, slot_delta = f
    first = spec.BeaconBlockHeader(
        slot=slot, proposer_index=index, parent_root=sha(b"p"), body_root=sha(b"1")
    )
    second = spec.BeaconBlockHeader(
        slot=(slot + slot_delta) % 2**64,
        proposer_index=(index + index_delta) % 2**64,
        parent_root=sha(b"p"),
        body_root=sha(b"1") if same else sha(b"2"),
    )
    key = key_at(state, index)
    return spec.ProposerSlashing(
        signed_header_1=signed_header(spec, state, first, key, ok1),
        signed_header_2=signed_header(spec, state, second, key, ok2),
    )


def indexed_attestation(spec, state, indices, data, ok):
    keys = [key_at(state, i) for i in indices]
    domain = spec.get_domain(state, spec.DOMAIN_BEACON_ATTESTER, data.target.epoch)
    return spec.IndexedAttestation(
        attesting_indices=field_of(spec.IndexedAttestation, "attesting_indices", indices),
        data=data,
        signature=signed(spec, keys, data, domain, ok),
    )


def attester_slashing(spec, fork, state, words):
    kind, ok1, ok2, sort1, sort2 = numbers(words[0])
    first = numbers(words[1]) if len(words) > 1 else []
    second = numbers(words[2]) if len(words) > 2 else []
    if len(words) > 2 and words[2] == "=":
        second = list(first)
    if sort1:
        first = sorted(set(first))
    if sort2:
        second = sorted(set(second))
    current = int(spec.get_current_epoch(state))

    def data(source, target, root):
        return spec.AttestationData(
            slot=max(target, 0) * int(spec.SLOTS_PER_EPOCH),
            beacon_block_root=root,
            source=spec.Checkpoint(epoch=max(source, 0), root=sha(b"s")),
            target=spec.Checkpoint(epoch=max(target, 0), root=sha(b"t")),
        )

    pairs = {
        0: (data(current - 1, current, sha(b"a")), data(current - 1, current, sha(b"b"))),
        1: (data(current - 3, current, sha(b"a")), data(current - 2, current - 1, sha(b"a"))),
        2: (data(current - 2, current - 1, sha(b"a")), data(current - 3, current, sha(b"a"))),
        3: (data(current - 1, current, sha(b"a")), data(current - 1, current, sha(b"a"))),
        4: (data(current - 2, current - 1, sha(b"a")), data(current - 1, current, sha(b"a"))),
        5: (data(current - 2, current, sha(b"a")), data(current - 2, current - 1, sha(b"a"))),
    }
    one, two = pairs[kind % len(pairs)]
    return spec.AttesterSlashing(
        attestation_1=indexed_attestation(spec, state, first, one, ok1),
        attestation_2=indexed_attestation(spec, state, second, two, ok2),
    )


def attestation(spec, fork, state, f):
    """An attestation of one committee, or of two from Electra, near valid."""
    back, cindex, seed, source_ok, target_ok, head_ok, ok, length, mode, payload = f
    if back > state.slot:
        raise SkipError()
    slot = state.slot - back
    epoch = spec.compute_epoch_at_slot(slot)
    current = epoch == spec.get_current_epoch(state)

    def committee_of(index):
        try:
            return list(spec.get_beacon_committee(state, slot, index))
        except Exception:
            return None

    chosen = [cindex, cindex + 1] if mode == 2 and since(fork, "electra") else [cindex]
    committees = [committee_of(i) for i in chosen]
    members = [m for c in committees for m in (c if c is not None else [0, 0, 0])]
    bits = seeded_bits(seed, len(members))
    bits = (bits + [True, True])[: max(len(bits) + length - 1, 0)]
    attesters = sorted({m for m, bit in zip(members, bits, strict=False) if bit})
    try:
        target_root = spec.get_block_root(state, epoch)
        head_root = spec.get_block_root_at_slot(state, slot)
    except Exception:
        target_root = head_root = bytes(32)
    source = state.current_justified_checkpoint if current else state.previous_justified_checkpoint
    if source_ok == 0:
        source = spec.Checkpoint(epoch=source.epoch, root=b"\x01" * 32)
    elif source_ok == 2:
        source = spec.Checkpoint(epoch=source.epoch + 1, root=source.root)
    data = spec.AttestationData(
        slot=slot,
        index=payload if since(fork, "electra") else cindex,
        beacon_block_root=head_root if head_ok else b"\x02" * 32,
        source=source,
        target=spec.Checkpoint(
            epoch=epoch if target_ok != 2 else epoch + 1,
            root=target_root if target_ok else b"\x03" * 32,
        ),
    )
    domain = spec.get_domain(state, spec.DOMAIN_BEACON_ATTESTER, data.target.epoch)
    signature = signed(spec, [key_at(state, i) for i in attesters], data, domain, ok)
    fields = {
        "aggregation_bits": field_of(spec.Attestation, "aggregation_bits", bits),
        "data": data,
        "signature": signature,
    }
    if since(fork, "electra"):
        count = int(spec.MAX_COMMITTEES_PER_SLOT)
        committee_bits = [i in chosen and mode != 3 for i in range(count)]
        fields["committee_bits"] = field_of(spec.Attestation, "committee_bits", committee_bits)
    return spec.Attestation(**fields)


def bls_change(spec, fork, state, f):
    index, key_seed, address, ok = f
    if key_seed == 9 and index < len(state.validators):
        # The key that the credentials of the validator commit to, if one does.
        held = bytes(state.validators[index].withdrawal_credentials)
        key_seed = next((k for k in range(6) if credentials(0, k) == held), 0)
    message = spec.BLSToExecutionChange(
        validator_index=index,
        from_bls_pubkey=pubkey(key_seed),
        to_execution_address=bytes([address]) * 20,
    )
    domain = spec.compute_domain(
        spec.DOMAIN_BLS_TO_EXECUTION_CHANGE,
        genesis_validators_root=state.genesis_validators_root,
    )
    signature = signed(spec, [pubkey(key_seed)], message, domain, ok)
    return spec.SignedBLSToExecutionChange(message=message, signature=signature)


def deposit_data(spec, f):
    key_seed, prefix, cred_seed, amount, ok = f[:5]
    message = spec.DepositMessage(
        pubkey=pubkey(key_seed),
        withdrawal_credentials=credentials(prefix, cred_seed),
        amount=amount,
    )
    domain = spec.compute_domain(spec.DOMAIN_DEPOSIT)
    if ok == 2 and hasattr(spec, "DOMAIN_BUILDER_DEPOSIT"):
        domain = spec.compute_domain(spec.DOMAIN_BUILDER_DEPOSIT)
    return spec.DepositData(
        pubkey=message.pubkey,
        withdrawal_credentials=message.withdrawal_credentials,
        amount=amount,
        signature=signed(spec, [message.pubkey], message, domain, ok),
    )


def deposit_request(spec, fork, state, f):
    data = deposit_data(spec, f)
    return spec.DepositRequest(
        pubkey=data.pubkey,
        withdrawal_credentials=data.withdrawal_credentials,
        amount=data.amount,
        signature=data.signature,
        index=f[5],
    )


def builder_deposit_request(spec, fork, state, f):
    key, prefix, cred_seed, amount, ok = f
    data = deposit_data(spec, [500 + key, prefix, cred_seed, amount, ok])
    return spec.BuilderDepositRequest(
        pubkey=data.pubkey,
        withdrawal_credentials=data.withdrawal_credentials,
        amount=data.amount,
        signature=data.signature,
    )


def builder_exit_request(spec, fork, state, f):
    address, key = f
    source = bytes([address]) * 20
    if address == 9 and key < len(state.builders):
        source = bytes(state.builders[key].execution_address)
    return spec.BuilderExitRequest(source_address=source, pubkey=pubkey(500 + key))


def payload_bid(spec, fork, state, f):
    """From Gloas: a bid for the payload of the slot, valid but for what the numbers break."""
    builder, value, ok, slot_delta, parent_ok, differs, root_ok, randao_ok, blobs = f
    slot = (int(state.slot) + slot_delta) % 2**64
    try:
        parent_root = spec.get_block_root_at_slot(state, state.slot - 1)
    except Exception:
        parent_root = spec.Root()
    parent_hash = bytes(state.latest_block_hash) if parent_ok else b"\x07" * 32
    commitments = [b"\xc0" + bytes(47)] * blobs
    bid = spec.ExecutionPayloadBid(
        parent_block_hash=parent_hash,
        parent_block_root=parent_root if root_ok else b"\x08" * 32,
        block_hash=sha(b"bid") if differs else parent_hash,
        prev_randao=spec.get_randao_mix(state, spec.get_current_epoch(state))
        if randao_ok
        else b"\x09" * 32,
        fee_recipient=b"\x0a" * 20,
        gas_limit=30000000,
        builder_index=builder,
        slot=slot,
        value=value,
        blob_kzg_commitments=field_of(
            spec.ExecutionPayloadBid, "blob_kzg_commitments", commitments
        ),
    )
    if ok == 2:
        signature = G2_INFINITY
    else:
        key = state.builders[builder].pubkey if builder < len(state.builders) else pubkey(0)
        domain = spec.get_domain(
            state, spec.DOMAIN_BEACON_BUILDER, spec.compute_epoch_at_slot(slot)
        )
        signature = signed(spec, [key], bid, domain, ok)
    return spec.SignedExecutionPayloadBid(message=bid, signature=signature)


def merkle_root_and_branch(leaves, index, depth):
    """A naive Merkle tree of a depth over zero-padded leaves, and one branch."""
    zero = [bytes(32)]
    for _ in range(depth):
        zero.append(sha(zero[-1] * 2))
    level, branch = list(leaves), []
    for height in range(depth):
        sibling = index ^ 1
        branch.append(level[sibling] if sibling < len(level) else zero[height])
        if len(level) % 2:
            level.append(zero[height])
        level = [sha(level[i] + level[i + 1]) for i in range(0, len(level), 2)]
        index //= 2
    return (level[0] if level else zero[depth]), branch


def deposit(spec, fork, state, f):
    """A deposit with its proof; the state gets the root of the deposit tree."""
    count, index, corrupt = f[5:8]
    index = index % max(count, 1)
    datas = [deposit_data(spec, [i + 40, 1, i, 32 * 10**9, 1]) for i in range(count)]
    data = deposit_data(spec, f)
    datas[index : index + 1] = [data]
    leaves = [bytes(d.hash_tree_root()) for d in datas]
    root, branch = merkle_root_and_branch(leaves, index, 32)
    length = len(leaves).to_bytes(32, "little")
    state.eth1_data.deposit_root = sha(root + length)
    state.eth1_data.deposit_count = len(leaves)
    state.eth1_deposit_index = index
    proof = branch + [length]
    if corrupt == 1:
        proof[index % 33] = sha(proof[index % 33])
    elif corrupt == 2:
        state.eth1_deposit_index = index + 1
    return spec.Deposit(proof=field_of(spec.Deposit, "proof", proof), data=data)


def withdrawal_request(spec, fork, state, f):
    address, index, amount = f
    return spec.WithdrawalRequest(
        source_address=address_at(state, index, address),
        validator_pubkey=key_at(state, index),
        amount=amount,
    )


def consolidation_request(spec, fork, state, f):
    address, source, target = f
    return spec.ConsolidationRequest(
        source_address=address_at(state, source, address),
        source_pubkey=key_at(state, source),
        target_pubkey=key_at(state, target),
    )


def sync_participant_keys(spec, state, bits, keys):
    """The keys that the fork checks a sync aggregate against.

    From Gloas the check takes the aggregate key of the committee when all took part.
    When more than half did, it takes that key less the keys of those who did not.
    """
    if "aggregate_pubkey" not in inspect.getsource(spec.process_sync_aggregate):
        return keys
    committee = state.current_sync_committee
    size = int(spec.SYNC_COMMITTEE_SIZE)
    if len(keys) == size:
        return [committee.aggregate_pubkey]
    if len(keys) > size // 2:
        absent = [k for k, bit in zip(committee.pubkeys, bits, strict=False) if not bit]
        try:
            key = spec.bls.add(
                spec.bls.bytes48_to_G1(committee.aggregate_pubkey),
                spec.bls.neg(spec.bls.bytes48_to_G1(spec.eth_aggregate_pubkeys(absent))),
            )
        except Exception:
            # The aggregate key of the state is no point: the check fails with any signature.
            return keys
        return [spec.BLSPubkey(spec.bls.G1_to_bytes48(key))]
    return keys


def sync_aggregate(spec, fork, state, f):
    seed, ok = f
    size = int(spec.SYNC_COMMITTEE_SIZE)
    bits = seeded_bits(seed, size)
    keys = [k for k, bit in zip(state.current_sync_committee.pubkeys, bits, strict=False) if bit]
    previous = max(int(state.slot), 1) - 1
    domain = spec.get_domain(
        state, spec.DOMAIN_SYNC_COMMITTEE, spec.compute_epoch_at_slot(previous)
    )
    try:
        root = spec.get_block_root_at_slot(state, previous)
    except Exception:
        root = spec.Root()
    signature = signed(spec, sync_participant_keys(spec, state, bits, keys), root, domain, ok)
    if not keys and ok:
        signature = G2_INFINITY
    return spec.SyncAggregate(
        sync_committee_bits=field_of(spec.SyncAggregate, "sync_committee_bits", bits),
        sync_committee_signature=signature,
    )


def withdrawals_payload(spec, fork, state, f):
    """A payload with the withdrawals that the state expects, or nearly."""
    (mutation,) = f
    try:
        expected = spec.get_expected_withdrawals(state)
        listed = list(getattr(expected, "withdrawals", expected))
    except Exception:
        # The state has no expected withdrawals: the call fails with any payload.
        listed = []
    if mutation == 1 and listed:
        listed = listed[:-1]
    elif mutation == 2 and listed:
        last = listed[-1].copy()
        last.amount = last.amount ^ 1
        listed[-1] = last
    elif mutation == 3:
        extra = spec.Withdrawal(index=FAR, validator_index=0, amount=1)
        full = len(listed) >= int(spec.MAX_WITHDRAWALS_PER_PAYLOAD)
        listed = listed[:-1] + [extra] if full else listed + [extra]
    elif mutation == 4 and len(listed) > 1:
        listed = [listed[1], listed[0]] + listed[2:]
    return spec.ExecutionPayload(withdrawals=field_of(spec.ExecutionPayload, "withdrawals", listed))


def show_withdrawals(spec, state):
    expected = spec.get_expected_withdrawals(state)
    listed = getattr(expected, "withdrawals", expected)
    rows = [
        f"{int(w.index)}:{int(w.validator_index)}:{bytes(w.address).hex()}:{int(w.amount)}"
        for w in listed
    ]
    counts = [
        int(getattr(expected, name))
        for name in (
            "processed_builder_withdrawals_count",
            "processed_partial_withdrawals_count",
            "processed_builders_sweep_count",
        )
        if hasattr(expected, name)
    ]
    return "[" + ",".join(rows) + "]" + "/" + ",".join(map(str, counts))


def payload_attestation(spec, state, parent_root, seed, kind):
    """From Gloas: an attestation of the committee of the slot before, or none.

    The kind says what is wrong with it: 1 nothing, 0 the signature, 2 the root, 3 the slot.
    """
    slot = max(int(state.slot), 1) - 1
    try:
        committee = [int(i) for i in spec.get_ptc(state, spec.Slot(slot))]
    except Exception:
        return None
    bits = seeded_bits(seed, len(committee))
    members = sorted(i for i, bit in zip(committee, bits, strict=False) if bit)
    data = spec.PayloadAttestationData(
        beacon_block_root=parent_root if kind != 2 else sha(b"other parent"),
        slot=slot if kind != 3 else slot + 1,
        payload_present=seed % 2 == 0,
        blob_data_available=seed % 3 == 0,
    )
    domain = spec.get_domain(state, spec.DOMAIN_PTC_ATTESTER, spec.compute_epoch_at_slot(data.slot))
    keys = [key_at(state, i) for i in members]
    return spec.PayloadAttestation(
        aggregation_bits=field_of(spec.PayloadAttestation, "aggregation_bits", bits),
        data=data,
        signature=signed(spec, keys, data, domain, kind != 0),
    )


def parent_requests(spec, state, kind):
    """From Gloas: the requests of the parent's payload, of a kind or none."""
    requests = spec.ExecutionRequests()
    if kind == 1:
        requests.withdrawals.append(
            spec.WithdrawalRequest(
                source_address=address_at(state, 0, 9),
                validator_pubkey=key_at(state, 0),
                amount=0,
            )
        )
    elif kind == 2:
        requests.consolidations.append(
            spec.ConsolidationRequest(
                source_address=address_at(state, 1, 9),
                source_pubkey=key_at(state, 1),
                target_pubkey=key_at(state, 1),
            )
        )
    elif kind == 3 and len(state.builders) > 0:
        requests.builder_exits.append(
            spec.BuilderExitRequest(
                source_address=bytes(state.builders[0].execution_address),
                pubkey=state.builders[0].pubkey,
            )
        )
    elif kind == 4:
        requests.deposits.append(
            spec.DepositRequest(
                pubkey=pubkey(700),
                withdrawal_credentials=credentials(1, 3),
                amount=32 * 10**9,
                signature=b"\x09" * 96,
                index=0,
            )
        )
    return requests


def gloas_block(spec, fork, state, f):
    """From Gloas: a block for the state, valid but for what the numbers break.

    The parent's payload is full or empty, by the hash that the bid builds on.
    The state gets the parent's bid that the block then answers to.
    """
    (
        slot_delta,
        proposer_delta,
        parent_ok,
        randao_ok,
        parent,
        kind,
        seed,
        sync_ok,
        bid_slot_delta,
        attestations,
        attestation_kind,
    ) = f
    try:
        proposer = int(spec.get_beacon_proposer_index(state))
    except Exception:
        proposer = 0
    epoch = spec.get_current_epoch(state)
    body = spec.BeaconBlockBody()
    domain = spec.get_domain(state, spec.DOMAIN_RANDAO)
    body.randao_reveal = signed(spec, [key_at(state, proposer)], epoch, domain, randao_ok)
    if hasattr(body, "eth1_data"):
        body.eth1_data = spec.Eth1Data(deposit_count=seed % 4)
    body.sync_aggregate = sync_aggregate(spec, fork, state, [seed, sync_ok])
    # The parent: 0 full, 1 empty, 2 full with other requests, 3 empty with requests.
    requests = parent_requests(spec, state, kind if parent != 1 else 0)
    full_hash = sha(b"the payload of the parent")
    state.latest_execution_payload_bid.block_hash = full_hash
    state.latest_execution_payload_bid.execution_requests_root = (
        requests.hash_tree_root() if parent != 2 else sha(b"other requests")
    )
    body.parent_execution_requests = requests
    self_build = int(spec.BUILDER_INDEX_SELF_BUILD)
    bid = payload_bid(spec, fork, state, [self_build, 0, 2, bid_slot_delta, 1, 1, 1, 1, 0])
    if parent in (0, 2):
        bid.message.parent_block_hash = full_hash
    body.signed_execution_payload_bid = bid
    parent_root = state.latest_block_header.hash_tree_root() if parent_ok else sha(b"x")
    made = [
        payload_attestation(spec, state, parent_root, seed + i, attestation_kind)
        for i in range(attestations)
    ]
    body.payload_attestations = [a for a in made if a is not None]
    return spec.BeaconBlock(
        slot=(int(state.slot) + slot_delta) % 2**64,
        proposer_index=(proposer + proposer_delta) % 2**64,
        parent_root=parent_root,
        body=body,
    )


def block(spec, fork, state, f):
    """A block for the state, valid but for what the numbers break."""
    (
        slot_delta,
        proposer_delta,
        parent_ok,
        randao_ok,
        payload,
        blobs,
        vote,
        seed,
        sync_ok,
        deposits,
    ) = f[:10]
    if hasattr(spec.BeaconBlockBody(), "signed_execution_payload_bid"):
        return gloas_block(spec, fork, state, f)
    try:
        proposer = int(spec.get_beacon_proposer_index(state))
    except Exception:
        proposer = 0
    epoch = spec.get_current_epoch(state)
    body = spec.BeaconBlockBody()
    domain = spec.get_domain(state, spec.DOMAIN_RANDAO)
    body.randao_reveal = signed(spec, [key_at(state, proposer)], epoch, domain, randao_ok)
    if hasattr(body, "eth1_data"):
        body.eth1_data = spec.Eth1Data(deposit_count=vote)
        if deposits == 0:
            # No deposit of the contract is left, so the block needs none.
            state.eth1_data.deposit_count = state.eth1_deposit_index
    if hasattr(body, "sync_aggregate"):
        body.sync_aggregate = sync_aggregate(spec, fork, state, [seed, sync_ok])
    if hasattr(body, "execution_payload"):
        made = spec.ExecutionPayload(
            parent_hash=state.latest_execution_payload_header.block_hash,
            prev_randao=spec.get_randao_mix(state, epoch),
            timestamp=spec.compute_time_at_slot(state.genesis_time, state.slot),
            block_hash=sha(b"block hash"),
        )
        if hasattr(made, "withdrawals"):
            made.withdrawals = withdrawals_payload(spec, fork, state, [0]).withdrawals
        if payload == 1:
            made.parent_hash = b"\x05" * 32
        elif payload == 2:
            made.prev_randao = b"\x06" * 32
        elif payload == 3:
            made.timestamp = made.timestamp + 1
        body.execution_payload = made
    if hasattr(body, "blob_kzg_commitments"):
        commitments = [b"\xc0" + bytes(47)] * blobs
        body.blob_kzg_commitments = field_of(
            spec.BeaconBlockBody, "blob_kzg_commitments", commitments
        )
    return spec.BeaconBlock(
        slot=(int(state.slot) + slot_delta) % 2**64,
        proposer_index=(proposer + proposer_delta) % 2**64,
        parent_root=state.latest_block_header.hash_tree_root() if parent_ok else sha(b"x"),
        body=body,
    )


OPERATIONS = {
    "process_execution_payload_bid": payload_bid,
    "process_builder_deposit_request": builder_deposit_request,
    "process_builder_exit_request": builder_exit_request,
    "process_block": block,
    "process_voluntary_exit": voluntary_exit,
    "process_proposer_slashing": proposer_slashing,
    "process_attestation": attestation,
    "process_bls_to_execution_change": bls_change,
    "process_deposit_request": deposit_request,
    "process_deposit": deposit,
    "process_withdrawal_request": withdrawal_request,
    "process_consolidation_request": consolidation_request,
    "process_sync_aggregate": sync_aggregate,
}


def prepare(spec, fork, state, call, words):
    """The argument in hexadecimal and the function that applies the call."""
    if not call.startswith("upgrade_to_") and not hasattr(spec, call):
        # The fork has no such function.
        raise SkipError()
    if call in MUTATORS or call in READERS:
        function = getattr(spec, call)
        return "-", lambda: function(state)
    if call in ("get_beacon_committee", "get_block_root_at_slot"):
        # The slot comes as its epoch and its place in the epoch.
        epoch, offset, *rest = numbers(words[0])
        slot = spec.Slot((epoch * int(spec.SLOTS_PER_EPOCH) + offset) % 2**64)
        rest = [spec.Uint64(r) for r in rest]
        function = getattr(spec, call)
        return "-", lambda: function(state, slot, *rest)
    if call in OPERATIONS:
        operation = OPERATIONS[call](spec, fork, state, numbers(words[0]))
        function = getattr(spec, call)
        if call == "process_attestation" and since(fork, "gloas"):
            parent = numbers(words[1])[0]
            return hexof(operation), lambda: function(state, operation, parent)
        return hexof(operation), lambda: function(state, operation)
    if call == "process_attester_slashing":
        operation = attester_slashing(spec, fork, state, words)
        return hexof(operation), lambda: spec.process_attester_slashing(state, operation)
    if call == "get_attesting_indices":
        operation = attestation(spec, fork, state, numbers(words[0]))
        return hexof(operation), lambda: sorted(spec.get_attesting_indices(state, operation))
    if call == "process_withdrawals":
        if since(fork, "gloas"):
            return "-", lambda: spec.process_withdrawals(state)
        payload = withdrawals_payload(spec, fork, state, numbers(words[0]))
        return hexof(payload), lambda: spec.process_withdrawals(state, payload)
    if call == "get_expected_withdrawals":
        return "-", lambda: show_withdrawals(spec, state)
    if call == "process_slots":
        (count,) = numbers(words[0])
        return "-", lambda: spec.process_slots(state, state.slot + count)
    if call == "slash_validator":
        index, whistleblower = words64(spec, words[0])
        reporter = None if whistleblower == FAR else whistleblower
        return "-", lambda: spec.slash_validator(state, index, reporter)
    if call in NUMBER_MUTATORS:
        f = words64(spec, words[0])
        function = getattr(spec, call)

        def mutate():
            function(state, *f)

        return "-", mutate
    if call in NUMBER_READERS:
        f = words64(spec, words[0])
        function = getattr(spec, call)
        return "-", lambda: function(state, *f)
    if call == "get_seed":
        epoch, domain = numbers(words[0])
        kind = getattr(spec, DOMAINS[domain % len(DOMAINS)])
        return "-", lambda: spec.get_seed(state, spec.Epoch(epoch), kind)
    if call == "get_domain":
        domain, epoch = numbers(words[0])
        kind = getattr(spec, DOMAINS[domain % len(DOMAINS)])
        at = None if epoch == FAR else spec.Epoch(epoch)
        return "-", lambda: spec.get_domain(state, kind, at)
    if call == "compute_proposer_index":
        seed = sha(words[0].encode())
        indices = words64(spec, words[1]) if len(words) > 1 else []
        return "-", lambda: spec.compute_proposer_index(state, indices, seed)
    if call.startswith("upgrade_to_"):
        target = __import__(f"eth_consensus_specs.{call[11:]}.minimal", fromlist=["minimal"])
        return "-", lambda: getattr(target, call)(state)
    raise ValueError(f"unknown call {call}")


def verify_branch(leaf, index, root, branch):
    """The check of a Merkle branch, as `is_valid_merkle_branch` of Phase 0."""
    value = leaf
    for height, sibling in enumerate(branch):
        if index >> height & 1:
            value = sha(sibling + value)
        else:
            value = sha(value + sibling)
    return value == root


def pure(spec_of, call, arguments):
    """A helper that needs no state."""
    if call == "deposit_root":
        # The root of the deposit contract over leaves, by a naive tree.
        leaves = [bytes.fromhex(a) for a in arguments]
        root, _ = merkle_root_and_branch(leaves, 0, 32)
        return sha(root + len(leaves).to_bytes(32, "little")).hex()
    if call == "deposit_proof":
        leaf, index, root, branch = arguments
        raw = bytes.fromhex(branch)
        nodes = [raw[i : i + 32] for i in range(0, len(raw), 32)]
        ok = len(nodes) == 33 and verify_branch(
            bytes.fromhex(leaf), int(index), bytes.fromhex(root), nodes
        )
        return "true" if ok else "false"
    if call == "shuffle":
        preset, count, seed = arguments
        spec = __import__(f"eth_consensus_specs.phase0.{preset}", fromlist=[preset])
        count = spec.Uint64(int(count))
        out = [
            int(spec.compute_shuffled_index(spec.Uint64(i), count, bytes.fromhex(seed)))
            for i in range(int(count))
        ]
        return "[" + ",".join(map(str, out)) + "]"
    if call == "committee":
        preset, seed, index, count, *indices = arguments
        spec = __import__(f"eth_consensus_specs.phase0.{preset}", fromlist=[preset])
        members = [spec.ValidatorIndex(int(i)) for i in indices]
        out = spec.compute_committee(
            members, bytes.fromhex(seed), spec.Uint64(int(index)), spec.Uint64(int(count))
        )
        return "[" + ",".join(str(int(i)) for i in out) + "]"
    if call == "constants":
        return constants(arguments)
    if call == "genesis":
        return genesis(arguments)
    if call == "schedule":
        return scheduled(arguments)
    if call == "time":
        return timed(arguments)
    raise ValueError(f"unknown call {call}")


def genesis(arguments):
    """Phase 0: the genesis state of deposits, each proved against the tree so far.

    The answer is the deposits, then the root of the state and whether it launches.
    """
    from eth_consensus_specs.phase0 import minimal as spec

    timestamp, *words = arguments
    datas = [deposit_data(spec, numbers(word)) for word in words]
    leaves = [bytes(d.hash_tree_root()) for d in datas]
    deposits = []
    for i, data in enumerate(datas):
        _, branch = merkle_root_and_branch(leaves[: i + 1], i, 32)
        proof = branch + [(i + 1).to_bytes(32, "little")]
        deposits.append(spec.Deposit(proof=field_of(spec.Deposit, "proof", proof), data=data))
    sent = b"".join(bytes(d.encode_bytes()) for d in deposits).hex() or "-"
    try:
        state = spec.initialize_beacon_state_from_eth1(
            sha(b"eth1"), spec.Uint64(int(timestamp)), deposits
        )
    except Exception as e:
        return f"{sent} error:{type(e).__name__}"
    valid = "true" if spec.is_valid_genesis_state(state) else "false"
    return f"{sent} ok:{bytes(state.hash_tree_root()).hex()}:{valid}"


def constants(arguments):
    """Compare named values, as `NAME := value` text, with those of the specification.

    A value is a number or a vector of bytes; a name the specification lacks is skipped.
    """
    import re

    preset, text = arguments
    # The latest fork that names a value decides it: Heze drops some of Electra's.
    specs = [
        __import__(f"eth_consensus_specs.{fork}.{preset}", fromlist=[preset])
        for fork in reversed(ORDER)
    ]
    text = bytes.fromhex(text).decode()
    wrong, matched, skipped, seen = [], 0, [], set()
    for name, raw in re.findall(r"([A-Z][A-Z0-9_]+) := (#v\[[^\]]*\]|0x[0-9a-fA-F]+|[0-9]+)", text):
        if name in seen:
            # An entry of the blob schedule repeats the name of a value: the first is it.
            continue
        seen.add(name)
        found = (getattr(m, name, getattr(m.config, name, None)) for m in specs)
        known = next((value for value in found if value is not None), None)
        if known is None:
            skipped.append(name)
            continue
        if raw.startswith("#v"):
            got = bytes(int(b, 0) for b in raw[3:-1].split(",") if b.strip()).hex()
            want = bytes(known).hex()
        else:
            got, want = int(raw, 0), int(known)
        if got == want:
            matched += 1
        else:
            wrong.append(f"{name}:ethlib={got},spec={want}")
    if wrong:
        return "differ:" + ";".join(wrong)
    return f"ok:{matched}_agree,_not_in_the_specification:{','.join(skipped) or 'none'}"


SCHEDULE_FORKS = ["ALTAIR", "BELLATRIX", "CAPELLA", "DENEB", "ELECTRA", "FULU", "GLOAS", "HEZE"]


def scheduled(arguments):
    """A function of the fork schedule, under fork epochs and a blob schedule."""
    from eth_consensus_specs.heze import mainnet as spec
    from frozendict import frozendict

    what, epochs, blobs, epoch, root = arguments
    entries = [e.split(":") for e in blobs.split(";")] if blobs != "-" else []
    saved = spec.config
    spec.config = saved._replace(
        BLOB_SCHEDULE=tuple(
            frozendict(EPOCH=spec.Epoch(int(e)), MAX_BLOBS_PER_BLOCK=spec.Uint64(int(m)))
            for e, m in entries
        ),
        **{
            f"{name}_FORK_EPOCH": spec.Epoch(int(e))
            for name, e in zip(SCHEDULE_FORKS, epochs.split(","), strict=False)
        },
    )
    try:
        at = spec.Epoch(int(epoch))
        if what == "version":
            return bytes(spec.compute_fork_version(at)).hex()
        if what == "blobs":
            parameters = spec.get_blob_parameters(at)
            return f"{int(parameters.epoch)}:{int(parameters.max_blobs_per_block)}"
        if what == "digest":
            return bytes(spec.compute_fork_digest(bytes.fromhex(root), at)).hex()
        raise ValueError(what)
    finally:
        spec.config = saved


def timed(arguments):
    """A function of time, with the minimal preset and configuration."""
    from eth_consensus_specs.heze import minimal as spec

    what, *rest = arguments
    a, b = (spec.Uint64(int(x)) for x in (rest + ["0"])[:2])
    try:
        if what == "compute_time_at_slot":
            return str(int(spec.compute_time_at_slot(a, b)))
        if what == "compute_slot_at_time":
            return str(int(spec.compute_slot_at_time(a, b)))
        if what == "compute_time_at_slot_ms":
            return str(int(spec.compute_time_at_slot_ms(a, b)))
        if what == "compute_slot_at_time_ms":
            return str(int(spec.compute_slot_at_time_ms(a, b)))
        return str(int(getattr(spec, what)(a)))
    except Exception as e:
        return f"error:{type(e).__name__}"

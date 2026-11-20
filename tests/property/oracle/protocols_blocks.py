"""Whole blocks for the consensus oracle: every field filled, several operations, a signature."""

# `consensus_ops.py` builds a block whose payload and votes are mostly zero.
# It builds no block with more than one operation.
# The earlier driver left some fields of the state and of the block at their defaults.
# Here a seed fills every such field, so that a definition which drops or swaps a field differs.
#
#     fill=<seed>        A word of a state: the fields that `consensus.py` leaves at zero.
#     process_block_full <block numbers> <counts>
#     process_operations <block numbers> <counts>
#     process_execution_payload <block numbers> <counts>
#     state_transition <block numbers> <counts> <ahead,signature,root,validate>
#
# The first counts are proposer slashings, attester slashings, attestations, deposits and exits.
# Then BLS changes, deposit requests, withdrawal requests, consolidation requests and transactions.
# Then the seed of the payload, and the answer of the execution layer.
# The answer is 0 to accept, 1 to refuse, or 2 to answer from a digest of the request it was given.
# `engineDigest` of the driver answers from such a digest too.

import hashlib

import consensus_ops as ops

FAR = 2**64 - 1


def sha(*parts):
    return hashlib.sha256(b"".join(parts)).digest()


def blob(seed, label, length):
    """Bytes of a length from a seed and a label."""
    out = b""
    counter = 0
    while len(out) < length:
        out += sha(seed.to_bytes(8, "little"), label.encode(), counter.to_bytes(4, "little"))
        counter += 1
    return out[:length]


def of_kind(old, data):
    """Bytes in the type of the value they replace: a byte list takes them as `data`."""
    kind = type(old)
    try:
        return kind(data)
    except TypeError:
        return kind(data=data)


def number(seed, label, limit):
    return int.from_bytes(blob(seed, label, 8), "little") % limit


def fill(spec, fork, state, seed):
    """Set the fields of a state that the words leave at their default."""
    has = type(state).model_fields.__contains__
    state.genesis_time = [0, 1578009600, number(seed, "genesis", 2**40)][seed % 3]
    if has("eth1_data"):
        state.eth1_data.deposit_root = blob(seed, "deposit root", 32)
        state.eth1_data.block_hash = blob(seed, "eth1 block hash", 32)
    state.latest_block_header.proposer_index = number(seed, "proposer", 2**20)
    if seed % 2:
        state.latest_block_header.state_root = blob(seed, "header state root", 32)
    if has("latest_execution_payload_header"):
        header = state.latest_execution_payload_header
        for name, annotation in type(header).model_fields.items():
            kind = annotation.annotation
            old = getattr(header, name)
            if name == "extra_data":
                value = blob(seed, name, number(seed, "extra length", 33))
                setattr(header, name, of_kind(old, value))
            elif name == "base_fee_per_gas":
                setattr(header, name, kind(int.from_bytes(blob(seed, name, 32), "little")))
            elif isinstance(old, int):
                setattr(header, name, kind(number(seed, name, 2**64)))
            else:
                setattr(header, name, of_kind(old, blob(seed, name, len(bytes(old)))))
        if seed % 5 == 0 and not has("next_withdrawal_index"):
            # Before the merge the header is empty, and Bellatrix may carry no payload.
            state.latest_execution_payload_header = type(header)()
    if has("historical_summaries"):
        for i in range(seed % 4):
            state.historical_summaries.append(
                spec.HistoricalSummary(
                    block_summary_root=blob(seed, f"block summary {i}", 32),
                    state_summary_root=blob(seed, f"state summary {i}", 32),
                )
            )
    if has("latest_execution_payload_bid"):
        bid = state.latest_execution_payload_bid
        bid.parent_block_hash = blob(seed, "bid parent hash", 32)
        bid.parent_block_root = blob(seed, "bid parent root", 32)
        bid.prev_randao = blob(seed, "bid randao", 32)
        bid.fee_recipient = blob(seed, "bid fee recipient", 20)
        bid.gas_limit = number(seed, "bid gas limit", 2**64)
        bid.slot = max(int(state.slot), 1) - 1 if seed % 4 else number(seed, "bid slot", 2**20)
        bits = blob(seed, "available", len(state.execution_payload_availability) // 8 + 1)
        for i in range(len(state.execution_payload_availability)):
            state.execution_payload_availability[i] = bool(bits[i // 8] >> (i % 8) & 1)


def engine_digest(spec, request):
    """What the test execution layer hashes of a request: every part that a fork passes."""
    parts = [bytes(request.execution_payload.hash_tree_root())]
    if hasattr(request, "versioned_hashes"):
        parts += [bytes(h) for h in request.versioned_hashes]
        parts.append(bytes(request.parent_beacon_block_root))
    if hasattr(request, "execution_requests"):
        parts += [
            bytes(item) for item in spec.get_execution_requests_list(request.execution_requests)
        ]
    return sha(*parts)


class Engine:
    """An execution layer that accepts, refuses, or answers from the request it is given."""

    def __init__(self, spec, mode):
        self.spec = spec
        self.mode = mode

    def verify_and_notify_new_payload(self, request):
        if self.mode == 2:
            return engine_digest(self.spec, request)[0] % 4 != 0
        return self.mode == 0


def with_engine(spec, mode, apply):
    """Run a function with the execution layer of a mode in place of the default one."""

    def run():
        if not hasattr(spec, "EXECUTION_ENGINE"):
            return apply()
        saved = spec.EXECUTION_ENGINE
        spec.EXECUTION_ENGINE = Engine(spec, mode)
        try:
            return apply()
        finally:
            spec.EXECUTION_ENGINE = saved

    return run


def deposits_for(spec, fork, state, count, seed):
    """Deposits of consecutive indices, proved against one tree whose root the state gets."""
    start = seed % 3
    datas = [
        ops.deposit_data(
            spec, [40 + (seed + i) % 20, 1 + i % 2, i, (1 + i % 40) * 10**9, i % 5 != 4]
        )
        for i in range(start + count)
    ]
    leaves = [bytes(d.hash_tree_root()) for d in datas]
    length = len(leaves).to_bytes(32, "little")
    root, _ = ops.merkle_root_and_branch(leaves, 0, 32)
    state.eth1_data.deposit_root = sha(root, length)
    state.eth1_data.deposit_count = len(leaves)
    state.eth1_deposit_index = start
    made = []
    for index in range(start, start + count):
        _, branch = ops.merkle_root_and_branch(leaves, index, 32)
        proof = ops.field_of(spec.Deposit, "proof", branch + [length])
        made.append(spec.Deposit(proof=proof, data=datas[index]))
    return made


def fill_payload(spec, fork, state, payload, seed, transactions):
    """Set every field of a payload that validity does not fix."""
    payload.fee_recipient = blob(seed, "fee recipient", 20)
    payload.state_root = blob(seed, "state root", 32)
    payload.receipts_root = blob(seed, "receipts root", 32)
    bloom = blob(seed, "bloom", len(bytes(payload.logs_bloom)))
    payload.logs_bloom = of_kind(payload.logs_bloom, bloom)
    payload.block_number = number(seed, "block number", 2**64)
    payload.gas_limit = number(seed, "gas limit", 2**64)
    payload.gas_used = number(seed, "gas used", 2**64)
    extra = blob(seed, "extra", number(seed, "extra length", int(spec.MAX_EXTRA_DATA_BYTES) + 1))
    payload.extra_data = of_kind(payload.extra_data, extra)
    payload.base_fee_per_gas = int.from_bytes(blob(seed, "base fee", 32), "little")
    payload.block_hash = blob(seed, "block hash", 32)
    kind = type(payload).model_fields["transactions"].annotation
    made = []
    for i in range(transactions):
        # Lengths around the chunk of 32 bytes, and none: an empty transaction.
        length = [1, 31, 32, 33, 64, 65, 200, 0][number(seed, f"tx length {i}", 15) % 8]
        made.append(kind.ELEMENT_TYPE(data=blob(seed, f"tx {i}", length)))
    payload.transactions = kind(data=made)
    if hasattr(payload, "blob_gas_used"):
        payload.blob_gas_used = number(seed, "blob gas used", 2**64)
        payload.excess_blob_gas = number(seed, "excess blob gas", 2**64)


def full_block(spec, fork, state, words):
    """A block with several operations and every field filled, valid but for what is asked."""
    g = ops.numbers(words[0])
    gloas = ops.since(fork, "gloas")
    # The numbers of both kinds of block are in one word; each kind reads its own.
    f = [g[0], g[1], g[2], g[3], g[10], g[11], g[7], g[8], g[12], g[13], g[14]] if gloas else g[:10]
    (
        proposer_slashings,
        attester_slashings,
        attestations,
        deposits,
        exits,
        changes,
        deposit_requests,
        withdrawal_requests,
        consolidation_requests,
        transactions,
        seed,
        _engine,
    ) = ops.numbers(words[1])
    count = len(state.validators)

    def bounded(wanted, limit):
        """Before Gloas a list of a block has a limit in its type, and holds no more."""
        return wanted if gloas else min(wanted, int(getattr(spec, limit)))

    suffix = "_ELECTRA" if ops.since(fork, "electra") else ""
    proposer_slashings = bounded(proposer_slashings, "MAX_PROPOSER_SLASHINGS")
    attester_slashings = bounded(attester_slashings, "MAX_ATTESTER_SLASHINGS" + suffix)
    attestations = bounded(attestations, "MAX_ATTESTATIONS" + suffix)
    exits = bounded(exits, "MAX_VOLUNTARY_EXITS")
    if ops.since(fork, "capella"):
        changes = bounded(changes, "MAX_BLS_TO_EXECUTION_CHANGES")
    if ops.since(fork, "electra") and not gloas:
        deposit_requests = bounded(deposit_requests, "MAX_DEPOSIT_REQUESTS_PER_PAYLOAD")
        withdrawal_requests = bounded(withdrawal_requests, "MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD")
        consolidation_requests = bounded(
            consolidation_requests, "MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD"
        )
    made_deposits = []
    if deposits and not ops.since(fork, "fulu"):
        made_deposits = deposits_for(spec, fork, state, bounded(deposits, "MAX_DEPOSITS"), seed)
    if not gloas:
        # The last number says whether the state expects deposits: those made here, or none.
        f = f[:9] + [1 if made_deposits else 0]
    block = ops.block(spec, fork, state, f)
    body = block.body
    body.graffiti = blob(seed, "graffiti", 32)
    if hasattr(body, "eth1_data"):
        body.eth1_data.deposit_root = blob(seed % 3, "vote root", 32)
        body.eth1_data.block_hash = blob(seed % 3, "vote hash", 32)
    epoch = int(spec.get_current_epoch(state))
    used = set()

    def pick(fits=lambda v: True):
        """A validator that an operation accepts and no earlier one of the block took.

        Every seventh seed takes any validator, so that operations also meet and fail.
        """
        order = [(seed + 3 * i) % max(count, 1) for i in range(count)]
        for index in order:
            if seed % 7 == 0:
                used.add(index)
                return (index + len(used)) % max(count, 1)
            if index not in used and fits(state.validators[index]):
                used.add(index)
                return index
        return len(used) % max(count, 1)

    def slashable(v):
        return not v.slashed and v.activation_epoch <= epoch < v.withdrawable_epoch

    def exitable(v):
        old = epoch >= int(v.activation_epoch) + int(spec.config.SHARD_COMMITTEE_PERIOD)
        return slashable(v) and v.exit_epoch == FAR and old and epoch < v.exit_epoch

    slot = int(state.slot)
    for _ in range(proposer_slashings):
        body.proposer_slashings.append(
            ops.proposer_slashing(spec, fork, state, [pick(slashable), slot, 0, 1, 1, 0, 0])
        )
    for i in range(attester_slashings):
        pair = f"{pick(slashable)},{pick(slashable)}"
        body.attester_slashings.append(
            ops.attester_slashing(spec, fork, state, [f"{i % 3},1,1,1,1", pair, "="])
        )
    delay = int(spec.MIN_ATTESTATION_INCLUSION_DELAY)
    for i in range(attestations):
        back = delay + i
        if back > slot:
            break
        body.attestations.append(
            ops.attestation(spec, fork, state, [back, 0, seed + i, 1, 1, 1, 1, 1, 0, 0])
        )
    for deposit in made_deposits:
        body.deposits.append(deposit)
    for _ in range(exits):
        body.voluntary_exits.append(
            ops.voluntary_exit(spec, fork, state, [pick(exitable), epoch, 1])
        )
    if hasattr(body, "bls_to_execution_changes"):
        for i in range(changes):
            index = pick(lambda v: bytes(v.withdrawal_credentials)[0] == 0)
            body.bls_to_execution_changes.append(
                ops.bls_change(spec, fork, state, [index, 9, i, 1])
            )
    requests = getattr(body, "execution_requests", None)
    if requests is not None:
        for i in range(deposit_requests):
            fields = [60 + (seed + i) % 9, 1 + i % 2, i, (1 + i) * 10**9, i % 3 != 2, seed + i]
            requests.deposits.append(ops.deposit_request(spec, fork, state, fields))
        for i in range(withdrawal_requests):
            amount = [0, 10**9, 5 * 10**9][(seed + i) % 3]
            requests.withdrawals.append(
                ops.withdrawal_request(spec, fork, state, [9, pick(exitable), amount])
            )
        for i in range(consolidation_requests):
            source = pick(exitable)
            target = source if i % 2 else pick(exitable)
            requests.consolidations.append(
                ops.consolidation_request(spec, fork, state, [9, source, target])
            )
    if hasattr(body, "execution_payload"):
        fill_payload(spec, fork, state, body.execution_payload, seed, transactions)
    return block


def signed_block(spec, fork, state, words):
    """A signed block some slots ahead of the state, with the root of the state after it."""
    ahead, signature_ok, root_ok, _validate = ops.numbers(words[2])
    # A block builder sets fields of the state it is given, so the state under test gets them.
    full_block(spec, fork, state, words)
    advanced = state.copy()
    if ahead:
        spec.process_slots(advanced, state.slot + ahead)
    block = full_block(spec, fork, advanced, words)
    mode = ops.numbers(words[1])[11]
    after = advanced.copy()
    try:
        with_engine(spec, mode, lambda: spec.process_block(after, block))()
        block.state_root = after.hash_tree_root()
    except Exception:
        block.state_root = sha(b"no state after")
    if root_ok == 0:
        block.state_root = sha(bytes(block.state_root))
    index = int(block.proposer_index)
    key = ops.key_at(advanced, index)
    domain = spec.get_domain(advanced, spec.DOMAIN_BEACON_PROPOSER)
    signature = ops.signed(spec, [key], block, domain, signature_ok)
    return spec.SignedBeaconBlock(message=block, signature=signature)


def prepare(spec, fork, state, call, words):
    """The argument and the function of a call of this module, or none for another call."""
    if call not in (
        "process_block_full",
        "process_operations",
        "process_execution_payload",
        "state_transition",
    ):
        return None
    mode = ops.numbers(words[1])[11]
    if call == "state_transition":
        try:
            signed = signed_block(spec, fork, state, words)
        except ops.SkipError:
            raise
        except Exception as e:
            raise ops.SkipError() from e
        validate = bool(ops.numbers(words[2])[3])
        return ops.hexof(signed), with_engine(
            spec, mode, lambda: spec.state_transition(state, signed, validate)
        )
    block = full_block(spec, fork, state, words)
    if call == "process_block_full":
        return ops.hexof(block), with_engine(spec, mode, lambda: spec.process_block(state, block))
    if call == "process_operations":
        if ops.since(fork, "gloas"):
            parent = state.latest_block_header.slot
            return ops.hexof(block.body), lambda: spec.process_operations(state, block.body, parent)
        return ops.hexof(block.body), lambda: spec.process_operations(state, block.body)
    if not hasattr(block.body, "execution_payload"):
        raise ops.SkipError()
    engine = Engine(spec, mode)
    return ops.hexof(block.body), lambda: spec.process_execution_payload(state, block.body, engine)

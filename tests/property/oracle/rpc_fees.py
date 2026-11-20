"""A model of eth_feeHistory, written from fee_market.yaml, the fee EIPs and go-ethereum."""

#     feehistory <activations> <schedules> <blocks> <marks> <count> <newest> <percentiles>
#
# An activation is `fork:b:number` or `fork:t:time`.
# Activations are joined with `,` in the order of the timeline.
# A schedule is `b|t:value:target:max:fraction`.
# A block is `fork|number,time,gas limit,gas used,base fee,excess blob gas,blob gas used|txs`.
# Blocks are joined with `;`.
# A transaction is `type:gas price:max fee:priority:gas used`, and they are joined with `/`.
# The marks are `safe&finalized&pending`: two block numbers and a block, each `-` for none.
# The percentiles are the JSON text of their array.
#
# The answer is `error <code>`, or seven fields joined with `|`.
# They are the oldest block, the base fees, the blob base fees, and the two lists of ratios.
# A ratio is `num/den`.
# The last two are the rewards by the exact rule and by the rule of go-ethereum.
# The rule of go-ethereum rounds in floats.
#
# The base fee is that of EIP-1559.
# The blob fee is that of EIP-4844, with the schedules of EIP-7691 and EIP-7892.
# The excess blob gas is that of EIP-4844 and, from Osaka, EIP-7918.
# The percentile rule is `processBlock` of go-ethereum's eth/gasprice/feehistory.go.

import importlib
import json
from fractions import Fraction

from ethereum_types.numeric import U64

ORDER = [
    "frontier",
    "homestead",
    "daoFork",
    "tangerineWhistle",
    "spuriousDragon",
    "byzantium",
    "constantinople",
    "petersburg",
    "istanbul",
    "muirGlacier",
    "phase0",
    "berlin",
    "london",
    "altair",
    "arrowGlacier",
    "grayGlacier",
    "bellatrix",
    "paris",
    "shapella",
    "dencun",
    "pectra",
    "fusaka",
    "bpo1",
    "bpo2",
    "bpo3",
    "bpo4",
    "bpo5",
    "glamsterdam",
    "hegota",
]
# The blob schedule of each fork: the target, the maximum and the update fraction.
# EIP-4844 gives Cancun's, EIP-7691 Prague's, and EIP-7892 with the BPO EIPs the others.
SCHEDULES = {
    "dencun": (3, 6, 3338477),
    "pectra": (6, 9, 5007716),
    "fusaka": (6, 9, 5007716),
    "bpo1": (10, 15, 8346193),
    "bpo2": (14, 21, 11684671),
}
# The module of the reference that has the blob constants of a fork.
EELS = {"dencun": "cancun", "pectra": "prague", "fusaka": "osaka", "bpo1": "bpo1", "bpo2": "bpo2"}
GAS_PER_BLOB = 2**17
BLOB_BASE_COST = 2**13
INITIAL_BASE_FEE = 1000000000


def since(fork, first):
    return ORDER.index(fork) >= ORDER.index(first)


def fake_exponential(factor, numerator, denominator):
    """The approximation of `factor * e ** (numerator / denominator)` of EIP-4844."""
    i = 1
    output = 0
    accumulator = factor * denominator
    while accumulator > 0:
        output += accumulator
        accumulator = (accumulator * numerator) // (denominator * i)
        i += 1
    return output // denominator


class Block:
    """A block of a view, from its text."""

    def __init__(self, text):
        self.fork, header, txs = text.split("|")
        (
            self.number,
            self.time,
            self.gas_limit,
            self.gas_used,
            self.base_fee,
            self.excess,
            self.blob_used,
        ) = (int(word) for word in header.split(",")[:7])
        self.txs = [] if txs == "-" else [[int(w) for w in tx.split(":")] for tx in txs.split("/")]

    def fee(self):
        return self.base_fee if since(self.fork, "london") else 0

    def tips(self):
        """The effective tip and the gas used of each transaction, as EIP-1559 defines the tip."""
        out = []
        for kind, gas_price, max_fee, priority, gas_used in self.txs:
            if kind < 2:
                out.append((gas_price - self.fee(), gas_used))
            else:
                out.append((min(priority, max_fee - self.fee()), gas_used))
        return out


class View:
    """The chain of a node: its forks, its blob schedules and its blocks."""

    def __init__(self, activations, schedules, blocks, marks):
        self.activations = [a.split(":") for a in activations.split(",")]
        self.schedules = [] if schedules == "-" else [s.split(":") for s in schedules.split(",")]
        self.blocks = [Block(text) for text in blocks.split(";")]
        safe, finalized, pending = marks.split("&")
        self.safe = None if safe == "-" else int(safe)
        self.finalized = None if finalized == "-" else int(finalized)
        self.pending = None if pending == "-" else Block(pending)

    def active(self, number, time):
        """The latest fork of the timeline that a block has reached."""
        reached = [
            fork
            for fork, kind, value in self.activations
            if (number if kind == "b" else time) >= int(value)
        ]
        return max(reached, key=ORDER.index) if reached else None

    def schedule(self, fork, number, time):
        """The blob schedule at a block: the last one that the chain sets, else the fork's."""
        own = None
        for kind, value, target, most, fraction in self.schedules:
            if (number if kind == "b" else time) >= int(value):
                own = (int(target), int(most), int(fraction))
        return own or SCHEDULES[fork]

    def by_number(self, number):
        return next((b for b in self.blocks if b.number == number), None)

    def resolve(self, name):
        if name == "latest":
            return self.blocks[-1]
        if name == "earliest":
            return self.blocks[0]
        if name == "pending":
            return self.pending
        if name == "safe":
            return None if self.safe is None else self.by_number(self.safe)
        if name == "finalized":
            return None if self.finalized is None else self.by_number(self.finalized)
        return self.by_number(int(name))

    def next_fork(self, block):
        """The fork of the child of a block, one second after it, never before its own."""
        fork = self.active(block.number + 1, block.time + 1)
        if fork is None or not since(fork, block.fork):
            return block.fork
        return fork

    def next_base_fee(self, block):
        """The base fee of the child of a block, by EIP-1559."""
        if not since(self.next_fork(block), "london"):
            return 0
        if not since(block.fork, "london"):
            return INITIAL_BASE_FEE
        target = block.gas_limit // 2
        fee = block.base_fee
        if block.gas_used == target:
            return fee
        if block.gas_used > target:
            return fee + max(fee * (block.gas_used - target) // target // 8, 1)
        return fee - fee * (target - block.gas_used) // target // 8

    def blob_fee(self, block):
        """The base fee per blob gas of a block, by EIP-4844, or 0 before Cancun."""
        if not since(block.fork, "dencun"):
            return 0
        schedule = self.schedule(block.fork, block.number, block.time)
        fee = fake_exponential(1, block.excess, schedule[2])
        # The module of the reference for the fork agrees, when the chain sets no schedule.
        if not self.schedules and block.fork in EELS and block.excess < 2**64:
            gas = importlib.import_module(f"ethereum.forks.{EELS[block.fork]}.vm.gas")
            assert int(gas.calculate_blob_gas_price(U64(block.excess))) == fee
        return fee

    def next_blob_fee(self, block):
        """The base fee per blob gas of the child of a block, or 0 before Cancun."""
        fork = self.next_fork(block)
        if not since(fork, "dencun") or not since(block.fork, "london"):
            return 0
        target, most, fraction = self.schedule(fork, block.number + 1, block.time + 1)
        excess, used = (block.excess, block.blob_used) if since(block.fork, "dencun") else (0, 0)
        target_gas = target * GAS_PER_BLOB
        if excess + used < target_gas:
            after = 0
        elif since(fork, "fusaka") and BLOB_BASE_COST * block.base_fee > GAS_PER_BLOB * (
            fake_exponential(1, excess, fraction)
        ):
            # EIP-7918: the blob fee stays above a share of the cost of the execution gas.
            after = excess + used * (most - target) // most
        else:
            after = excess + used - target_gas
        return fake_exponential(1, after, fraction)

    def blob_ratio(self, block):
        if not since(block.fork, "dencun"):
            return (0, 0)
        most = self.schedule(block.fork, block.number, block.time)[1]
        return (block.blob_used, most * GAS_PER_BLOB)


def reward(tips, percentile, floats):
    """The tip at a percentile of the gas used, of transactions sorted by tip."""
    if not tips:
        return 0
    tips = sorted(tips, key=lambda tip: tip[0])
    total = sum(gas for _, gas in tips)
    if floats:
        # In go-ethereum: `uint64(float64(gasUsed) * p / 100)`.
        threshold = int(float(total) * float(percentile) / 100)
    else:
        threshold = Fraction(total) * percentile / 100
    used = 0
    for tip, gas in tips:
        used += gas
        if used >= threshold:
            return tip
    return tips[-1][0]


def percentiles_of(text):
    """The percentiles of a JSON array, or none when one is no number from 0 to 100."""
    values = json.loads(text, parse_float=Fraction, parse_int=Fraction)
    if not isinstance(values, list):
        return None
    for value in values:
        if isinstance(value, bool) or not isinstance(value, Fraction):
            return None
        if value < 0 or value > 100:
            return None
    return values


def feehistory(activations, schedules, blocks, marks, count, newest, percentiles):
    view = View(activations, schedules, blocks, marks)
    wanted = percentiles_of(percentiles)
    ordered = wanted is not None and all(a < b for a, b in zip(wanted, wanted[1:], strict=False))
    last = view.resolve(newest)
    if wanted is None or not ordered:
        # Two faults in one request: the source does not say which is answered.
        return "error -32602" + (" or -32001" if last is None else "")
    if last is None:
        return "error -32001"
    count = int(count)
    held = view.blocks + ([view.pending] if view.pending else [])
    blocks = [b for b in held if last.number - count < b.number <= last.number]
    oldest = blocks[0].number if blocks else last.number + 1
    fees = [b.fee() for b in blocks] + [view.next_base_fee(last)]
    blob_fees = [view.blob_fee(b) for b in blocks] + [view.next_blob_fee(last)]
    ratios = [f"{b.gas_used}/{b.gas_limit}" for b in blocks]
    blob_ratios = ["{}/{}".format(*view.blob_ratio(b)) for b in blocks]

    def rewards(floats):
        if not wanted:
            return "none"
        rows = [",".join(str(reward(b.tips(), p, floats)) for p in wanted) for b in blocks]
        return ";".join(rows) or "-"

    def csv(items):
        return ",".join(str(item) for item in items) or "-"

    fields = [oldest, csv(fees), csv(blob_fees), csv(ratios), csv(blob_ratios)]
    return "|".join(str(f) for f in fields + [rewards(False), rewards(True)])


COMMANDS = {"feehistory": feehistory}

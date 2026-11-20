"""Forks, activations and blob schedules, written from the EIPs apart from EthLib."""

# The order of the forks: EIP-7568 up to Shapella, with the forks of the
# consensus layer where they activated on mainnet, then the meta EIPs
# EIP-7569, EIP-7600, EIP-7607, EIP-8134, EIP-8135, EIP-7773 and EIP-8081.

FORKS = [
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

DEPOSIT_CONTRACT = "00000000219ab540356cbb839cbe05303d7705fa"

# Mainnet: EIP-6953 for the blocks and for Shapella, EIP-3675 and EIP-7643 for
# Paris, EIP-7569, EIP-7600, EIP-7607, EIP-8134 and EIP-8135 for the times.
MAINNET = [
    ("frontier", "block", 0),
    ("homestead", "block", 1_150_000),
    ("daoFork", "block", 1_920_000),
    ("tangerineWhistle", "block", 2_463_000),
    ("spuriousDragon", "block", 2_675_000),
    ("byzantium", "block", 4_370_000),
    ("constantinople", "block", 7_280_000),
    ("petersburg", "block", 7_280_000),
    ("istanbul", "block", 9_069_000),
    ("muirGlacier", "block", 9_200_000),
    ("berlin", "block", 12_244_000),
    ("london", "block", 12_965_000),
    ("arrowGlacier", "block", 13_773_000),
    ("grayGlacier", "block", 15_050_000),
    ("paris", "block", 15_537_394),
    ("shapella", "time", 1_681_338_455),
    ("dencun", "time", 1_710_338_135),
    ("pectra", "time", 1_746_612_311),
    ("fusaka", "time", 1_764_798_551),
    ("bpo1", "time", 1_765_290_071),
    ("bpo2", "time", 1_767_747_671),
]

# Hoodi: the genesis file of eth-clients/hoodi, at the commit that the text of
# `ChainConfig.hoodi` pins, and EIP-7600 and EIP-7607 for the times.
# That file ends at `bpo2Time`: the change before it removed `amsterdamTime`.
# The Activation table of EIP-7773 has an empty row for Hoodi since 2026-11-18.
# So Glamsterdam has no activation on Hoodi.
HOODI = [
    ("frontier", "block", 0),
    ("homestead", "block", 0),
    ("tangerineWhistle", "block", 0),
    ("spuriousDragon", "block", 0),
    ("byzantium", "block", 0),
    ("constantinople", "block", 0),
    ("petersburg", "block", 0),
    ("istanbul", "block", 0),
    ("berlin", "block", 0),
    ("london", "block", 0),
    ("paris", "block", 0),
    ("shapella", "time", 0),
    ("dencun", "time", 0),
    ("pectra", "time", 1_742_999_832),
    ("fusaka", "time", 1_761_677_592),
    ("bpo1", "time", 1_762_365_720),
    ("bpo2", "time", 1_762_955_544),
]

NETWORKS = {"mainnet": (1, MAINNET), "hoodi": (560048, HOODI)}

# Target, maximum and update fraction: EIP-4844, EIP-7691, EIP-8134, EIP-8135.
# EIP-7892 gives a fork without parameters of its own those of the fork before.
BLOB = {
    "dencun": (3, 6, 3338477),
    "pectra": (6, 9, 5007716),
    "bpo1": (10, 15, 8346193),
    "bpo2": (14, 21, 11684671),
}


def active(network, number, timestamp):
    # The table is in the order of the timeline: the last one reached is active.
    found = "none"
    for fork, kind, at in NETWORKS[network][1]:
        if (number if kind == "block" else timestamp) >= at:
            found = fork
    return found


def blob(fork):
    held = None
    for name in FORKS:
        held = BLOB.get(name, held)
        if name == fork:
            return "none" if held is None else " ".join(str(x) for x in held)
    return "error unknown fork"


def gas_limit(parent, target):
    # `is_gas_limit_target_compatible` of the Gloas fork choice: the one limit it accepts.
    difference = max(parent // 1024, 1) - 1
    lowest, highest = parent - difference, parent + difference
    if target < lowest:
        return lowest
    if target > highest:
        return highest
    return target


def answer(words):
    match words:
        case ["gaslimit", parent, target]:
            return str(gas_limit(int(parent), int(target)))
        case ["forks"]:
            return " ".join(FORKS)
        case ["active", network, number, timestamp]:
            return active(network, int(number), int(timestamp))
        case ["network", network]:
            chain, table = NETWORKS[network]
            rows = " ".join(f"{fork}={kind}:{at}" for fork, kind, at in table)
            return f"{chain} {DEPOSIT_CONTRACT} {rows}"
        case ["blob", fork]:
            return blob(fork)
    return None

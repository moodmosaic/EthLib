"""The executable consensus-specs at any preset and configuration, with or without real BLS."""

# A preset is `minimal` or `mainnet`, then `;NAME=value` for each constant that differs.
# The modules of consensus-specs hold their constants as literals, one module per fork.
# A fork reads the types of the fork before it.
# So a preset is built by running the source of each fork again, in order.
# Each run has the literals replaced and the earlier forks taken from the same build.
#
# A configuration is `-` or `NAME=value;...`, set on the `config` of the module for one call.

import importlib.util
import os
import re
import sys
import types

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
SOURCES = {}
BUILT = {}
BASE_CONFIG = {}


def source_of(fork, base):
    """The source text of a fork at a named preset, and its path."""
    if (fork, base) not in SOURCES:
        path = importlib.util.find_spec(f"eth_consensus_specs.{fork}.{base}").origin
        with open(path) as handle:
            SOURCES[fork, base] = (handle.read(), path)
    return SOURCES[fork, base]


def parse(key):
    """The base and the changed constants of a preset key."""
    base, *changes = key.split(";")
    return base, {name: int(value) for name, _, value in (c.partition("=") for c in changes)}


def spec_of(fork, key):
    """The module of a fork at a preset, built on the forks before it at the same preset."""
    if (fork, key) in BUILT:
        return BUILT[fork, key]
    base, changes = parse(key)
    # `PROTOCOLS_MUTANT=NAME=value` gives the reference a constant that the driver does not have.
    # This is to see that a property notices: a run with it must fail.
    if "=" in os.environ.get("PROTOCOLS_MUTANT", ""):
        name, _, value = os.environ["PROTOCOLS_MUTANT"].partition("=")
        changes[name] = int(value)
    if not changes:
        module = importlib.import_module(f"eth_consensus_specs.{fork}.{base}")
        BUILT[fork, key] = module
        return module
    chain = {name: spec_of(name, key) for name in FORKS[: FORKS.index(fork)]}
    text, path = source_of(fork, base)
    text = re.sub(
        r"^from eth_consensus_specs\.(\w+) import (?:minimal|mainnet) as (\w+)$",
        r'\2 = _CHAIN["\1"]',
        text,
        flags=re.M,
    )
    for name, value in changes.items():
        text = re.sub(rf"^{name} = (\w+)\(.*\)$", rf"{name} = \1({value})", text, flags=re.M)
    # A constant that the source derives from others is a literal in the module.
    text = re.sub(
        r"^UPDATE_TIMEOUT = Slot\(.*\)$",
        "UPDATE_TIMEOUT = Slot(int(SLOTS_PER_EPOCH) * int(EPOCHS_PER_SYNC_COMMITTEE_PERIOD))",
        text,
        flags=re.M,
    )
    name = f"protocols_spec_{len(BUILT)}_{fork}"
    module = types.ModuleType(name)
    module.__file__ = path
    module._CHAIN = chain
    sys.modules[name] = module
    exec(compile(text, path, "exec"), module.__dict__)
    BUILT[fork, key] = module
    return module


def typed(spec, name, old, text):
    """A value of a configuration in the type of the one it replaces."""
    if isinstance(old, (bytes, bytearray)):
        # A fork version is sent as the number that its bytes spell.
        return type(old)(int(text).to_bytes(len(old), "big"))
    return type(old)(int(text))


def configure(spec, key):
    """Set the configuration of a module: its own, with the values of the key."""
    if id(spec) not in BASE_CONFIG:
        BASE_CONFIG[id(spec)] = spec.config
    base = BASE_CONFIG[id(spec)]
    if key == "-":
        spec.config = base
        return
    changes = {}
    for change in key.split(";"):
        name, _, text = change.partition("=")
        if hasattr(base, name):
            changes[name] = typed(spec, name, getattr(base, name), text)
    spec.config = base._replace(**changes)


def configure_chain(fork, preset, key):
    """The module of a fork with a configuration, set on every fork up to it.

    An upgrade function reads the configuration of its own fork.
    """
    for name in FORKS[: FORKS.index(fork) + 1]:
        configure(spec_of(name, preset), key)
    return spec_of(fork, preset)

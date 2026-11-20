# Property tests

Property tests of EthLib, written with [lean-hedgehog](https://github.com/hedgehogqa/lean-hedgehog).

EthLib's theorems are stated about its definitions, so they hold for the code that runs.
They do not say that a definition is the function its source defines.
A driver here generates inputs and requires an answer that EthLib did not compute.
When the two disagree, the input shrinks to the smallest that still does.

This is a separate Lake package, as `tests/downstream` is, so EthLib gains no dependency.

## Where an answer comes from

- A reference implementation written apart from EthLib, in another process (`oracle/<layer>.py`).
- Arithmetic on `Nat` and `Int`, for a definition on fixed-width words.
- An inverse: what is written reads back, and what reads is what the writer writes.
- A model: a sequence of operations on a state against a simple reference of that state.
- A rule of the source: an input that the source refuses is refused.

## Running

```bash
lake build EthLib                      # At the repository root, once.
cd tests/property
uv venv .venv
uv pip install --python .venv/bin/python -r oracle/requirements.txt
lake exe base-property                 # 100 cases of each property.
lake exe base-property 20000
```

A driver takes the number of cases as its argument.
`ETHLIB_ORACLE_PYTHON` names another interpreter for the oracles.

Every driver takes its selection from the environment, as lean-hedgehog reads it.
`HEDGEHOG_ONLY` holds parts of the names of the properties to run, separated by commas.
`HEDGEHOG_RECHECK` holds the size and the two numbers of the seed that a failure report prints.
The driver then runs that one case again.
The consensus driver also takes the names of its groups as arguments.

`oracle/requirements.txt` is enough for the base driver.
Each other driver has `oracle/requirements-<layer>.txt`, which lists its references with their versions.
Some say in a comment how to install a reference whose own dependencies do not resolve with the others.

A report lists the kinds of case that a property names, each with its share of the cases.
A kind with a minimum fails the property when a long run stays under it, so a generator that stops reaching a rule fails the run.

A property that found something is kept in a group of findings that must fail, so that a run shows the counterexample.
The driver fails when such a property passes: the finding is gone, and the property moves to the passing group.

## Drivers

| Driver | What it compares EthLib with |
| --- | --- |
| `base-property` | the Python standard library, and arithmetic on `Nat` and `Int` |
| `kernels-property` | Python integers, py_ecc, and each constant table computed from its standard |
| `serialization-property` | `ssz-specs`, remerkleable, the `rlp` package, `cryptography` for DER |
| `hashes-property` | hashlib, `cryptography`, pycryptodome, crc32c |
| `curves-property` | coincurve, eth-keys, OpenSSL, py_ecc, arkworks, milagro, c-kzg-4844 |
| `networking-property` | cramjam, aioquic, noiseprotocol, and references written from the texts |
| `decoders-property` | the `protobuf` package, aioquic, `cryptography`, and readers written from the texts |
| `evm-property` | the Python execution-specs, at every fork they have |
| `execution-property` | the Python execution-specs, eth-account, py-trie, eth-bloom |
| `transition-property` | the Python execution-specs, on whole transactions and whole blocks |
| `rpc-property` | the Python execution-specs, py-trie, and models written from execution-apis |
| `consensus-property` | pyspec at the commit that `tests/sources.toml` pins |
| `forkchoice-property` | the same pyspec, and a model of slashing protection from EIP-3076 |
| `protocols-property` | the same pyspec, rebuilt at other presets, with real BLS |
| `engine-property` | models written from execution-apis, and PyJWT |

Each driver tests state in both ways that lean-hedgehog has: a state machine whose transitions are one type, and a scenario of commands that are each a type.

## Layout

| Path | What it holds |
| --- | --- |
| `Property/<Layer>.lean` | the driver of a layer, an executable |
| `Property/<Layer>/*.lean` | the modules a driver imports |
| `Support/` | generators, hexadecimal and the oracle process |
| `oracle/<layer>.py` | the reference implementations of a layer, one command per line |
| `findings/<layer>.md` | what a driver found, and how to see it again |

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
python3 -m venv .venv && .venv/bin/pip install -r oracle/requirements.txt
lake exe base-property                 # 100 cases of each property.
lake exe base-property 20000
```

A driver takes the number of cases as its argument.
`ETHLIB_ORACLE_PYTHON` names another interpreter for the oracles.

## Layout

| Path | What it holds |
| --- | --- |
| `Property/<Layer>.lean` | the driver of a layer, an executable |
| `Property/<Layer>/*.lean` | the modules a driver imports |
| `Support/` | generators, hexadecimal and the oracle process |
| `oracle/<layer>.py` | the reference implementations of a layer, one command per line |
| `findings/<layer>.md` | what a driver found, and how to see it again |

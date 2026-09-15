# Python implementation

The Python port is the readable reference for a reviewer who works in Python.
Review it against [Lean Float](lean-implementation.md), then run its differential
tests. Native source correspondence is tested, not proved.

## Numerical code and API

The numerical implementation is in
[ephemeris/](../python/ephemeris):

```text
ephemeris/
  __init__.py
  message.py
  position_reconstruction.py
```

| Module | Purpose |
| --- | --- |
| [message.py](../python/ephemeris/message.py) | Shared bounded Message, ReceiverError, tick arithmetic, and validation. |
| [position_reconstruction.py](../python/ephemeris/position_reconstruction.py) | Fixed-point-message receiver using bounded integers and binary64. |

The receiver accepts the [decoded input contract](paper-and-spec.md#decoded-input-contract).
Python integers and their intermediates are explicitly bounded to match the
corresponding Rust operations. Coefficients are copied into immutable tuples;
shape and profile ranges are checked by evaluation. The implementation requires
binary64 precision/exponent range and round-to-nearest from the host Python runtime.

```python
from ephemeris import Message, evaluate_float
from ephemeris.message import start_tick

message = Message(
    day_offset=0, second_of_day=43200, validity_code=2,
    coefficients=([3200, 640] + [0] * 9, [0] * 11, [0] * 11),
)
start = start_tick(message)
assert evaluate_float(message, start) == (80.0, 0.0, 0.0)
assert evaluate_float(message, start + 1800000000) == (100.0, 0.0, 0.0)
assert evaluate_float(message, start + 3600000000) == (120.0, 0.0, 0.0)
```

`evaluate_float(message, time)` returns an XYZ tuple of floats in meters. It raises
`ReceiverError` with a `.code` for the [shared numerical rejections](lean-implementation.md#validation-and-arithmetic).
Wrong representation types and out-of-carrier values raise `TypeError` or
`ValueError` before numerical evaluation. Bools and floats are not implicitly
accepted as integers. Tick subtraction precedes float conversion; all recurrence
and accumulation operations retain Lean's grouping and order.

A constant or lower-degree trajectory uses eleven coefficients with unused
terms set to zero.

## Install and test

Python 3.11+ is required; the numerical package uses the standard library.
From the repository root:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -e ./python
lake build
python -m fuzz.drivers.float --mode lean-python --cases 1000 --seed 20260911
```

See the [development guide](development.md) for Ruff setup, formatting and linting,
and the `make test-python` target that builds the required Lean/Rust oracles.

This fuzz command compares Python with Lean without requiring Rust. For the
full regression suite, build the Rust oracle as well:

```sh
cargo build --manifest-path rust/Cargo.toml --release --locked
python -m unittest discover -s python/tests -v
```

Without installation, prefix Python module commands with `PYTHONPATH=python`.
Installed tooling can locate external executables through explicit client paths,
`PATH`, `EPHEMERIS_FLOAT_ORACLE`, and `EPHEMERIS_RUST_ORACLE`; a wheel does not bundle
Lean/Rust executables. Source-checkout clients discover the local build outputs.
The installed driver can write reports without Lean/Rust sources present;
missing sources are listed explicitly alongside selected executable hashes.

## Fuzzing organization and method

Everything used to drive or support fuzzing is under
[python/fuzz/](../python/fuzz):

```text
fuzz/
  drivers/float.py                 generation, comparison, reports, replay
  oracles/python_float.py          standalone P3 JSON-line server
  shared/                         protocols, clients, cases, reports
  benchmarks/float_processes.py    process timing
```

The numerical package does not import these tools. Oracles do not import drivers.
Regression tests remain in [python/tests/](../python/tests). Bit-pattern encoding
and decoding live in `fuzz/shared/float_protocol.py`; they are not numerical APIs.
The [shared guide](fuzzing.md) defines comparison modes, coverage,
protocols, reproduction, replay, and the limits of differential evidence.

## Results

The Python suite has **18 passing tests**, covering bounded carriers and profile
validation, hand-calculated positions, input copying, subprocess recovery,
Lean model/native/Python/Rust comparisons, strict JSON array/number tokens,
installed-driver reports, and replay provenance. The package contains `message.py`
and `position_reconstruction.py`; the numerical implementation is separate from
fuzz infrastructure.
A fresh wheel was installed outside the checkout and checked against every oracle
backend. Build release wheels from a clean source tree so generated build outputs
cannot add unintended package files.

The release validation campaign (seed `271828`, 10,000 generated groups) passed
**30,464 requests**, including **20,177 successful positions**, across all four
targets with identical result bits and errors. These are the same campaign counts
reported for Rust, not additional cases. See the
[campaign record and reproduction command](fuzzing.md#recorded-campaign).
The 10-micrometer bound is proved for Lean's model and native Float evaluator;
Python correspondence is supported by code review and differential testing.

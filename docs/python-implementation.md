# Python implementation

The Python port is the readable reference for a reviewer who works in Python.
Review it against [Lean Float](lean-implementation.md), then run its differential
tests. Native source correspondence is tested, not proved.

## Numerical code and API

Both numerical implementations are in
[ephemeris/](../python/ephemeris):

```text
ephemeris/
  __init__.py
  message.py
  float.py
  rational.py
```

| Module | Purpose |
| --- | --- |
| [message.py](../python/ephemeris/message.py) | Shared bounded Message, ReceiverError, tick arithmetic, and validation. |
| [float.py](../python/ephemeris/float.py) | Primary fixed-point-message receiver using bounded integers and binary64. |
| [rational.py](../python/ephemeris/rational.py) | Optional Fraction arithmetic over the same Message and query tick. |

The float kernel accepts the [decoded input contract](paper-and-spec.md#decoded-input-contract).
It uses no Fraction, Decimal, rational normalization, or runtime certificates.
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

## Optional rational reference

`evaluate_exact` accepts the very same `Message` object and integer query tick
as `evaluate_float`. Both call the validator in `message.py`, so carrier limits,
profile checks, inclusive endpoints, and error precedence are shared. Only the
working arithmetic and successful result type differ.

```python
from fractions import Fraction as Q
from ephemeris import Message, evaluate_exact, evaluate_float
from ephemeris.message import start_tick

message = Message(
    day_offset=0, second_of_day=43200, validity_code=2,
    coefficients=([96, 64, 32] + [0] * 8,
                  [-32, 0, 64] + [0] * 8,
                  [0, 32, 0] + [0] * 8),
)
when = start_tick(message) + 1800000000
assert evaluate_exact(message, when) == (Q(2), Q(-3), Q(0))
assert evaluate_float(message, when) == (2.0, -3.0, 0.0)
```

Rational decodes q/32-meter coefficients and computes Julian dates and all Table 3
operations with exact Fractions. It returns three Fractions without requiring a
Lean executable. Its correspondence with Lean Rational is differentially tested
through the [shared-input exact oracle](fuzzing.md#rational-oracle-on-p3-inputs).

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
python -m fuzz.drivers.rational --cases 1000 --seed 20260911
python -m fuzz.drivers.float --mode lean-python --cases 1000 --seed 20260911
```

For development, `make format-python`, `make format-check-python`, and
`make lint-python` use Ruff 0.16.7, pinned in the `dev` extra. These targets install
the extra into `.venv/` automatically. Formatting also sorts imports; linting
checks import order, unused or undefined names, and basic Python errors.
`make test-python` builds the Lean and Rust oracles and runs the Python regression suite.

The two fuzz commands compare Python with Lean without requiring Rust. For the
full regression suite, build the Rust oracle as well:

```sh
cargo build --manifest-path rust/Cargo.toml --release --locked
python -m unittest discover -s python/tests -v
```

Without installation, prefix Python module commands with `PYTHONPATH=python`.
Installed tooling can locate external executables through explicit client paths,
`PATH`, `EPHEMERIS_ORACLE`, and `EPHEMERIS_FLOAT_ORACLE`; a wheel does not bundle
Lean/Rust executables. Source-checkout clients discover the local build outputs.
Both installed drivers can write reports without Lean/Rust sources present;
missing sources are listed explicitly alongside selected executable hashes.

## Fuzzing organization and method

Everything used to drive or support fuzzing is under
[python/fuzz/](../python/fuzz):

```text
fuzz/
  drivers/{rational,float}.py      generation, comparison, reports, replay
  oracles/python_float.py          standalone P3 JSON-line server
  shared/                         protocols, clients, cases, exact targets, reports
  benchmarks/float_processes.py    process timing
```

The numerical package does not import these tools. Oracles do not import drivers.
Regression tests remain in [python/tests/](../python/tests). Bit-pattern encoding
and decoding live in `fuzz/shared/float_protocol.py`; they are not numerical APIs.
The independent exact recurrence used to measure sampled float error lives in fuzz support, outside
`float.py`. The [shared guide](fuzzing.md) defines comparison modes, coverage,
protocols, reproduction, replay, and the limits of differential evidence.

## Results

The current Python suite has **31 passing tests**, covering shared Message/error
identity, carrier and profile validation, hand-calculated positions, exact output
transport, independent Julian-date/tick comparisons, subprocess recovery, and
Lean model/native/Python/Rust comparisons, strict JSON array/number tokens,
installed-driver reports, and replay provenance. Numerical kernels remain separate from
fuzz infrastructure; the package contains `message.py`, `float.py`, and `rational.py`.
A fresh wheel was installed outside the checkout and checked against every oracle
backend. Build release wheels from a clean source tree so generated build outputs
cannot add unintended package files.

The release validation campaign (seed `271828`, 10,000 generated groups) passed **30,464
requests** across all four targets with identical result bits and errors. Its
20,177 successful position evaluations were also compared with the independent
exact recurrence. Maximum sampled coordinate error was **1.1069938432770927e-8 m**.
These are the same shared campaign counts reported for Rust, not additional cases.
The [campaign record and reproduction command](fuzzing.md#recorded-campaign)
distinguishes sampled accuracy from the proved uniform Lean bound of 10 micrometers
per coordinate. The theorem covers the Lean model and native Lean Float evaluator;
Python correspondence is supported by code review and differential testing.

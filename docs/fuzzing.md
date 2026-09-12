# Differential fuzzing

This guide defines the shared method, process protocols, and evidence limits.
The [Python](python-implementation.md) and [Rust](rust-implementation.md) guides
cover each port's code, setup, test commands, and results. Read the
[Lean proof status](lean-implementation.md#proof-status) separately: differential
agreement does not establish a universal correctness or roundoff theorem.

## Targets and comparison modes

The default Lean P3 oracle independently executes `Implementation.Correctness.Float.modelEvaluate`, which uses
explicit `Float.Model` operations. It does not run native Float and then convert
the resulting position. The same executable's `--native` mode is a separate
comparison target that runs `Implementation.Float.PositionReconstruction.evaluate`.

| Mode | Targets |
| --- | --- |
| `all` (default) | Lean software model, native Lean Float, Python float, Rust f64 |
| `triangle` | Lean software model, Python float, Rust f64 |
| `lean-python` | Lean software model and Python float |
| `lean-rust` | Lean software model and Rust f64 |
| `pair` | Python float and Rust f64; no Lean calls |

P3 compares every successful result bit and detailed error code. Keeping the
model comparison catches mistakes that both native ports might share. Pair mode
can add cheaper native comparison coverage, but it adds no Lean validation.

The Rational driver compares Python's exact reference with Lean Rational on the
same bounded Message/tick inputs. Its oracle accepts P3 `evaluate` requests and
returns exact fractions instead of output bits. The Float normalization and
accuracy proofs are independent of the optional Rational implementation.

## Coverage and exact targets

The fixed P3 boundary corpus includes each coefficient field's signed limits,
metadata limits, malformed shapes, query endpoints and outside-window values,
and full Int32 conversion boundaries. Each generated group adds a bounded
message query, a coefficient-conversion query, and a day-shifted message/query
with the same relative time. Tests also check wrong protocol types, carrier
overflow, response shape/finiteness, error precedence, and recovery after bad lines.

An independent rational recurrence in test support evaluates the exact polynomial
of each successful sampled fixed-point message and query tick. Comparing the
returned float with that target measures sampled error; it is not a radius
computed by the native kernel. `--tolerance` defaults to 1e-5 meters, matching the
proved Lean bound. This campaign tests that threshold on sampled Python/Rust
outputs; it does not prove a bound for those ports. The report's
`accuracy_is_formally_proved: false` describes the campaign's evidence, not the
separate Lean theorem. Reports identify replay runs with their path and zero
generated cases. Missing binaries, process failures, malformed responses,
mismatches, and threshold violations fail the run.

The Rational driver generates bounded fixed-point messages, all shared validation
errors, and exact algebraic properties: day shifts, axis permutations, negation,
constant translation by 1/32 meter, and Chebyshev parity. Transformations preserve
the selected field widths; there is no arbitrary-degree or zero-padding expansion.
It compares exact coordinates and rejection codes. Its reducer retains the original
mismatch kind; replay fixtures keep integer inputs and exact expected coordinates.

## Run and replay

From the repository root, after [Lean setup](lean-implementation.md#setup):

```sh
cargo build --manifest-path rust/Cargo.toml --release --locked
PYTHONPATH=python python3 -m fuzz.drivers.float --mode all --cases 1000 --seed 20260911 --output .lake/fuzz-layout-check
PYTHONPATH=python python3 -m fuzz.drivers.rational --cases 1000 --seed 20260911 --output .lake/exact-layout-check
```

Use a separate output directory per campaign. P3 writes `report.json` with source
hashes, mode, seed, counts, outcomes, sampled error, and elapsed time. On a mismatch
it writes the request and backend responses to `failure.json`; the Rational driver also retains
its minimized reproducer. Replay uses the same driver's artifact format:

```sh
PYTHONPATH=python python3 -m fuzz.drivers.float --mode all --replay DIR/failure.json
PYTHONPATH=python python3 -m fuzz.drivers.rational --replay DIR/failure.json
```

The Float driver accepts one seed per invocation; Rational permits repeated `--seed` options.
A report's request count is queries submitted to each selected target, not the
sum of backend executions. Boundary corpora and repeated seeds overlap, so totals
from separate campaigns must not be reported as unique coverage without deduplication.

## Tool organization

```text
python/
  ephemeris/{message,float,rational}.py  shared input and numerical code
  tests/                            regression tests
  fuzz/
    drivers/{rational,float}.py         campaigns and replay
    oracles/python_float.py          standalone Python P3 server
    shared/
      clients.py                    subprocess adapters
      protocol.py                   shared P3 requests, rational outputs, process errors
      float_protocol.py             P3 float responses and server adapter
      cases.py                      bounded rational cases, properties, replay
      float_cases.py                P3 generators and exact test-only target
      decimal.py                    exact output integer-string parsing
    benchmarks/float_processes.py    process timing
rust/src/fuzz.rs                     Rust P3 oracle adapter
Ephemeris/FuzzOracle/                Lean model/oracle construction
```

`fuzz.shared.clients` exposes `LeanOracle` for Rational and `FloatOracle` for Float.
P3 backend names are `lean`, `lean-native`, `python`, and `rust`. Oracles consume
requests; drivers generate and compare them. Neither the numerical Python package
nor an oracle imports the drivers. The Python server can be used independently:

```sh
PYTHONPATH=python python3 -m fuzz.oracles.python_float
```

Clients discover checkout binaries or use explicit paths, `PATH`,
`EPHEMERIS_ORACLE`, `EPHEMERIS_FLOAT_ORACLE`, and `EPHEMERIS_RUST_ORACLE`.
`FloatOracle("python")` runs the same installed/check-out package revision in the
current interpreter. Wheels include the `fuzz` package but no Lean/Rust binaries.
Drivers also work from an installed wheel outside the checkout. Reports hash available Python
sources, list unavailable Lean/Rust sources, and record the selected oracle
commands and executable hashes. In a checkout they additionally hash local
Lean/Rust sources. A local source hash alone does not show that an externally
selected oracle binary was built from that source.

## P3 bounded receiver protocol

These project requirements apply to both native ports and the comparison tooling:

| ID | Requirement |
| --- | --- |
| P3.1 | Accept FP1 decoded integer fields and the FP3 query tick, with explicit carrier checks at external boundaries. |
| P3.2 | Follow Lean Float's separately rounded operation order using bounded integers and binary64, without rational normalization or certificates. |
| P3.3 | Preserve FP2 validation errors and precedence; compare successful output bits, including signed zero. |
| P3.4 | Execute `Implementation.Correctness.Float.modelEvaluate` independently in the default Lean oracle; keep native Lean Float as a separate `--native` target. |
| P3.5 | Use version 3 JSON lines with bounded integer tokens and output bit strings; malformed data is `invalidProtocol`. Number tokens have no decimal point, exponent, or negative zero. |
| P3.6 | Compare all native targets against the model, retain replayable requests, and label pair-only coverage separately. Exact rational target arithmetic stays in test tooling. |

P3 is a local JSON-line test interface, not satellite serialization. Each line
produces one response; malformed lines do not end the stream. Integer fields must
fit the selected carriers before profile validation. Wrong JSON types, carrier
overflow, unknown operations, or the wrong version return `invalidProtocol`.
`message.coefficients` and each contained axis must be JSON arrays. Every number token uses
integer syntax without a decimal point, exponent, or negative zero: spell zero
as `0`, not `-0`. Thus `1.0` and `1e0` are rejected before parsing can erase their
spelling. These rules are shared by the Lean, Python, and Rust adapters; quoted
text is unaffected. They are test-protocol choices, not paper or numerical-API rules.

| Operation | Request fields beyond `version: 3` and `operation` | Success result |
| --- | --- | --- |
| `coefficient` | `coefficient`: signed 32-bit integer | One decimal uint64 bit string |
| `evaluate` | `message`: day_offset, second_of_day, validity_code, three coefficient arrays; `time`: unsigned 64-bit tick | Three decimal uint64 bit strings in XYZ order |

```json
{"version":3,"operation":"coefficient","coefficient":32}
```

The example returns `{"ok":true,"result":"4607182418800017408"}`, the bits of
positive one. Evaluation success uses an array for `result`. Numerical rejection
returns `{"ok":false,"error":"..."}` with the
[shared error code](lean-implementation.md#validation-and-arithmetic). Diagnostic
text is not part of the contract. Bit strings preserve signed zero; numerical
success requires finite values. Nonfinite values and NaN payload propagation are
not successful output cases. Parsing and process adapters remain tested tooling,
outside the current Lean proof boundary.

## Rational oracle on P3 inputs

`ephemeris_oracle` accepts the same P3 `evaluate` request as the Float oracles.
Both Lean adapters use the bounded parser in
[OracleProtocol](../Ephemeris/FuzzOracle/OracleProtocol.lean). For example:

```json
{"version":3,"operation":"evaluate","message":{"day_offset":0,"second_of_day":43200,"validity_code":2,"coefficients":[[224,0,0,0,0,0,0,0,0,0,0],[-96,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0]]},"time":212630486400000000}
```

Its exact response is
`{"ok":true,"position":[["7","1"],["-3","1"],["0","1"]]}`.
Only output coordinates use decimal numerator/denominator string pairs, with
positive denominators. Inputs are bounded integers throughout. Numerical errors
and their precedence are identical to Message validation; malformed requests,
unsupported operations, and carrier overflow return `invalidProtocol`.
The Rational oracle supports `evaluate` only, not Float's coefficient-bit query.

The stream continues after a bad request. `LeanOracle.evaluate_many` returns
positions or receiver errors in order; `evaluate` raises numerical rejection.
Process failures and malformed responses raise `OracleError`. Output integers
are parsed as strict ASCII decimals without changing interpreter-wide limits.
Empty batches return an empty list.

## Recorded campaign

Release validation on 2026-09-11 passed the following campaigns:

| Campaign | Result |
| --- | --- |
| Float, all four targets, seed `271828`, 10,000 generated groups | **30,464 requests** with identical bits/errors; 20,177 successful positions; maximum sampled coordinate error **1.1069938432770927e-8 m** |
| Rational, seeds `20260911` and `314159265`, 3,000 base cases each | **7,012 exact differential queries** (3,509 + 3,503), including shared validation errors and algebraic properties |

The Float run took 45.82 seconds and the Rational runs 10.76 seconds, including
process/JSON and test-oracle work. These are campaign timings, not kernel or
onboard execution measurements. Reproduce the corpora with:

```sh
PYTHONPATH=python python3 -m fuzz.drivers.float --mode all --cases 10000 --seed 271828 --output .lake/validation/float
PYTHONPATH=python python3 -m fuzz.drivers.rational --cases 3000 --seed 20260911 --seed 314159265 --output .lake/validation/rational
```

Reports in those directories record source and executable hashes. The 31 Python
regressions also check malformed array/number tokens, stream recovery, replay
counts, finite CLI limits, and installed drivers outside the checkout. A fresh
wheel ran both drivers outside the checkout using external Lean/Rust binaries;
its reports are under `.lake/validation/package/`. Python and Rust guide examples
were executed successfully. Rust's five regression tests, the Lean build's
836 executable checks, and its 33-entry theorem axiom audit passed.

The Float counts in the Python and Rust guides describe this same campaign.
The sampled error supports the native ports' differential validation, separate
from Lean's universal accuracy theorem.

## Process timing


```sh
PYTHONPATH=python python3 -m fuzz.benchmarks.float_processes --cases 1000
```

This times Lean-model, Python, and Rust process paths including JSON/startup.
It does not measure onboard worst-case execution time. Keep performance
measurements on a fixed corpus separate from coverage counts and accuracy claims.

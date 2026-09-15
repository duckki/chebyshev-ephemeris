# Differential fuzzing

This guide defines the comparison method, process protocol, and evidence limits.
The [Python](python-implementation.md) and [Rust](rust-implementation.md) guides
cover each port's code and API. Read the
[Lean proof status](lean-implementation.md#proof-status) separately: differential
agreement tests correspondence on sampled inputs; the universal accuracy bound
is proved in Lean.

## Targets and comparison modes

The default Lean P3 oracle independently executes
`Implementation.Correctness.Float.modelEvaluate` using concrete `Float.Model`
operations. The same executable's `--native` mode runs
`Implementation.PositionReconstruction.evaluate` using native `Float`.
The model and native reconstruction loops have separate concrete definitions;
both call the decoded Message's validation policy. The model does not run the
native implementation and convert its result.

| Mode | Targets |
| --- | --- |
| `all` (default) | Lean software model, native Lean Float, Python float, Rust f64 |
| `triangle` | Lean software model, Python float, Rust f64 |
| `lean-python` | Lean software model and Python float |
| `lean-rust` | Lean software model and Rust f64 |
| `pair` | Python float and Rust f64; no Lean calls |

P3 compares every successful output bit and rejection code. Keeping the model
comparison catches mistakes that both native ports might share. Pair mode can add
cheaper native comparison coverage, but it adds no Lean validation.

## Coverage and accuracy

The fixed boundary corpus includes each coefficient field's signed limits,
metadata limits, malformed shapes, query endpoints and outside-window values,
and full Int32 conversion boundaries. Each generated group adds a bounded
message query, a coefficient-conversion query, and a day-shifted message/query
with the same relative time. Tests also check wrong protocol types, carrier
overflow, response shape/finiteness, error precedence, and recovery after bad lines.

The Lean software model is the numerical oracle. Lean proves its supported-domain
success and 10-micrometer per-coordinate bound against the real specification,
then transfers that bound to native Lean through a correspondence proof. The
Python/Rust campaigns test matching bits and errors on sampled inputs; they do
not prove source equivalence for those ports.
Missing binaries, process failures, malformed responses, and disagreements fail
the run. Reports identify replay runs by their path and zero generated groups.

## Run and replay

From the repository root, after [Lean setup](lean-implementation.md#setup):

```sh
make fuzz-smoke
make fuzz-full
```

For a custom corpus:

```sh
PYTHONPATH=python .venv/bin/python -m fuzz.drivers.float --mode all --cases 1000 --seed 20260911 --output .lake/fuzz-custom
```

Use a separate output directory per campaign. The driver writes `report.json`
with source/executable hashes, mode, seed, counts, outcomes, and elapsed time.
On a mismatch it writes the request and backend responses to `failure.json`.
Replay the request with:

```sh
PYTHONPATH=python .venv/bin/python -m fuzz.drivers.float --mode all --replay DIR/failure.json
```

The driver accepts one seed per invocation. A report's request count is queries
submitted to each selected target, not the sum of backend executions. Boundary
corpora and repeated seeds overlap, so totals from separate campaigns must not be
reported as unique coverage without deduplication.

## Tool organization

```text
python/
  ephemeris/
    message.py                      bounded input and validation
    position_reconstruction.py      numerical implementation
  tests/                            regression tests
  fuzz/
    drivers/float.py                campaigns and replay
    oracles/python_float.py         standalone Python P3 server
    shared/
      clients.py                    subprocess adapters
      protocol.py                   P3 requests and process errors
      float_protocol.py             P3 responses and server adapter
      float_cases.py                boundary cases and seeded inputs
      reports.py                    source/executable provenance
    benchmarks/float_processes.py   process timing
rust/src/fuzz.rs                     Rust P3 oracle adapter
Ephemeris/FuzzOracle/                Lean model/native oracle construction
```

`fuzz.shared.clients.FloatOracle` accepts `lean`, `lean-native`, `python`, or `rust`.
Oracles consume requests; drivers generate and compare them. Neither the numerical
Python package nor an oracle imports the driver. The Python server can also run
independently:

```sh
PYTHONPATH=python python3 -m fuzz.oracles.python_float
```

Clients discover checkout binaries or use explicit paths, `PATH`,
`EPHEMERIS_FLOAT_ORACLE`, and `EPHEMERIS_RUST_ORACLE`. `FloatOracle("python")` runs
the same installed/check-out package revision in the current interpreter. Wheels
include the `fuzz` package but no Lean/Rust binaries. The driver also works from
an installed wheel outside the checkout. Reports hash available Python sources,
list unavailable Lean/Rust sources, and record the selected oracle commands and
executable hashes. In a checkout they additionally hash local Lean/Rust sources.
A local source hash alone does not show that an externally selected oracle binary
was built from that source.

## P3 bounded receiver protocol

These project requirements apply to both native ports and the comparison tooling:

| ID | Requirement |
| --- | --- |
| P3.1 | Accept FP1 decoded integer fields and the FP3 query tick, with explicit carrier checks at external boundaries. |
| P3.2 | Follow Lean Float's separately rounded operation order using bounded integers and binary64. |
| P3.3 | Preserve FP2 validation errors and precedence; compare successful output bits, including signed zero. |
| P3.4 | Execute `Implementation.Correctness.Float.modelEvaluate` independently in the default Lean oracle; keep native Lean Float as a separate `--native` target. |
| P3.5 | Use version 3 JSON lines with bounded integer tokens and output bit strings; malformed data is `invalidProtocol`. Number tokens have no decimal point, exponent, or negative zero. |
| P3.6 | Compare all native targets against the model, retain replayable requests, and label pair-only coverage separately. |

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

## Recorded campaign

The release campaign (seed `271828`, 10,000 generated groups) passed **30,464
requests**, including **20,177 successful positions**, across the Lean model,
native Lean, Python, and Rust. Every output bit and rejection error agreed.
Reproduce it, together with all local checks, using:

```sh
make release-check
```

Reports under `.lake/validation/float/` record source and executable hashes;
`environment.txt` beside that directory records the checkout and toolchain versions.
Provenance covers the concrete native implementation, software model, oracle
adapters, and pinned dependencies. See the
[local validation commands](development.md#differential-fuzzing).

The **18 Python tests**, **5 Rust tests**, **764 Lean executable checks**, and
**27-entry theorem axiom audit** also passed. A clean Python wheel was installed
outside the checkout and its driver exercised against all four targets. The
Python/Rust guides report this same campaign, not additional cases.

## Process timing

```sh
PYTHONPATH=python python3 -m fuzz.benchmarks.float_processes --cases 1000
```

This times the Lean-model, Python, and Rust process paths, including JSON and
startup. It does not measure onboard worst-case execution time.

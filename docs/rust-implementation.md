# Rust implementation

The Rust port demonstrates the intended shipped numerical implementation. Review
its operation order against [Lean Float](lean-implementation.md) and compare its
outputs with Lean. Native source correspondence is tested, not proved.

## Numerical code and API

[rust/src/lib.rs](../rust/src/lib.rs) contains the receiver. Metadata uses `u16`,
`u32`, and `u8`; coefficients use `i32`; query ticks use `u64`; output is
`Result<[f64; 3], ReceiverError>`. The input is the same
[decoded fixed-point message](paper-and-spec.md#decoded-input-contract) used by Lean
and Python. There are no big-integer or rational-arithmetic dependencies.

The public numerical functions are `evaluate`, `validate_query`, `coefficient`,
`start_tick`, and `duration_ticks`. Input coefficient vectors admit malformed lengths
so the evaluator can return a shape error. Validation precedes indexing; working
storage is `[f64; 11]` for the basis and `[f64; 3]` for the output.

```rust
use ephemeris_reference::{Message, evaluate, start_tick};

fn main() {
    let mut message = Message {
        day_offset: 0,
        second_of_day: 43200,
        validity_code: 2,
        coefficients: std::array::from_fn(|_| vec![0; 11]),
    };
    message.coefficients[0][0] = 3200;
    message.coefficients[0][1] = 640;
    let start = start_tick(&message);
    assert_eq!(evaluate(&message, start), Ok([80.0, 0.0, 0.0]));
    assert_eq!(evaluate(&message, start + 1800000000), Ok([100.0, 0.0, 0.0]));
    assert_eq!(evaluate(&message, start + 3600000000), Ok([120.0, 0.0, 0.0]));
}
```

The [error vocabulary and precedence](lean-implementation.md#validation-and-arithmetic)
match Lean and Python. External input adapters must reject integers that cannot
fit their carriers before casting. The fuzz adapter explicitly performs those
checks; Rust's typed API already constrains carrier widths.

## Arithmetic review

Subtract checked integer timestamps before float conversion. Convert bounded
elapsed/duration values, divide, multiply by two, and subtract one. Decode q/32,
build the degree-10 basis, and accumulate coordinates in increasing index order.
The signed conversion mirrors Lean's modeled unsigned-magnitude adaptation,
including the minimum i32 value. Keep each floating operation separate: no
`mul_add`, fast-math, reassociation, or alternative summation without a reviewed
model change and numerical argument.

Finiteness checks remain executable. There are no runtime radii or budgets;
Lean proves an offline uniform bound of 10 micrometers per coordinate and
success for every supported query. Rust correspondence is supported by code review
and differential testing. The proof and test scope does not establish deployment-target
timing, compiler correctness,
frame/time-scale integration, physical-orbit accuracy, or a satellite bitstream.

## Build, test, and fuzz

Use the locked dependencies and the pinned Lean toolchain. Rust 1.85+ is required
by the crate. Set up Python as described in the [Python guide](python-implementation.md#install-and-test).
From the repository root:

```sh
lake build
cargo build --manifest-path rust/Cargo.toml --release --locked
cargo test --manifest-path rust/Cargo.toml --locked
PYTHONPATH=python python3 -m fuzz.drivers.float --mode lean-rust --cases 1000 --seed 20260911
PYTHONPATH=python python3 -m fuzz.drivers.float --mode all --cases 10000 --seed 271828
```

Install formatter and linter components with `rustup component add rustfmt clippy`.
Use `make format-rust` to apply rustfmt, `make format-check-rust` to check formatting,
and `make lint-rust` to run Clippy over all targets and features with warnings
treated as errors. `make test-rust` runs the locked Rust test suite.

The numerical kernel is separate from the
[fuzz oracle adapter](../rust/src/fuzz.rs), exposed as `ephemeris_reference::fuzz`.
[src/main.rs](../rust/src/main.rs) runs that adapter as the
`ephemeris_float_reference` JSON-line executable. P3 parsing and response encoding
are test infrastructure, not a satellite wire codec. The adapter can be driven by
Python or another client without embedding the fuzz driver into the Rust library.
Set `EPHEMERIS_RUST_ORACLE` to use a separately installed binary.

The [shared fuzzing guide](fuzzing.md) covers the comparison modes, boundary cases,
independent exact target, process protocol, and replay. `pair` runs additional
Python/Rust comparisons without Lean; do not count those as Lean validation.

## Results

The Rust regression tests are together in [tests/reference.rs](../rust/tests/reference.rs),
keeping test fixtures out of the numerical kernel. The suite has **five passing tests**: line/endpoints, validation
precedence, integer-conversion extrema, every coefficient field boundary, and
malformed protocol/carrier rejection.

Rust participated in the same **30,464-request** P3 campaign reported for Python
(seed `271828`, 10,000 groups). All four targets agreed on bits and errors. The
20,177 successful sampled positions had maximum coordinate error
**1.1069938432770927e-8 m** against the exact recurrence. This is a sampled maximum,
not the general Float accuracy theorem. The release validation campaign covers all four targets. Its timing includes process/JSON
overhead and exact test-oracle work; it is not a kernel benchmark or flight timing
guarantee. See the [campaign record](fuzzing.md#recorded-campaign).

# Ephemeris

A reviewable path from a scientific paper to proved Lean code and tested Python/Rust
implementations. Review the specification, correctness statements, and code. Lean
checks the proofs; differential tests reduce the correctness reasoning reviewers
need to repeat for the native ports.

The receiver evaluates a trajectory at a query time: eleven Chebyshev coefficients
per axis, transmitted as signed fixed-point integers at **1/32 meter**. Real and
float evaluation interpret the same decoded message and tick. Fitting, upstream
quantization, and satellite serialization are outside this numerical component.

**Current status:** every supported Lean Float query is proved to succeed with
finite coordinates within **10 micrometers per axis** of real evaluation of the
same message. Message/real correctness, exact decoding, and full native/model
correspondence are also proved. Python and Rust use bounded integers and binary64;
the recorded four-target campaign passed 30,464 requests with matching bits/errors.

## 1. Review the paper and Lean specification

Compare [Definitions/](Ephemeris/Definitions) with
[Bury et al. (2025), §2.3 and Table 3](https://doi.org/10.1186/s40645-024-00676-1).
The [paper and specification guide](docs/paper-and-spec.md) maps declarations to
sources, records the paper's discrepancies, and identifies the project-selected
input profile and validation policy in Definitions/Message.

## 2. Review the Lean implementation and correctness statements

Compare the [ideal real interpretation](Ephemeris/Definitions/PositionReconstruction.lean)
with the [Float implementation](Ephemeris/Implementation/Float/PositionReconstruction.lean).
Review [Correctness/](Ephemeris/Implementation/Correctness), then install Lean's
`elan` toolchain manager and run from the repository root:

```sh
make
```

This uses the pinned Lean and Mathlib v4.33.1 releases, downloads the Mathlib build
cache, and runs `lake build`. Cache downloads stay under `.lake/mathlib-cache/`.
Use `make cache` to fetch the cache alone; subsequent local checks can use
`lake build` directly.

The [Lean guide](docs/lean-implementation.md) provides setup, implementation maps,
and the proof checklist. The build checks 33 theorem entry
points for unexpected axioms and runs 836 executable checks. A proposition
definition or passing test is not a proof of that proposition.

For development, install Python 3.11+ and Rust with `rustfmt` and `clippy`
(`rustup component add rustfmt clippy`). The Makefile installs the pinned Ruff
version into `.venv/` when needed; LeanFmt is pinned as a Lake dependency.

```sh
make format        # Format project Lean, Python, and Rust sources
make format-check  # Check formatting without rewriting sources
make lint          # Lean warnings, Ruff, and Clippy with warnings as errors
make check         # Formatting, linting, Lean build/audit, and Python/Rust tests
```

Each formatting and lint target also has a `-lean`, `-python`, or `-rust` variant.
Lean formatting builds imported modules first so LeanFmt can load project syntax.

## 3. Review Python and run its differential tests

The [Python guide](docs/python-implementation.md) explains the bounded float port,
optional rational reference, APIs, installation, and results.

```sh
PYTHONPATH=python python3 -m fuzz.drivers.float --mode lean-python --cases 1000 --seed 20260911
```

## 4. Review Rust and compare all implementations

The [Rust guide](docs/rust-implementation.md) covers the bounded kernel, fuzz adapter,
and results. After the Lean build:

```sh
cargo build --manifest-path rust/Cargo.toml --release --locked
cargo test --manifest-path rust/Cargo.toml --locked
PYTHONPATH=python python3 -m unittest discover -s python/tests -v
PYTHONPATH=python python3 -m fuzz.drivers.float --mode all --cases 1000 --seed 20260911
```

The [shared fuzzing guide](docs/fuzzing.md) explains model/native comparisons,
coverage, protocols, replay, and evidence limits. Python/Rust source correspondence
is tested, not formally proved. Supporting research and the conventional
development estimate are in [docs/references/](docs/references/README.md).

# Ephemeris

**Satellite position reconstruction, proved in Lean and ported to Python and Rust.**

Ephemeris implements the Chebyshev reconstruction algorithm from
[Bury et al. (2025)](https://doi.org/10.1186/s40645-024-00676-1) in Lean, proves its
correctness and floating-point accuracy, then checks the Python and Rust ports
against Lean's numerical model through differential fuzzing.

**The main guarantee:** every supported Lean binary64 query succeeds with finite
XYZ coordinates within **10 micrometers per axis** of exact real evaluation of
the same decoded message.

## What's implemented

- **Lean specification and proofs:** real Chebyshev semantics, input validation,
  exact coefficient decoding, bounded tick arithmetic, and agreement between
  native Float execution and its software model.
- **Executable receivers:** binary64 implementations in Lean, Python, and Rust,
  sharing a bounded integer input contract. Lean and Python also provide exact
  rational reference evaluators.
- **Differential validation:** a recorded campaign of **30,464 requests** matched
  output bits and rejection errors across the Lean model, native Lean, Python,
  and Rust. The ports are tested against Lean; their source equivalence is not
  formally proved.

Each query reconstructs a position from eleven fixed-point coefficients per axis
and a query time. The accuracy bound covers numerical evaluation of that message;
trajectory fitting, upstream quantization, and satellite serialization are
outside this component's scope.

## Build

With Lean's `elan` toolchain manager installed, run from the repository root:

```sh
make
```

This uses Lean and Mathlib **4.33.1**, fetches the Mathlib build cache, and builds
the Lean code, including **836 executable checks** and a **33-theorem axiom audit**.
See the [development guide](docs/development.md) for full setup and checks.

## Explore

| Guide | What you'll find |
| --- | --- |
| [Paper and specification](docs/paper-and-spec.md) | Source equations, interpretations, and the decoded-input contract |
| [Lean](docs/lean-implementation.md) | Implementation structure, theorem statements, and proof status |
| [Python](docs/python-implementation.md) | Binary64 and rational APIs, usage, and tests |
| [Rust](docs/rust-implementation.md) | Bounded binary64 API and validation |
| [Differential fuzzing](docs/fuzzing.md) | Comparison targets, recorded results, and replay |
| [Development](docs/development.md) | Setup, builds, formatting, linting, and test commands |

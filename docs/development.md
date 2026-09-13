# Development

Build, format, and reproduce its validation from the repository root. For the algorithm
and its guarantees, start with the [project introduction](../README.md),
[specification](paper-and-spec.md), and [Lean proof status](lean-implementation.md#proof-status).

## Setup

The Lean build requires `make` and Lean's `elan` toolchain manager. The project
pins Lean and Mathlib to **4.33.1** in [lean-toolchain](../lean-toolchain) and
[lakefile.toml](../lakefile.toml).

For Python/Rust development and the complete test suite, also install:

- **Python 3.11+**, with `venv` and `pip` support.
- **Rust 1.85+**, with the formatter and linter components:

```sh
rustup component add rustfmt clippy
```

The Python targets create `.venv/` and install the package's `dev` extra when
needed. It pins **Ruff 0.16.7** in [pyproject.toml](../python/pyproject.toml).
Use `PYTHON=python3.11 make check`, for example, to choose the interpreter when
creating the environment. Activate `.venv/` for direct Python commands:

```sh
. .venv/bin/activate
```

LeanFmt **v0.4.1** is a pinned [Lake dependency](../lakefile.toml), resolved through
[lake-manifest.json](../lake-manifest.json). Rustfmt and Clippy use the active Rust
toolchain.

## Build and cache

```sh
make             # Fetch the Mathlib cache and build the default Lean targets
make cache       # Fetch the Mathlib cache alone
lake build       # Subsequent local Lean builds
make build-rust  # Build the release Rust oracle with locked dependencies
```

Mathlib downloads stay in the ignored `.lake/mathlib-cache/` directory. Set
`MATHLIB_CACHE_DIR` to use another location. `make` preserves the dependency
revisions in the Lake lockfile.

The Lean default targets build both oracle executables, run **836 executable
checks**, and audit **33 theorem entry points** for unexpected axioms. The
[Lean guide](lean-implementation.md#proof-status) describes the proofs and their
allowed dependencies.

## Formatting and linting

```sh
make format        # Apply LeanFmt, Ruff formatting/import sorting, and rustfmt
make format-check  # Check formatting without rewriting source files
make lint          # Run Lean, Python, and Rust lint checks
```

Each target has a language-specific variant:

| Language | Apply formatting | Check formatting | Lint |
| --- | --- | --- | --- |
| Lean | `make format-lean` | `make format-check-lean` | `make lint-lean` |
| Python | `make format-python` | `make format-check-python` | `make lint-python` |
| Rust | `make format-rust` | `make format-check-rust` | `make lint-rust` |

- **Lean:** [duckki/leanfmt v0.4.1](https://github.com/duckki/leanfmt/tree/v0.4.1)
  formats `Ephemeris.lean` and every Lean file under `Ephemeris/`. Both formatting
  targets build imported modules first so LeanFmt can load project syntax.
  Linting uses the Lake build with `warningAsError = true`.
- **Python:** Ruff formats source, fuzz tooling, and tests under `python/`, plus
  development helpers under `scripts/`.
  The formatting target also sorts imports. Linting checks import order, unused
  or undefined names, and basic Python errors. Ruff is installed in `.venv/`;
  no environment activation is required for Makefile targets.
- **Rust:** rustfmt covers the crate's sources and tests. Clippy runs with
  `--all-targets --all-features --locked -- -D warnings`.

Formatting applies source edits. Review the diff, then run the complete checks.

## Tests and complete checks

```sh
make check        # Formatting, linting, Lean build/audit, Python/Rust tests, and docs
make check-docs   # Check local documentation links and heading anchors offline
make test         # Lean checks plus Python and Rust regression suites
make test-python  # Build Lean/Rust oracles and run the 31 Python tests
make test-rust    # Run the 5 Rust regression tests with locked dependencies
```

`make check` checks source formatting without rewriting it. It may download
missing dependencies and caches, install Python development tools, and build
executables. The Python tests invoke the Lean and release Rust oracle programs;
`make test-python` builds those dependencies automatically.

The documentation check covers inline Markdown links and heading anchors in the
README and guides. It skips external websites and fenced code examples.

## Differential fuzzing

The Makefile builds the required oracles and runs fixed, reproducible campaigns:

```sh
make fuzz-smoke     # Small four-target Float and exact Rational campaigns
make fuzz-full      # Full recorded Float and Rational campaigns
make release-check  # Complete checks followed by the full campaigns
```

The Float targets are the independent Lean Float model, native Lean Float, Python,
and Rust. Reports and any failure reproducer go under `.lake/validation/` by
default; set `VALIDATION_DIR` to choose another directory. `environment.txt`
records the checkout commit, working-tree changes, OS, and Python/Rust/Lean versions.
The [fuzzing guide](fuzzing.md) covers comparison modes, exact rational
campaigns, replay, and the recorded validation results.

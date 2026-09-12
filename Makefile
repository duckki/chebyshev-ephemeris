MATHLIB_CACHE_DIR ?= $(CURDIR)/.lake/mathlib-cache
PYTHON ?= python3

.PHONY: all build build-rust cache format format-lean format-python format-rust \
	format-check format-check-lean format-check-python format-check-rust \
	lint lint-lean lint-python lint-rust test test-python test-rust check

all: build

build: cache
	lake build

build-rust:
	cargo build --manifest-path rust/Cargo.toml --release --locked

cache:
	MATHLIB_NO_CACHE_ON_UPDATE=1 MATHLIB_CACHE_DIR="$(MATHLIB_CACHE_DIR)" lake exe cache get

# LeanFmt loads imported syntax, so project modules must be built first.
format: format-lean format-python format-rust

format-lean: build
	lake exe fmt -r Ephemeris.lean Ephemeris

format-python: .venv/.dev-tools
	.venv/bin/ruff check --select I --fix python
	.venv/bin/ruff format python

format-rust:
	cargo fmt --manifest-path rust/Cargo.toml --all

format-check: format-check-lean format-check-python format-check-rust

format-check-lean: build
	lake exe fmt --check -r Ephemeris.lean Ephemeris

format-check-python: .venv/.dev-tools
	.venv/bin/ruff format --check python

format-check-rust:
	cargo fmt --manifest-path rust/Cargo.toml --all -- --check

lint: lint-lean lint-python lint-rust

# The Lake configuration treats Lean warnings (including linter warnings) as errors.
lint-lean: build

lint-python: .venv/.dev-tools
	.venv/bin/ruff check python

lint-rust:
	cargo clippy --manifest-path rust/Cargo.toml --all-targets --all-features --locked -- -D warnings

test: build test-python test-rust

# Python tooling tests invoke both Lean oracles and the release Rust oracle.
test-python: build build-rust .venv/.dev-tools
	PYTHONPATH=python .venv/bin/python -m unittest discover -s python/tests -v

test-rust:
	cargo test --manifest-path rust/Cargo.toml --locked

check: format-check lint test

.venv/.dev-tools: python/pyproject.toml
	$(PYTHON) -m venv .venv
	.venv/bin/python -m pip install -e "./python[dev]"
	touch $@

MATHLIB_CACHE_DIR ?= $(CURDIR)/.lake/mathlib-cache
PYTHON ?= python3
VALIDATION_DIR ?= $(CURDIR)/.lake/validation

.PHONY: all build build-rust cache format format-lean format-python format-rust \
	format-check format-check-lean format-check-python format-check-rust \
	lint lint-lean lint-python lint-rust test test-python test-rust check check-docs \
	fuzz-smoke fuzz-full validation-info release-check

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
	.venv/bin/ruff check --select I --fix python scripts
	.venv/bin/ruff format python scripts

format-rust:
	cargo fmt --manifest-path rust/Cargo.toml --all

format-check: format-check-lean format-check-python format-check-rust

format-check-lean: build
	lake exe fmt --check -r Ephemeris.lean Ephemeris

format-check-python: .venv/.dev-tools
	.venv/bin/ruff format --check python scripts

format-check-rust:
	cargo fmt --manifest-path rust/Cargo.toml --all -- --check

lint: lint-lean lint-python lint-rust

# The Lake configuration treats Lean warnings (including linter warnings) as errors.
lint-lean: build

lint-python: .venv/.dev-tools
	.venv/bin/ruff check python scripts

lint-rust:
	cargo clippy --manifest-path rust/Cargo.toml --all-targets --all-features --locked -- -D warnings

test: build test-python test-rust

# Python tooling tests invoke both Lean oracles and the release Rust oracle.
test-python: build build-rust .venv/.dev-tools
	PYTHONPATH=python .venv/bin/python -m unittest discover -s python/tests -v

test-rust:
	cargo test --manifest-path rust/Cargo.toml --locked

check-docs:
	$(PYTHON) scripts/check_docs.py

check: format-check lint test check-docs

validation-info: build .venv/.dev-tools
	mkdir -p "$(VALIDATION_DIR)"
	set -e; { git rev-parse HEAD; git status --short; uname -a; .venv/bin/python --version; rustc --version; lake env lean --version; } > "$(VALIDATION_DIR)/environment.txt"

fuzz-smoke: build build-rust .venv/.dev-tools validation-info
	PYTHONPATH=python .venv/bin/python -m fuzz.drivers.float --mode all --cases 100 --seed 20260911 --output "$(VALIDATION_DIR)/float"
	PYTHONPATH=python .venv/bin/python -m fuzz.drivers.rational --cases 100 --seed 20260911 --output "$(VALIDATION_DIR)/rational"

fuzz-full: build build-rust .venv/.dev-tools validation-info
	PYTHONPATH=python .venv/bin/python -m fuzz.drivers.float --mode all --cases 10000 --seed 271828 --output "$(VALIDATION_DIR)/float"
	PYTHONPATH=python .venv/bin/python -m fuzz.drivers.rational --cases 3000 --seed 20260911 --seed 314159265 --output "$(VALIDATION_DIR)/rational"

release-check: check fuzz-full

.venv/.dev-tools: python/pyproject.toml
	$(PYTHON) -m venv .venv
	.venv/bin/python -m pip install -e "./python[dev]"
	touch $@

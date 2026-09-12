"""Batch subprocess clients for the Lean exact/float and Python/Rust float oracles."""

import os
import shutil
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Iterable

import ephemeris
from ephemeris.message import Message, ReceiverError

from .float_protocol import response as float_response
from .protocol import (
    OracleError,
    _encode_request,
    _request,
    exact_response,
)


class LeanOracle:
    """Run bounded Message/tick queries in batches; return exact rational coordinates.

    Install the executable with `lake build ephemeris_oracle`. An installed Python
    wheel can use an explicit executable path, EPHEMERIS_ORACLE, or PATH.
    """

    def __init__(self, executable: str | Path | None = None, *, timeout: float = 30.0):
        selected = (
            executable
            or os.environ.get("EPHEMERIS_ORACLE")
            or shutil.which("ephemeris_oracle")
        )
        if selected is None:
            selected = (
                Path(ephemeris.__file__).resolve().parents[2]
                / ".lake/build/bin/ephemeris_oracle"
            )
        self.executable = Path(selected).expanduser().resolve()
        self.timeout = timeout
        if not self.executable.is_file():
            raise OracleError(
                "Lean oracle not found; build it and set EPHEMERIS_ORACLE"
            )

    def evaluate_many(
        self, queries: Iterable[tuple[Message, int]]
    ) -> list[tuple[Fraction, ...] | ReceiverError]:
        requests = [_request(m, t) for m, t in queries]
        if not requests:
            return []
        data = "".join(_encode_request(r) + "\n" for r in requests)
        try:
            completed = subprocess.run(
                [str(self.executable)],
                input=data,
                capture_output=True,
                text=True,
                encoding="utf-8",
                timeout=self.timeout,
                check=True,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            raise OracleError(f"Lean oracle execution failed: {exc}") from exc
        lines = completed.stdout.splitlines()
        if len(lines) != len(requests):
            raise OracleError("Lean oracle returned the wrong response count")
        return [exact_response(line) for line in lines]

    def evaluate(self, message: Message, time: int) -> tuple[Fraction, ...]:
        result = self.evaluate_many([(message, time)])[0]
        if isinstance(result, ReceiverError):
            raise result
        return result


class FloatOracle:
    """Compiled/model process adapter; source-checkout paths or explicit overrides.

    backend='python' runs this installed package in the current interpreter.
    EPHEMERIS_FLOAT_ORACLE and EPHEMERIS_RUST_ORACLE configure the other binaries.
    """

    def __init__(self, backend="lean", executable=None, *, timeout=60.0):
        root = Path(ephemeris.__file__).resolve().parents[2]
        self.env = None
        if backend == "python":
            self.command = [sys.executable, "-m", "fuzz.oracles.python_float"]
            # A checkout script adds python/ to its own sys.path, not its child's.
            # Explicitly run the same package revision in the child interpreter.
            self.env = os.environ.copy()
            package_root = str(Path(ephemeris.__file__).resolve().parents[1])
            self.env["PYTHONPATH"] = (
                package_root + os.pathsep + self.env.get("PYTHONPATH", "")
            )
        else:
            names = {
                "lean": (
                    "EPHEMERIS_FLOAT_ORACLE",
                    "ephemeris_float_oracle",
                    root / ".lake/build/bin/ephemeris_float_oracle",
                ),
                "lean-native": (
                    "EPHEMERIS_FLOAT_ORACLE",
                    "ephemeris_float_oracle",
                    root / ".lake/build/bin/ephemeris_float_oracle",
                ),
                "rust": (
                    "EPHEMERIS_RUST_ORACLE",
                    "ephemeris_float_reference",
                    root / "rust/target/release/ephemeris_float_reference",
                ),
            }
            if backend not in names:
                raise ValueError("backend must be lean, lean-native, rust, or python")
            variable, name, fallback = names[backend]
            selected = (
                Path(
                    executable
                    or os.environ.get(variable)
                    or shutil.which(name)
                    or fallback
                )
                .expanduser()
                .resolve()
            )
            if not selected.is_file():
                raise OracleError(
                    f"{backend} float oracle not found; build it or set {variable}"
                )
            self.command = [str(selected)]
            if backend == "lean-native":
                self.command.append("--native")
        self.timeout = timeout
        self.backend = backend

    def request_many(self, requests):
        requests = list(requests)
        if not requests:
            return []
        data = "".join(_encode_request(r) + "\n" for r in requests)
        try:
            completed = subprocess.run(
                self.command,
                input=data,
                text=True,
                encoding="utf-8",
                capture_output=True,
                timeout=self.timeout,
                check=True,
                env=self.env,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            raise OracleError(f"{self.backend} float oracle failed: {exc}") from exc
        lines = completed.stdout.splitlines()
        if len(lines) != len(requests):
            raise OracleError("float oracle returned wrong response count")
        return [
            float_response(line, request.get("operation", "evaluate"))
            for line, request in zip(lines, requests, strict=True)
        ]

    def evaluate_many(self, queries):
        return self.request_many(_request(m, t) for m, t in queries)

    def evaluate(self, message, when):
        return self.evaluate_many([(message, when)])[0]

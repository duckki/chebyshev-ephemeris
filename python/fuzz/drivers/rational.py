"""Seeded exact differential/property fuzzing of the shared bounded Message domain.

Run from the checkout: python -m fuzz.drivers.rational --cases 3000 --seed 20260911
Failures retain Message/tick inputs and exact hexadecimal expected coordinates.
Replay with --replay PATH. No third-party dependency.
"""

import argparse
import json
import random
import time
from collections import Counter
from dataclasses import replace
from pathlib import Path

from ephemeris.rational import ReceiverError, evaluate_exact
from fuzz.shared.cases import (
    decode_case,
    encode_case,
    generate,
    outcome,
    transformations,
)
from fuzz.shared.clients import LeanOracle
from fuzz.shared.reports import provenance


class FuzzFailure(Exception):
    def __init__(self, case, kind, detail):
        self.case, self.kind, self.detail = case, kind, detail
        super().__init__(f"{kind}: {detail}; case {case.label}")


def compare_batch(oracle, cases):
    try:
        actual = oracle.evaluate_many((c.message, c.time) for c in cases)
    except Exception as exc:
        # Identify a reproducer when transport fails before individual replies exist.
        for case in cases:
            try:
                oracle.evaluate_many([(case.message, case.time)])
            except Exception as single:
                raise FuzzFailure(
                    case, "oracle_transport", f"{type(single).__name__}: {single}"
                ) from single
        raise FuzzFailure(
            cases[0], "batch_transport", f"{type(exc).__name__}: {exc}"
        ) from exc
    for case, lean in zip(cases, actual, strict=True):
        try:
            python = outcome(evaluate_exact, case.message, case.time)
        except Exception as exc:
            raise FuzzFailure(case, "python_exception", type(exc).__name__) from exc
        expected = (
            ("error", lean.code) if isinstance(lean, ReceiverError) else ("ok", lean)
        )
        if python != expected:
            raise FuzzFailure(case, "differential", "Python and Lean disagree")
        if case.expected_position is not None and python != (
            "ok",
            case.expected_position,
        ):
            raise FuzzFailure(case, "metamorphic", case.label)
        expected_code = "ok" if case.expected_error is None else case.expected_error
        actual_code = "ok" if python[0] == "ok" else python[1]
        if expected_code != actual_code:
            raise FuzzFailure(
                case, "error_precedence", f"expected {expected_code}, got {actual_code}"
            )
    return actual


def minimize(oracle, failure, limit=60):
    """Bounded reduction; retain the same failure kind, never turn a timeout into success."""
    current = failure.case
    attempts = 0
    if failure.kind not in {"oracle_transport", "python_exception", "differential"}:
        return current, attempts

    def candidates(case):
        m = case.message
        day_shift = m.day_offset * 86400000000
        if case.time >= day_shift:
            yield replace(
                case, message=replace(m, day_offset=0), time=case.time - day_shift
            )
        seconds_shift = m.second_of_day * 1000000
        if case.time >= seconds_shift:
            yield replace(
                case,
                message=replace(m, second_of_day=0),
                time=case.time - seconds_shift,
            )
        for axis in range(3):
            axes = list(m.coefficients)
            axes[axis] = tuple(0 for _ in axes[axis])
            yield replace(case, message=replace(m, coefficients=tuple(axes)))

    while attempts < limit:
        improved = False
        for candidate in candidates(current):
            if candidate == current:
                continue
            attempts += 1
            try:
                compare_batch(oracle, [candidate])
            except FuzzFailure as reduced:
                if reduced.kind == failure.kind:
                    current, improved = candidate, True
                    break
            if attempts >= limit:
                break
        if not improved:
            break
    return current, attempts


def run(seed, count, batch_size, oracle):
    rng = random.Random(seed)
    coverage = Counter()
    checked = 0
    for offset in range(0, count, batch_size):
        cases = [
            generate(rng, i) for i in range(offset, min(offset + batch_size, count))
        ]
        replies = compare_batch(oracle, cases)
        properties = []
        for i, (case, result) in enumerate(zip(cases, replies, strict=True)):
            coverage[case.label] += 1
            coverage[
                f"outcome:{result.code if isinstance(result, ReceiverError) else 'ok'}"
            ] += 1
            if not isinstance(result, ReceiverError) and (offset + i) % 13 == 0:
                for derived, expected in transformations(case, result):
                    derived = replace(derived, expected_position=expected)
                    if outcome(evaluate_exact, derived.message, derived.time) != (
                        "ok",
                        expected,
                    ):
                        raise FuzzFailure(derived, "metamorphic", derived.label)
                    properties.append(derived)
                    coverage[derived.label] += 1
        for part in range(0, len(properties), batch_size):
            compare_batch(oracle, properties[part : part + batch_size])
        checked += len(cases) + len(properties)
    return {
        "seed": seed,
        "base_cases": count,
        "differential_queries": checked,
        "coverage": dict(sorted(coverage.items())),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, action="append")
    parser.add_argument("--cases", type=int, default=3000, help="base cases per seed")
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--output", type=Path, default=Path(".lake/fuzz"))
    parser.add_argument("--replay", type=Path)
    args = parser.parse_args()
    if args.cases < 1 or args.batch_size < 1:
        parser.error("positive case/batch counts required")
    oracle = LeanOracle(timeout=30)
    args.output.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    reports = []
    try:
        if args.replay:
            artifact = json.loads(args.replay.read_text())
            compare_batch(
                oracle, [decode_case(artifact.get("minimized", artifact["original"]))]
            )
            print("Replayed case passes.")
            return
        for seed in args.seed or [20260911]:
            report = run(seed, args.cases, args.batch_size, oracle)
            reports.append(report)
            print(
                f"Seed {seed}: {report['differential_queries']} differential queries passed.",
                flush=True,
            )
    except FuzzFailure as failure:
        artifact = {
            "format": "ephemeris-message-fuzz-v2",
            "kind": failure.kind,
            "detail": failure.detail,
            "seed": locals().get("seed"),
            "original": encode_case(failure.case),
        }
        path = args.output / "failure.json"
        path.write_text(json.dumps(artifact, indent=2) + "\n")
        minimized, attempts = minimize(oracle, failure)
        artifact.update(minimized=encode_case(minimized), shrink_attempts=attempts)
        path.write_text(json.dumps(artifact, indent=2) + "\n")
        raise SystemExit(f"{failure}\nReproducer: {path}") from failure
    sources = [
        "Ephemeris/Definitions/Message.lean",
        "Ephemeris/Implementation/Rational/PositionReconstruction.lean",
        "Ephemeris/FuzzOracle/OracleProtocol.lean",
        "Ephemeris/FuzzOracle/RationalOracle.lean",
        "python/ephemeris/message.py",
        "python/ephemeris/rational.py",
        "python/fuzz/shared/protocol.py",
        "python/fuzz/shared/clients.py",
        "python/fuzz/shared/cases.py",
        "python/fuzz/shared/reports.py",
        "python/fuzz/drivers/rational.py",
    ]
    report = {
        "format": "ephemeris-message-fuzz-report-v2",
        "protocol": 3,
        **provenance(sources, {"lean-rational": [str(oracle.executable)]}),
        "elapsed_seconds": time.monotonic() - started,
        "profile": "Message",
        "batch_size": args.batch_size,
        "runs": reports,
    }
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        f"Passed {sum(r['differential_queries'] for r in reports)} queries in {report['elapsed_seconds']:.2f}s."
    )


if __name__ == "__main__":
    main()

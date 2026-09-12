"""Seeded P3 float comparisons; reports distinguish model bits from sampled accuracy."""

import argparse
import json
import math
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

from fuzz.shared.clients import FloatOracle
from fuzz.shared.float_cases import edge_cases, exact_position, generate
from fuzz.shared.float_protocol import bits_float
from fuzz.shared.reports import provenance


def run(args):
    names = {
        "all": ["lean", "lean-native", "python", "rust"],
        "triangle": ["lean", "python", "rust"],
        "lean-python": ["lean", "python"],
        "lean-rust": ["lean", "rust"],
        "pair": ["python", "rust"],
    }[args.mode]
    oracles = {name: FloatOracle(name, timeout=args.timeout) for name in names}
    requests = (
        [json.loads(args.replay.read_text())["request"]]
        if args.replay
        else [*edge_cases(), *generate(args.seed, args.cases)]
    )
    args.output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    outcomes = Counter()
    max_error = Q(0)
    successes = 0
    for offset in range(0, len(requests), args.batch_size):
        batch = requests[offset : offset + args.batch_size]
        results = {name: oracle.request_many(batch) for name, oracle in oracles.items()}
        for i, request in enumerate(batch):
            row = {name: values[i] for name, values in results.items()}
            first = row[names[0]]
            if any(value != first for value in row.values()):
                artifact = args.output / "failure.json"
                artifact.write_text(
                    json.dumps({"request": request, "responses": row}, indent=2) + "\n"
                )
                raise AssertionError(f"bit/error disagreement; replay {artifact}")
            outcomes["ok" if first["ok"] else first["error"]] += 1
            if first["ok"] and request["operation"] == "evaluate":
                exact = exact_position(request)
                observed = tuple(
                    Q.from_float(bits_float(int(b))) for b in first["result"]
                )
                error = max(abs(a - b) for a, b in zip(observed, exact, strict=True))
                max_error = max(max_error, error)
                successes += 1
                if error > Q(str(args.tolerance)):
                    artifact = args.output / "failure.json"
                    artifact.write_text(
                        json.dumps(
                            {
                                "request": request,
                                "responses": row,
                                "sampled_error_m": float(error),
                            },
                            indent=2,
                        )
                        + "\n"
                    )
                    raise AssertionError(
                        f"empirical accuracy threshold exceeded; replay {artifact}"
                    )
    sources = [
        "Ephemeris/Definitions/Message.lean",
        "Ephemeris/Implementation/Float/PositionReconstruction.lean",
        "Ephemeris/Implementation/Correctness/Float.lean",
        "Ephemeris/FuzzOracle/FloatOracle.lean",
        "Ephemeris/FuzzOracle/OracleProtocol.lean",
        "python/ephemeris/message.py",
        "python/ephemeris/float.py",
        "rust/src/lib.rs",
        "rust/src/fuzz.rs",
        "python/fuzz/shared/float_protocol.py",
        "python/fuzz/shared/protocol.py",
        "python/fuzz/shared/clients.py",
        "python/fuzz/shared/float_cases.py",
        "python/fuzz/shared/reports.py",
        "python/fuzz/oracles/python_float.py",
        "python/fuzz/drivers/float.py",
    ]
    report = {
        "protocol": 3,
        "mode": args.mode,
        "seed": args.seed,
        "generated_cases": 0 if args.replay else args.cases,
        "replay": str(args.replay) if args.replay else None,
        "requests": len(requests),
        "backends": names,
        "outcomes": dict(outcomes),
        "successful_positions": successes,
        "max_sampled_error_m": float(max_error),
        "empirical_threshold_m": args.tolerance,
        "accuracy_is_formally_proved": False,
        "elapsed_seconds": time.perf_counter() - started,
        **provenance(
            sources, {name: oracle.command for name, oracle in oracles.items()}
        ),
    }
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode",
        choices=["all", "triangle", "lean-python", "lean-rust", "pair"],
        default="all",
    )
    parser.add_argument("--cases", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=20260911)
    parser.add_argument("--batch-size", type=int, default=128)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument(
        "--tolerance",
        type=float,
        default=1e-5,
        help="empirical test threshold, not a proved bound",
    )
    parser.add_argument("--output", type=Path, default=Path(".lake/fixed-float-fuzz"))
    parser.add_argument("--replay", type=Path)
    args = parser.parse_args()
    if (
        args.cases < 0
        or args.batch_size <= 0
        or not math.isfinite(args.timeout)
        or args.timeout <= 0
        or not math.isfinite(args.tolerance)
        or args.tolerance < 0
    ):
        parser.error(
            "finite nonnegative limits required, with positive batch size and timeout"
        )
    run(args)


if __name__ == "__main__":
    main()

"""P3 process throughput including JSON and process startup, not flight WCET."""

import argparse
import time

from fuzz.shared.clients import FloatOracle
from fuzz.shared.float_cases import generate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases", type=int, default=1000)
    args = parser.parse_args()
    requests = list(generate(20260911, args.cases))
    for backend in ["lean", "python", "rust"]:
        start = time.perf_counter()
        replies = FloatOracle(backend).request_many(requests)
        elapsed = time.perf_counter() - start
        print(
            f"{backend}: {len(replies)} requests in {elapsed:.3f}s (includes process/JSON overhead)"
        )


if __name__ == "__main__":
    main()

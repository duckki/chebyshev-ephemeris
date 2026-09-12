"""Independent Python P3 process server, usable by Rust tests without Lean."""

import json
import sys

from ephemeris.float import require_binary64
from fuzz.shared.float_protocol import respond


def main():
    require_binary64()
    for line in sys.stdin:
        print(json.dumps(respond(line), separators=(",", ":")))


if __name__ == "__main__":
    main()

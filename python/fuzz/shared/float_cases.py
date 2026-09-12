"""P3 input generation and independent exact arithmetic for tests only."""

import random
from copy import deepcopy
from fractions import Fraction as Q

from ephemeris.message import EPOCH_ORIGIN_TICK, WIDTHS


def fixture():
    axes = [[0] * 11 for _ in range(3)]
    axes[0][:2] = [3200, 640]
    return {
        "version": 3,
        "operation": "evaluate",
        "message": {
            "day_offset": 0,
            "second_of_day": 43200,
            "validity_code": 2,
            "coefficients": axes,
        },
        "time": EPOCH_ORIGIN_TICK + 43200000000,
    }


def interval(m):
    return (
        EPOCH_ORIGIN_TICK
        + m["day_offset"] * 86400000000
        + m["second_of_day"] * 1000000,
        m["validity_code"] * 1800000000,
    )


def edge_cases():
    cases = []
    base = fixture()
    start, duration = interval(base["message"])
    for t in [
        0,
        (1 << 64) - 1,
        start - 1,
        start,
        start + 1,
        start + duration // 2,
        start + duration - 1,
        start + duration,
        start + duration + 1,
    ]:
        q = deepcopy(base)
        q["time"] = t
        cases.append(q)
    for field, values in [
        ("day_offset", [0, 16383, 16384, 65535]),
        ("second_of_day", [0, 86399, 86400, (1 << 32) - 1]),
        ("validity_code", [0, 1, 2, 7, 8, 255]),
    ]:
        for value in values:
            q = deepcopy(base)
            q["message"][field] = value
            q["time"] = interval(q["message"])[0]
            cases.append(q)
    for axis in range(3):
        for size in [0, 1, 10, 12, 15]:
            q = deepcopy(base)
            q["message"]["coefficients"][axis] = [0] * size
            cases.append(q)
        for i, width in enumerate(WIDTHS):
            bound = 1 << (width - 1)
            for value in [-bound - 1, -bound, -1, 0, 1, bound - 1, bound]:
                q = deepcopy(base)
                q["message"]["coefficients"][axis][i] = value
                cases.append(q)
    # Earliest invalid field must win even when several later fields also fail.
    for day, seconds, validity in [(16384, 86400, 0), (0, 86400, 0), (0, 0, 0)]:
        q = deepcopy(base)
        q["message"].update(
            day_offset=day, second_of_day=seconds, validity_code=validity
        )
        q["message"]["coefficients"] = [[], [], []]
        cases.append(q)
    for q in [-(1 << 31), -(1 << 31) + 1, -1, 0, 1, (1 << 31) - 1]:
        cases.append({"version": 3, "operation": "coefficient", "coefficient": q})
    for i in range(31):
        for sign in [-1, 1]:
            for delta in [-1, 0, 1]:
                q = sign * (1 << i) + delta
                if -(1 << 31) <= q < (1 << 31):
                    cases.append(
                        {"version": 3, "operation": "coefficient", "coefficient": q}
                    )
    return cases


def generate(seed, count):
    rng = random.Random(seed)
    for i in range(count):
        axes = [
            [rng.randrange(-(1 << (w - 1)), 1 << (w - 1)) for w in WIDTHS]
            for _ in range(3)
        ]
        if i % 5 == 0:
            axes = [
                [rng.choice([-(1 << (w - 1)), (1 << (w - 1)) - 1, 0]) for w in WIDTHS]
                for _ in range(3)
            ]
        m = dict(
            day_offset=rng.randrange(16384),
            second_of_day=rng.randrange(86400),
            validity_code=rng.randrange(1, 8),
            coefficients=axes,
        )
        start, duration = interval(m)
        time = rng.choice(
            [start, start + duration, start + rng.randrange(duration + 1)]
        )
        yield {"version": 3, "operation": "evaluate", "message": m, "time": time}
        yield {
            "version": 3,
            "operation": "coefficient",
            "coefficient": rng.randrange(-(1 << 31), 1 << 31),
        }
        # Identical relative epoch, different absolute day: tests subtract-before-convert.
        shifted = deepcopy(m)
        shifted["day_offset"] = (m["day_offset"] + 8192) % 16384
        shifted_time = time + (shifted["day_offset"] - m["day_offset"]) * 86400000000
        yield {
            "version": 3,
            "operation": "evaluate",
            "message": shifted,
            "time": shifted_time,
        }


def exact_position(request):
    """Independent rational interpretation of the same integer message and tick.

    Unbounded arithmetic belongs to this test oracle, never the native float code.
    """
    m = request["message"]
    start, duration = interval(m)
    x = 2 * Q(request["time"] - start, duration) - 1
    basis = [Q(1), x]
    for _ in range(2, 11):
        basis.append(2 * x * basis[-1] - basis[-2])
    return tuple(
        sum(Q(q, 32) * t for q, t in zip(axis, basis, strict=True))
        for axis in m["coefficients"]
    )

"""Bounded Message cases, independent exact properties, and replay fixtures."""

from dataclasses import asdict, dataclass, replace
from fractions import Fraction as Q

from ephemeris.message import WIDTHS, Message, ReceiverError, duration_ticks, start_tick


@dataclass(frozen=True)
class Case:
    message: Message
    time: int
    label: str
    expected_error: str | None = None
    expected_position: tuple[Q, ...] | None = None


def outcome(function, message, when):
    try:
        return "ok", function(message, when)
    except ReceiverError as exc:
        return "error", exc.code


def generate(rng, index):
    axes = tuple(
        tuple(
            rng.choice([-(1 << (w - 1)), (1 << (w - 1)) - 1, 0])
            if index % 5 == 0
            else rng.randrange(-(1 << (w - 1)), 1 << (w - 1))
            for w in WIDTHS
        )
        for _ in range(3)
    )
    m = Message(
        rng.randrange(16384),
        rng.choice([0, 86399, rng.randrange(86400)]),
        rng.randrange(1, 8),
        axes,
    )
    start, duration = start_tick(m), duration_ticks(m)
    offset = rng.choice(
        [0, 1, duration // 2, duration - 1, duration, rng.randrange(duration + 1)]
    )
    when = start + offset
    mode = index % 12
    code = None
    label = f"valid:{'start' if offset == 0 else 'end' if offset == duration else 'interior'}"
    if mode == 6:
        m = replace(
            m,
            day_offset=rng.choice([16384, 65535]),
            second_of_day=86400,
            validity_code=0,
        )
        code, label = "invalidDayOffset", "invalid:day_precedence"
    elif mode == 7:
        m = replace(
            m, second_of_day=rng.choice([86400, (1 << 32) - 1]), validity_code=0
        )
        code, label = "invalidSecondOfDay", "invalid:seconds_precedence"
    elif mode == 8:
        m = replace(m, validity_code=rng.choice([0, 8, 255]), coefficients=((), (), ()))
        code, label = "invalidValidityCode", "invalid:validity_precedence"
    elif mode == 9:
        axes = list(m.coefficients)
        axis = rng.randrange(3)
        axes[axis] = axes[axis][:-1] if rng.randrange(2) else axes[axis] + (0,)
        m = replace(m, coefficients=tuple(axes))
        code, label = "coefficientCountMismatch", "invalid:shape"
    elif mode == 10:
        axes = [list(a) for a in m.coefficients]
        axis, i = rng.randrange(3), rng.randrange(11)
        bound = 1 << (WIDTHS[i] - 1)
        axes[axis][i] = rng.choice([-bound - 1, bound])
        m = replace(m, coefficients=axes)
        code, label = "coefficientOutOfRange", "invalid:coefficient"
    elif mode == 11:
        when = rng.choice([0, (1 << 64) - 1, start - 1, start + duration + 1])
        code, label = "outsideValidity", "invalid:window"
    return Case(m, when, label, code)


def transformations(case, result):
    """Exact algebraic properties whose derived messages also satisfy the profile."""
    m, t = case.message, case.time
    day = (m.day_offset + 8192) % 16384
    yield (
        Case(
            replace(m, day_offset=day),
            t + (day - m.day_offset) * 86400000000,
            "property:epoch_shift",
        ),
        result,
    )
    yield (
        Case(
            replace(
                m,
                coefficients=(m.coefficients[2], m.coefficients[0], m.coefficients[1]),
            ),
            t,
            "property:axis_permutation",
        ),
        (result[2], result[0], result[1]),
    )
    if all(
        q != -(1 << (w - 1))
        for a in m.coefficients
        for q, w in zip(a, WIDTHS, strict=True)
    ):
        yield (
            Case(
                replace(
                    m, coefficients=tuple(tuple(-q for q in a) for a in m.coefficients)
                ),
                t,
                "property:negation",
            ),
            tuple(-q for q in result),
        )
    if all(a[0] < (1 << 29) - 1 for a in m.coefficients):
        axes = tuple((a[0] + 1, *a[1:]) for a in m.coefficients)
        yield (
            Case(replace(m, coefficients=axes), t, "property:constant_translation"),
            tuple(q + Q(1, 32) for q in result),
        )
    if all(
        q != -(1 << (WIDTHS[i] - 1))
        for a in m.coefficients
        for i, q in enumerate(a)
        if i % 2
    ):
        parity = tuple(
            tuple(q if i % 2 == 0 else -q for i, q in enumerate(a))
            for a in m.coefficients
        )
        mirrored = 2 * start_tick(m) + duration_ticks(m) - t
        yield (
            Case(
                replace(m, coefficients=parity), mirrored, "property:chebyshev_parity"
            ),
            result,
        )


def encode_case(case):
    return {
        "message": asdict(case.message),
        "time": case.time,
        "label": case.label,
        "expected_error": case.expected_error,
        "expected_position": None
        if case.expected_position is None
        else [[hex(q.numerator), hex(q.denominator)] for q in case.expected_position],
    }


def decode_case(data):
    expected = data.get("expected_position")
    return Case(
        Message(**data["message"]),
        data["time"],
        data["label"],
        data.get("expected_error"),
        None
        if expected is None
        else tuple(Q(int(n, 16), int(d, 16)) for n, d in expected),
    )

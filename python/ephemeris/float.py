"""Bounded binary64 receiver matching Lean Implementation.Float (FP1/FP2/FP3).

A message describes a trajectory segment. evaluate_float returns its XYZ position
in meters at a UInt64 microsecond Julian-date tick. There is no implicit input
quantization in this implementation.
"""

import math
import sys

from .message import (
    Message,
    ReceiverError,
    _bounded,
    _u64,
    duration_ticks,
    start_tick,
    validate_query,
)


def require_binary64() -> None:
    if (
        sys.float_info.radix,
        sys.float_info.mant_dig,
        sys.float_info.max_exp,
        sys.float_info.min_exp,
        sys.float_info.rounds,
    ) != (2, 53, 1024, -1021, 1):
        raise RuntimeError("FP3 requires binary64 with round-to-nearest")


def coefficient(q: int) -> float:
    _bounded(q, -(1 << 31), (1 << 31) - 1, "coefficient")
    # Matches Lean's bounded signed-conversion adaptation, including Int32.min.
    value = -float(-(q + 1) + 1) if q < 0 else float(q)
    return value / 32.0


def _finite(value: float) -> float:
    if not math.isfinite(value):
        raise ReceiverError("nonfiniteComputation")
    return value


def _normalized_epoch(message: Message, time: int) -> float:
    elapsed = _u64(time - start_tick(message))  # Caller has validated order.
    ratio = _finite(float(elapsed) / float(duration_ticks(message)))
    scaled = _finite(2.0 * ratio)
    return _finite(scaled - 1.0)


def evaluate_float(message: Message, time: int) -> tuple[float, float, float]:
    """Checked position at time, with the same error precedence as Lean.evaluate."""
    require_binary64()
    validate_query(message, time)
    argument = _normalized_epoch(message, time)
    basis = []
    for i in range(11):
        if i == 0:
            value = 1.0
        elif i == 1:
            value = argument
        else:
            twice_x = _finite(2.0 * argument)
            product = _finite(twice_x * basis[i - 1])
            value = _finite(product - basis[i - 2])
        basis.append(value)
    result = []
    for axis in message.coefficients:
        total = 0.0
        for i in range(11):
            product = _finite(coefficient(axis[i]) * basis[i])
            total = _finite(total + product)
        result.append(total)
    return tuple(result)

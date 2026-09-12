"""Exact Fraction evaluation of the same bounded Message accepted by Float.

Matches Lean Implementation.Rational, including exact Julian-date normalization.
The Lean implementation is proved; this Python port is differentially tested.
"""

from fractions import Fraction as Q

from .message import Message, validate_query
from .message import ReceiverError as ReceiverError


def evaluate_exact(message: Message, time: int) -> tuple[Q, Q, Q]:
    """Return exact XYZ meters at a UInt64 microsecond Julian-date tick.

    Inputs, inclusive validity window, and errors are shared with evaluate_float.
    Fractions are working values and outputs, never an alternative input format.
    """
    validate_query(message, time)
    reference_day = Q(4922001, 2) + message.day_offset
    start = reference_day + Q(message.second_of_day, 86400)
    end = start + Q(message.validity_code, 48)
    argument = 2 * ((Q(time, 86400000000) - start) / (end - start)) - 1
    basis: list[Q] = []
    for i in range(11):
        if i == 0:
            basis.append(Q(1))
        elif i == 1:
            basis.append(argument)
        else:
            basis.append(2 * argument * basis[i - 1] - basis[i - 2])
    result = []
    for axis in message.coefficients:
        value = Q(0)
        for i in range(11):
            value = value + Q(axis[i], 32) * basis[i]
        result.append(value)
    return tuple(result)

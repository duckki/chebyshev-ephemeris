"""Bounded decoded Message, tick arithmetic, and validation for the Float receiver.

Matches Lean Definitions.Message. Fixed-point integers are inputs; the receiver
interprets them as binary64 values during reconstruction.
"""

from dataclasses import dataclass

WIDTHS = (30, 28, 25, 21, 19, 17, 14, 12, 9, 7, 5)
EPOCH_ORIGIN_TICK = 212630443200000000
UINT64_MAX = 18446744073709551615


class ReceiverError(ValueError):
    """A checked receiver rejection, using the corresponding Lean error code."""

    def __init__(self, code: str):
        self.code = code
        super().__init__(code)


def _bounded(value: int, low: int, high: int, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer")
    if not low <= value <= high:
        raise ValueError(f"{name} exceeds its integer carrier")
    return value


def _u64(value: int) -> int:
    return _bounded(value, 0, UINT64_MAX, "uint64")


@dataclass(frozen=True)
class Message:
    """Decoded bounded carriers; profile validity is checked during evaluation.

    Coefficients are signed integer multiples of 1/32 meter. Copy input arrays
    so a caller cannot mutate a validated value during reconstruction.
    """

    day_offset: int
    second_of_day: int
    validity_code: int
    coefficients: tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]

    def __post_init__(self):
        _bounded(self.day_offset, 0, (1 << 16) - 1, "day_offset")
        _bounded(self.second_of_day, 0, (1 << 32) - 1, "second_of_day")
        _bounded(self.validity_code, 0, (1 << 8) - 1, "validity_code")
        axes = tuple(tuple(axis) for axis in self.coefficients)
        if len(axes) != 3:
            raise ValueError("expected three coordinate arrays")
        for axis in axes:
            for q in axis:
                _bounded(q, -(1 << 31), (1 << 31) - 1, "coefficient")
        object.__setattr__(self, "coefficients", axes)


def start_tick(message: Message) -> int:
    day = _u64(message.day_offset * 86400000000)
    seconds = _u64(message.second_of_day * 1000000)
    return _u64(_u64(EPOCH_ORIGIN_TICK + day) + seconds)


def duration_ticks(message: Message) -> int:
    return _u64(message.validity_code * 1800000000)


def validate_query(message: Message, time: int) -> None:
    if not isinstance(message, Message):
        raise TypeError("expected a fixed-point Message")
    _u64(time)
    if message.day_offset >= 16384:
        raise ReceiverError("invalidDayOffset")
    if message.second_of_day >= 86400:
        raise ReceiverError("invalidSecondOfDay")
    if not 1 <= message.validity_code <= 7:
        raise ReceiverError("invalidValidityCode")
    if any(len(axis) != 11 for axis in message.coefficients):
        raise ReceiverError("coefficientCountMismatch")
    for axis in message.coefficients:
        for q, width in zip(axis, WIDTHS, strict=True):
            bound = 1 << (width - 1)  # At most 2^29, inside signed Int32.
            if not -bound <= q < bound:
                raise ReceiverError("coefficientOutOfRange")
    start = start_tick(message)
    if time < start:
        raise ReceiverError("outsideValidity")
    if _u64(time - start) > duration_ticks(message):
        raise ReceiverError("outsideValidity")

"""Local, integer-only decimal conversion without changing interpreter limits."""

import re

_INTEGER = re.compile(r"-?[0-9]+\Z")


def decimal_integer(value: str) -> int:
    """Decode only ASCII decimal integer strings, including large exact numerators and denominators."""
    if type(value) is not str or not _INTEGER.fullmatch(value):
        raise ValueError("expected an ASCII decimal integer string")
    try:
        return int(value)
    except ValueError:
        negative = value.startswith("-")
        digits = value[1:] if negative else value
        result = 0
        for offset in range(0, len(digits), 9):
            chunk = digits[offset : offset + 9]
            result = result * 10 ** len(chunk) + int(chunk)
        return -result if negative else result

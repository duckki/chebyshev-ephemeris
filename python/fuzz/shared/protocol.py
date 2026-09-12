"""Shared P3 Message requests and exact-rational response parsing.

Integer carriers are identical for Rational and Float; only successful responses
have a different numerical representation. This is tested fuzz infrastructure.
"""

import json
from dataclasses import asdict
from fractions import Fraction

from ephemeris.message import Message, ReceiverError, _u64

from .decimal import decimal_integer


class OracleError(RuntimeError):
    """Oracle installation, process, or protocol failure (not receiver rejection)."""


def _encode_request(request: dict) -> str:
    return json.dumps(request, separators=(",", ":"))


def parse_request(line: str):
    """P3 number tokens are integers, without decimals, exponents, or -0."""

    def reject_number(token):
        raise ValueError(f"invalid P3 number token: {token}")

    def integer(token):
        return reject_number(token) if token == "-0" else int(token)

    return json.loads(
        line, parse_int=integer, parse_float=reject_number, parse_constant=reject_number
    )


def _request(message: Message, time: int) -> dict:
    if not isinstance(message, Message):
        raise TypeError("expected a fixed-point Message")
    _u64(time)
    fields = asdict(message)
    fields["coefficients"] = [list(axis) for axis in message.coefficients]
    return {"version": 3, "operation": "evaluate", "message": fields, "time": time}


def exact_response(line: str) -> tuple[Fraction, ...] | ReceiverError:
    try:
        payload = json.loads(line)
        if type(payload) is not dict or type(payload.get("ok")) is not bool:
            raise ValueError("missing Boolean status")
        if not payload["ok"]:
            code = payload.get("error")
            if code not in (
                "invalidDayOffset",
                "invalidSecondOfDay",
                "invalidValidityCode",
                "coefficientOutOfRange",
                "coefficientCountMismatch",
                "outsideValidity",
            ):
                raise ValueError(f"unexpected oracle error: {code}")
            return ReceiverError(code)
        position = payload["position"]
        if type(position) is not list or len(position) != 3:
            raise ValueError("expected three position components")
        values = []
        for pair in position:
            if (
                type(pair) is not list
                or len(pair) != 2
                or any(type(v) is not str for v in pair)
            ):
                raise ValueError("invalid rational pair")
            num, den = map(decimal_integer, pair)
            if den <= 0:
                raise ValueError("nonpositive denominator")
            values.append(Fraction(num, den))
        return tuple(values)
    except (ValueError, KeyError, TypeError) as exc:
        raise OracleError(f"invalid oracle response: {exc}") from exc

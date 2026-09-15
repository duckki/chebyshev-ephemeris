"""P3 bounded Message requests and process errors for Float differential tests."""

import json
from dataclasses import asdict

from ephemeris.message import Message, _u64


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

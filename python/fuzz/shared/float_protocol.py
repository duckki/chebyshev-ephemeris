"""P3 bounded-input test-process protocol shared by float oracles and fuzzing."""

import json
import math
import struct

from ephemeris.float import coefficient, evaluate_float
from ephemeris.message import Message, ReceiverError, _u64

from .protocol import OracleError, parse_request

ERRORS = {
    "invalidProtocol",
    "invalidDayOffset",
    "invalidSecondOfDay",
    "invalidValidityCode",
    "coefficientCountMismatch",
    "coefficientOutOfRange",
    "outsideValidity",
    "nonfiniteComputation",
}


def float_bits(value: float) -> int:
    return struct.unpack(">Q", struct.pack(">d", value))[0]


def bits_float(bits: int) -> float:
    return struct.unpack(">d", struct.pack(">Q", _u64(bits)))[0]


def respond(line: str):
    try:
        j = parse_request(line)
        if (
            type(j) is not dict
            or type(j.get("version")) is not int
            or j["version"] != 3
        ):
            raise ValueError("expected P3")
        if j["operation"] == "coefficient":
            result = str(float_bits(coefficient(j["coefficient"])))
        elif j["operation"] == "evaluate":
            m = j["message"]
            axes = m["coefficients"]
            if type(axes) is not list or any(type(axis) is not list for axis in axes):
                raise ValueError("expected coefficient arrays")
            result = [
                str(float_bits(v))
                for v in evaluate_float(
                    Message(
                        m["day_offset"], m["second_of_day"], m["validity_code"], axes
                    ),
                    j["time"],
                )
            ]
        else:
            raise ValueError("unknown operation")
        return {"ok": True, "result": result}
    except ReceiverError as error:
        return {"ok": False, "error": error.code}
    except (ValueError, TypeError, KeyError, OverflowError):
        return {"ok": False, "error": "invalidProtocol"}


def response(line: str, operation: str):
    """Validate response shape, bit width, finiteness, and error vocabulary."""
    try:
        j = json.loads(line)
        if type(j) is not dict or type(j.get("ok")) is not bool:
            raise ValueError("missing Boolean status")
        if not j["ok"]:
            if j.get("error") not in ERRORS:
                raise ValueError("unknown error")
            return {"ok": False, "error": j["error"]}
        values = [j["result"]] if operation == "coefficient" else j["result"]
        if type(values) is not list or len(values) != (
            1 if operation == "coefficient" else 3
        ):
            raise ValueError("wrong result shape")
        for value in values:
            if (
                type(value) is not str
                or not value
                or len(value) > 20
                or not value.isascii()
                or not value.isdecimal()
            ):
                raise ValueError("expected decimal uint64 bits")
            if not math.isfinite(bits_float(int(value))):
                raise ValueError("nonfinite success")
        return {"ok": True, "result": j["result"]}
    except (ValueError, TypeError, KeyError, OverflowError) as error:
        raise OracleError(f"invalid P3 response: {error}") from error

import json
import random
import subprocess
import unittest
from copy import deepcopy
from dataclasses import replace
from fractions import Fraction as Q

from ephemeris import Message, ReceiverError, evaluate_exact, evaluate_float
from ephemeris.message import duration_ticks, start_tick
from fuzz.shared.cases import generate
from fuzz.shared.clients import LeanOracle
from fuzz.shared.float_cases import exact_position
from fuzz.shared.protocol import OracleError, _request
from fuzz.shared.protocol import exact_response as _response


def fixture() -> Message:
    return Message(
        0,
        43200,
        2,
        ([96, 64, 32] + [0] * 8, [-32, 0, 64] + [0] * 8, [0, 32, 0] + [0] * 8),
    )


class ReceiverTests(unittest.TestCase):
    def test_hand_calculated_positions(self):
        m = fixture()
        start = 212630486400000000
        for offset, expected in [
            (0, (2, 1, -1)),
            (900000000, (Q(3, 2), -2, Q(-1, 2))),
            (1800000000, (2, -3, 0)),
            (3600000000, (6, 1, 1)),
        ]:
            with self.subTest(offset=offset):
                self.assertEqual(evaluate_exact(m, start + offset), expected)

    def test_shared_message_and_errors(self):
        from ephemeris.float import Message as FloatMessage
        from ephemeris.float import ReceiverError as FloatError
        from ephemeris.rational import Message as RationalMessage
        from ephemeris.rational import ReceiverError as RationalError

        self.assertIs(Message, FloatMessage)
        self.assertIs(Message, RationalMessage)
        self.assertIs(ReceiverError, FloatError)
        self.assertIs(ReceiverError, RationalError)
        m = fixture()
        self.assertEqual(
            evaluate_exact(m, start_tick(m)), evaluate_float(m, start_tick(m))
        )

    def test_constant_and_empty_polynomials(self):
        m = replace(
            fixture(), coefficients=([224] + [0] * 10, [-96] + [0] * 10, [0] * 11)
        )
        self.assertEqual(evaluate_exact(m, start_tick(m)), (7, -3, 0))
        with self.assertRaises(ReceiverError) as caught:
            evaluate_exact(replace(m, coefficients=([], [], [])), start_tick(m))
        self.assertEqual(caught.exception.code, "coefficientCountMismatch")

    def test_rejections_and_precedence(self):
        m = fixture()
        cases = [
            (
                replace(m, day_offset=16384, second_of_day=86400, validity_code=0),
                0,
                "invalidDayOffset",
            ),
            (replace(m, second_of_day=86400, validity_code=0), 0, "invalidSecondOfDay"),
            (
                replace(m, validity_code=0, coefficients=([], [], [])),
                0,
                "invalidValidityCode",
            ),
            (replace(m, validity_code=8), 0, "invalidValidityCode"),
            (replace(m, coefficients=([], [], [])), 0, "coefficientCountMismatch"),
            (
                replace(m, coefficients=([1 << 29] + [0] * 10, [0] * 11, [0] * 11)),
                0,
                "coefficientOutOfRange",
            ),
            (m, start_tick(m) - 1, "outsideValidity"),
            (m, start_tick(m) + duration_ticks(m) + 1, "outsideValidity"),
        ]
        for candidate, time, code in cases:
            for evaluator in [evaluate_exact, evaluate_float]:
                with (
                    self.subTest(code=code, evaluator=evaluator),
                    self.assertRaises(ReceiverError) as caught,
                ):
                    evaluator(candidate, time)
                self.assertEqual(caught.exception.code, code)

    def test_no_implicit_input_conversion_or_unbounded_carriers(self):
        m = fixture()
        for value in [0.1, True, float("nan"), float("inf"), "0", Q(1, 2), Q(1)]:
            with self.subTest(value=value):
                with self.assertRaises(TypeError):
                    replace(m, second_of_day=value)
                with self.assertRaises(TypeError):
                    evaluate_exact(m, value)
        for field, value in [
            ("day_offset", 1 << 16),
            ("second_of_day", 1 << 32),
            ("validity_code", 256),
        ]:
            with self.assertRaises(ValueError):
                replace(m, **{field: value})
        for time in [-1, 1 << 64]:
            with self.assertRaises(ValueError):
                evaluate_exact(m, time)

    def test_coefficient_inputs_are_copied(self):
        axes = [[224] + [0] * 10, [-96] + [0] * 10, [0] * 11]
        m = replace(fixture(), coefficients=axes)
        axes[0][0] = 999
        axes.append([100])
        self.assertEqual(evaluate_exact(m, start_tick(m)), (7, -3, 0))


class OracleIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.oracle = LeanOracle()

    def test_nonmidnight_endpoints_and_errors(self):
        m = fixture()
        queries = [
            (m, start_tick(m) + offset)
            for offset in [-1, 0, 1, 900000000, 1800000000, 3600000000, 3600000001]
        ]
        queries.extend(
            [
                (replace(m, day_offset=16384, second_of_day=86400, validity_code=0), 0),
                (replace(m, second_of_day=86400, validity_code=0), 0),
                (replace(m, validity_code=0, coefficients=([], [], [])), 0),
                (replace(m, coefficients=([], [], [])), 0),
            ]
        )
        self.assert_agreement(queries)

    def test_reproducible_cross_language_cases(self):
        rng = random.Random(20260911)
        cases = [generate(rng, i) for i in range(120)]
        self.assert_agreement((c.message, c.time) for c in cases)

    def test_full_julian_date_matches_independent_relative_tick_arithmetic(self):
        m = fixture()
        queries = []
        for day in [0, 8192, 16383]:
            for validity in [1, 2, 7]:
                candidate = replace(
                    m, day_offset=day, validity_code=validity, second_of_day=86399
                )
                for offset in [
                    0,
                    1,
                    duration_ticks(candidate) // 7,
                    duration_ticks(candidate),
                ]:
                    t = start_tick(candidate) + offset
                    expected = exact_position(_request(candidate, t))
                    self.assertEqual(evaluate_exact(candidate, t), expected)
                    queries.append((candidate, t))
        self.assert_agreement(queries)

    def test_oracle_continues_after_malformed_request(self):
        good = _request(fixture(), start_tick(fixture()))
        invalid = []
        for field, value in [
            ("version", 1),
            ("operation", "coefficient"),
            ("time", ["1", "2"]),
            ("time", -1),
            ("time", 1 << 64),
            ("time", 1.0),
            ("time", True),
        ]:
            candidate = dict(good)
            candidate[field] = value
            invalid.append(json.dumps(candidate))
        for field, value in [
            ("day_offset", 65536),
            ("second_of_day", 1 << 32),
            ("validity_code", 256),
            ("coefficients", [[1 << 31] * 11] * 3),
        ]:
            candidate = deepcopy(good)
            candidate["message"][field] = value
            invalid.append(json.dumps(candidate))
        for token in ["1e0", "-0", "1.0"]:
            candidate = json.dumps(good).replace(str(good["time"]), token)
            invalid.append(candidate)
        data = "\n".join(["not JSON", *invalid, json.dumps(good)]) + "\n"
        result = subprocess.run(
            [str(self.oracle.executable)],
            input=data,
            capture_output=True,
            text=True,
            check=True,
            timeout=30,
        )
        replies = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(replies), len(invalid) + 2)
        for reply in replies[:-1]:
            self.assertEqual(reply, {"ok": False, "error": "invalidProtocol"})
        self.assertTrue(replies[-1]["ok"])

    def test_bad_responses_are_process_errors(self):
        for payload in [
            {},
            {"ok": 1},
            {"ok": True, "position": [["1", "0"]] * 3},
            {"ok": False, "error": "invalidProtocol"},
        ]:
            with self.subTest(payload=payload), self.assertRaises(OracleError):
                _response(json.dumps(payload))

    def test_empty_batch(self):
        self.assertEqual(self.oracle.evaluate_many([]), [])

    def assert_agreement(self, queries):
        queries = list(queries)
        for (message, time), result in zip(
            queries, self.oracle.evaluate_many(queries), strict=True
        ):
            with self.subTest(time=time):
                try:
                    expected = evaluate_exact(message, time)
                except ReceiverError as error:
                    self.assertIsInstance(result, ReceiverError)
                    self.assertEqual(result.code, error.code)
                else:
                    self.assertEqual(result, expected)


if __name__ == "__main__":
    unittest.main()

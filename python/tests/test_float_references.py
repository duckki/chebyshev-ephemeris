import json
import subprocess
import unittest
from copy import deepcopy
from dataclasses import replace

from ephemeris.float import coefficient, evaluate_float
from ephemeris.message import WIDTHS, Message, ReceiverError, duration_ticks, start_tick
from fuzz.shared.clients import FloatOracle
from fuzz.shared.float_cases import edge_cases, fixture, generate
from fuzz.shared.float_protocol import float_bits, response
from fuzz.shared.protocol import OracleError


def message():
    return Message(**fixture()["message"])


class FloatReceiverTests(unittest.TestCase):
    def test_line_and_inclusive_window(self):
        m = message()
        start = start_tick(m)
        duration = duration_ticks(m)
        for offset, x in [(0, 80.0), (duration // 2, 100.0), (duration, 120.0)]:
            self.assertEqual(evaluate_float(m, start + offset), (x, 0.0, 0.0))
        for t in [start - 1, start + duration + 1, 0, (1 << 64) - 1]:
            with self.assertRaises(ReceiverError) as caught:
                evaluate_float(m, t)
            self.assertEqual(caught.exception.code, "outsideValidity")

    def test_carriers_reject_unbounded_or_implicit_inputs(self):
        for field, values in [
            ("day_offset", [-1, 65536, True, 0.0]),
            ("second_of_day", [-1, 1 << 32]),
            ("validity_code", [-1, 256]),
        ]:
            for value in values:
                with self.assertRaises((TypeError, ValueError)):
                    replace(message(), **{field: value})
        for q in [-(1 << 31) - 1, 1 << 31, True, 1.0]:
            with self.assertRaises((TypeError, ValueError)):
                coefficient(q)
        for t in [-1, 1 << 64, True, 1.0]:
            with self.assertRaises((TypeError, ValueError)):
                evaluate_float(message(), t)

    def test_profile_errors_precede_time(self):
        m = message()
        cases = [
            (replace(m, day_offset=16384, validity_code=0), "invalidDayOffset"),
            (replace(m, second_of_day=86400, validity_code=0), "invalidSecondOfDay"),
            (
                replace(m, validity_code=0, coefficients=((), (), ())),
                "invalidValidityCode",
            ),
            (replace(m, coefficients=((), (), ())), "coefficientCountMismatch"),
        ]
        for candidate, code in cases:
            with self.assertRaises(ReceiverError) as caught:
                evaluate_float(candidate, 0)
            self.assertEqual(caught.exception.code, code)

    def test_arrays_are_copied_and_widths_checked(self):
        data = fixture()["message"]
        m = Message(**data)
        data["coefficients"][0][0] = 999
        self.assertEqual(m.coefficients[0][0], 3200)
        for axis in range(3):
            for i, width in enumerate(WIDTHS):
                data = fixture()["message"]
                data["coefficients"][axis][i] = 1 << (width - 1)
                with self.assertRaises(ReceiverError) as caught:
                    evaluate_float(Message(**data), 0)
                self.assertEqual(caught.exception.code, "coefficientOutOfRange")

    def test_all_int32_extremes_decode(self):
        for q in [-(1 << 31), -(1 << 31) + 1, -1, 0, 1, (1 << 31) - 1]:
            self.assertEqual(float_bits(coefficient(q)), float_bits(float(q) / 32.0))

    def test_response_validation(self):
        for payload in [
            {},
            {"ok": 1},
            {"ok": False, "error": "unknown"},
            {"ok": True, "result": []},
            {"ok": True, "result": ["1"] * 2},
            {"ok": True, "result": [str(1 << 64)] * 3},
            {"ok": True, "result": [str(0x7FF0000000000000)] * 3},
        ]:
            with self.assertRaises(OracleError):
                response(json.dumps(payload), "evaluate")


class FloatOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.oracles = [
            FloatOracle(name) for name in ["lean", "lean-native", "python", "rust"]
        ]

    def test_boundaries_and_seeded_cases(self):
        cases = [*edge_cases(), *generate(20260911, 20)]
        results = [oracle.request_many(cases) for oracle in self.oracles]
        for result in results[1:]:
            self.assertEqual(results[0], result)

    def test_protocol_rejection_and_recovery(self):
        cases = [
            {"version": 2},
            {"version": 3, "operation": "unknown"},
            {"version": 3, "operation": "coefficient", "coefficient": 1 << 31},
            {"version": 3, "operation": "coefficient", "coefficient": -(1 << 31) - 1},
        ]
        q = fixture()
        q["time"] = 1 << 64
        cases.append(q)
        cases.extend(
            {"version": 3, "operation": "coefficient", "coefficient": value}
            for value in [1.0, 1.5, True, None, "1", {}, []]
        )
        cases.append(fixture())
        results = [oracle.request_many(cases) for oracle in self.oracles]
        for result in results[1:]:
            self.assertEqual(results[0], result)
        self.assertTrue(
            all(r == {"ok": False, "error": "invalidProtocol"} for r in results[0][:-1])
        )
        self.assertTrue(results[0][-1]["ok"])

    def test_protocol_requires_json_arrays(self):
        cases = []
        for value in [{}, "", 0, None, True]:
            for location in ["axes", "axis"]:
                request = fixture()
                request["message"]["coefficients"] = (
                    value if location == "axes" else [value, [], []]
                )
                cases.append(request)
        cases.append(fixture())
        expected = [{"ok": False, "error": "invalidProtocol"}] * (len(cases) - 1)
        for oracle in self.oracles:
            with self.subTest(backend=oracle.backend):
                results = oracle.request_many(cases)
                self.assertEqual(results[:-1], expected)
                self.assertTrue(results[-1]["ok"])

    def test_raw_number_spelling_and_quoted_text(self):
        # Dict serialization cannot preserve tokens such as 1e0 or -0.
        bad = [
            f'{{"version":3,"operation":"coefficient","coefficient":{token}}}'
            for token in ["1e0", "1E0", "1.0", "-0", "-0.0", "NaN", "Infinity"]
        ]
        bad.append('{"version":3e0,"operation":"coefficient","coefficient":1}')
        good = fixture()
        good["note"] = 'Quoted \\" and \\\\ text: 1e0, -0, 1.0'
        lines = [*bad, json.dumps(good)]
        for oracle in self.oracles:
            with self.subTest(backend=oracle.backend):
                process = subprocess.run(
                    oracle.command,
                    env=oracle.env,
                    input="\n".join(lines) + "\n",
                    text=True,
                    capture_output=True,
                    check=True,
                    timeout=30,
                )
                replies = [json.loads(line) for line in process.stdout.splitlines()]
                self.assertEqual(len(replies), len(lines))
                self.assertEqual(
                    replies[:-1], [{"ok": False, "error": "invalidProtocol"}] * len(bad)
                )
                self.assertTrue(replies[-1]["ok"])

    def test_day_shift_preserves_bits(self):
        a = fixture()
        b = deepcopy(a)
        b["message"]["day_offset"] = 16383
        b["time"] += 16383 * 86400000000
        for oracle in self.oracles:
            first, second = oracle.request_many([a, b])
            self.assertEqual(first, second)


if __name__ == "__main__":
    unittest.main()

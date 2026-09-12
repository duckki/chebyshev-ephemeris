import json
import random
import sys
import unittest

from ephemeris import Message, evaluate_exact
from ephemeris.message import WIDTHS, start_tick
from fuzz.shared.cases import decode_case, encode_case, generate
from fuzz.shared.clients import LeanOracle
from fuzz.shared.decimal import decimal_integer
from fuzz.shared.protocol import OracleError, _encode_request, _request
from fuzz.shared.protocol import exact_response as _response


class DecimalTransportTests(unittest.TestCase):
    def test_large_integer_decoding_without_global_changes(self):
        original_limit = sys.get_int_max_str_digits()
        for sign in ["", "-"]:
            encoded = sign + "1" + "0" * 6000 + "123"
            expected = 10**6003 + 123
            self.assertEqual(decimal_integer(encoded), -expected if sign else expected)
        self.assertEqual(sys.get_int_max_str_digits(), original_limit)

    def test_exact_outputs_preserve_large_denominators(self):
        axes = tuple(tuple((1 << (w - 1)) - 1 for w in WIDTHS) for _ in range(3))
        m = Message(16383, 86399, 7, axes)
        time = start_tick(m) + 1
        expected = evaluate_exact(m, time)
        self.assertGreater(expected[0].denominator, 1 << 64)
        self.assertEqual(LeanOracle().evaluate(m, time), expected)

    def test_bounded_requests_roundtrip(self):
        m = Message(65535, (1 << 32) - 1, 255, ([0] * 11, [0] * 11, [0] * 11))
        request = _request(m, (1 << 64) - 1)
        self.assertEqual(json.loads(_encode_request(request)), request)
        with self.assertRaises(ValueError):
            _request(m, 1 << 64)

    def test_protocol_integer_strings_are_strict_ascii(self):
        for text in ["+1", " 1", "1_0", "١", "1.0", "1e1", "--1", "1\n", ""]:
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    decimal_integer(text)
                with self.assertRaises(OracleError):
                    _response(json.dumps({"ok": True, "position": [[text, "1"]] * 3}))

    def test_seed_and_hex_fixture_replay(self):
        first = generate(random.Random(20260911), 0)
        second = generate(random.Random(20260911), 0)
        self.assertEqual(first, second)
        self.assertEqual(decode_case(json.loads(json.dumps(encode_case(first)))), first)


if __name__ == "__main__":
    unittest.main()

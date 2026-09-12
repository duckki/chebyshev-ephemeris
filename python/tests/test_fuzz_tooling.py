import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import ephemeris
import fuzz
from fuzz.shared.clients import FloatOracle, LeanOracle
from fuzz.shared.float_cases import fixture


class FuzzToolingTests(unittest.TestCase):
    def test_drivers_work_outside_checkout_and_report_provenance(self):
        # Copy the installed package layout without any Lean/Rust source tree.
        # This catches report generation accidentally depending on checkout paths.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            packages = root / "packages"
            for module in [ephemeris, fuzz]:
                shutil.copytree(
                    Path(module.__file__).parent,
                    packages / module.__name__,
                    ignore=shutil.ignore_patterns("__pycache__"),
                )
            env = os.environ.copy()
            env.update(
                PYTHONPATH=str(packages),
                EPHEMERIS_ORACLE=str(LeanOracle().executable),
                EPHEMERIS_FLOAT_ORACLE=FloatOracle("lean").command[0],
            )
            for driver, arguments in [
                ("rational", ["--cases", "1"]),
                ("float", ["--cases", "0", "--mode", "lean-python"]),
            ]:
                with self.subTest(driver=driver):
                    output = root / driver
                    subprocess.run(
                        [
                            sys.executable,
                            "-m",
                            f"fuzz.drivers.{driver}",
                            *arguments,
                            "--output",
                            str(output),
                        ],
                        cwd=root,
                        env=env,
                        text=True,
                        capture_output=True,
                        check=True,
                        timeout=30,
                    )
                    report = json.loads((output / "report.json").read_text())
                    self.assertIn(
                        "python/ephemeris/message.py", report["source_sha256"]
                    )
                    self.assertIn(
                        "Ephemeris/Definitions/Message.lean",
                        report["unavailable_sources"],
                    )
                    for command in report["oracle_commands"].values():
                        self.assertTrue(Path(command["argv"][0]).is_file())
                        self.assertEqual(len(command["executable_sha256"]), 64)

    def test_float_replay_records_one_replayed_request(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            replay = root / "case.json"
            replay.write_text(json.dumps({"request": fixture()}))
            subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "fuzz.drivers.float",
                    "--mode",
                    "pair",
                    "--replay",
                    str(replay),
                    "--output",
                    str(root),
                ],
                text=True,
                capture_output=True,
                check=True,
                timeout=30,
            )
            report = json.loads((root / "report.json").read_text())
            self.assertEqual(report["generated_cases"], 0)
            self.assertEqual(report["requests"], 1)
            self.assertEqual(report["replay"], str(replay))

    def test_float_limits_must_be_finite(self):
        for argument in [
            "--timeout=nan",
            "--timeout=inf",
            "--tolerance=nan",
            "--tolerance=inf",
        ]:
            with self.subTest(argument=argument):
                process = subprocess.run(
                    [sys.executable, "-m", "fuzz.drivers.float", argument],
                    text=True,
                    capture_output=True,
                    timeout=10,
                )
                self.assertEqual(process.returncode, 2)
                self.assertIn("finite nonnegative limits required", process.stderr)


if __name__ == "__main__":
    unittest.main()

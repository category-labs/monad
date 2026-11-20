# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

import io
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

from cachegrind import main as runner


class CachegrindTest(unittest.TestCase):
    def test_parse_summary_with_trailing_records(self):
        text = "events: Ir Dr\nsummary: 100 36\n\n"
        self.assertEqual(runner.parse_cachegrind_file(io.StringIO(text)), {"Ir": 100, "Dr": 36, "log": text})

    def test_inconsistent_number_of_counters(self):
        for summary in ("summary: 100", "summary: 100 12 4"):
            with self.subTest(summary=summary), self.assertRaisesRegex(ValueError, "same counters"):
                runner.parse_cachegrind_file(io.StringIO(f"events: Ir Dr\n{summary}\n"))

    def test_missing_records_and_invalid_numbers(self):
        with self.assertRaisesRegex(ValueError, "missing"):
            runner.parse_cachegrind_file(io.StringIO("summary: 1"))
        with self.assertRaisesRegex(ValueError, "non-integer"):
            runner.parse_cachegrind_file(io.StringIO("events: Ir\nsummary: invalid"))

    def test_missing_program_reports_usage(self):
        with patch.object(sys, "argv", ["cachegrind", "--"]), patch("sys.stderr", io.StringIO()) as stderr:
            with self.assertRaises(SystemExit) as error:
                runner.main()
            self.assertEqual(error.exception.code, 2)
            self.assertIn("a program to benchmark is required", stderr.getvalue())

    def test_program_separator_is_removed(self):
        for flag in ("-v", "--verbose"):
            with (
                self.subTest(flag=flag),
                patch.object(sys, "argv", ["cachegrind", flag, "--", "program", "--flag"]),
                patch.object(runner, "cachegrind", return_value={}) as run,
                patch.object(runner, "generate_report", return_value={"data": {"time_estimate": 1}}),
                patch("sys.stdout", io.StringIO()),
            ):
                runner.main()
                run.assert_called_once_with(True, [], ["program", "--flag"])

    def test_failed_subprocess_cleans_up_temporary_output(self):
        def fail(command):
            path = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("--cachegrind-out-file=")))
            self.assertTrue(path.is_file())
            paths.append(path)
            raise OSError("benchmark failed")

        paths = []
        with patch.object(runner, "check_call", side_effect=fail):
            with self.assertRaisesRegex(OSError, "benchmark failed"):
                runner.cachegrind(False, [], ["program"])
        self.assertFalse(paths[0].exists())

    def test_unavailable_git_metadata_does_not_abort_report(self):
        with patch.object(runner, "check_output", side_effect=OSError):
            self.assertEqual(runner.git_rev(), "unknown")

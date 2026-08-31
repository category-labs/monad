"""Run with python3 -m unittest discover -s zkvm/zisk -p 'test_audit_*.py'."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "audit_official_build", Path(__file__).with_name("audit-official-build.py")
)
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


def valid_flags() -> str:
    return " ".join(
        (
            *audit.REQUIRED_FLAGS,
            f"-march={audit.EXPECTED_MARCH}",
            f"-mtune={audit.EXPECTED_MTUNE}",
        )
    )


class FlagTests(unittest.TestCase):
    def test_current_flags_and_quoted_paths(self):
        audit.check_flags(
            valid_flags() + ' -include "/path with spaces/nodelete.hpp"', "test"
        )

    def test_both_parameter_spellings(self):
        audit.check_flags(valid_flags().replace("--param=", "--param "), "test")

    def test_each_required_flag_is_required(self):
        for flag in audit.REQUIRED_FLAGS:
            with self.subTest(flag=flag), self.assertRaises(SystemExit):
                audit.check_flags(valid_flags().replace(flag, ""), "test")

    def test_later_parameter_wins_with_either_spelling(self):
        for flag in audit.REQUIRED_FLAGS:
            if not flag.startswith("--param="):
                continue
            wrong = flag.rsplit("=", 1)[0] + "=9999"
            for spelling in [wrong, wrong.replace("--param=", "--param ")]:
                with self.subTest(flag=spelling):
                    with self.assertRaises(SystemExit):
                        audit.check_flags(valid_flags() + " " + spelling, "test")
                    audit.check_flags(spelling + " " + valid_flags(), "test")

    def test_later_codegen_overrides_are_rejected(self):
        for override in [
            "-O2", "-Os", "-march=rv64ima", "-mtune=generic-ooo", "-mabi=ilp32",
            "-fpic", "-fPIC", "-fno-unroll-loops",
            "-fno-inline-functions", "-mno-zisk-dma",
        ]:
            with self.subTest(override=override):
                with self.assertRaises(SystemExit):
                    audit.check_flags(valid_flags() + " " + override, "test")
                audit.check_flags(override + " " + valid_flags(), "test")

    def test_flags_make_uses_only_cxx_flags(self):
        audit.check_flags(
            "# -O0\nCXX_FLAGS = " + valid_flags() + "\nC_FLAGS = -O0\n", "test"
        )
        with self.assertRaises(SystemExit):
            audit.check_flags("C_FLAGS = " + valid_flags(), "test")
        with self.assertRaises(SystemExit):
            audit.check_flags(
                "C_FLAGS = " + valid_flags() + "\nCXX_FLAGS = -O0\n", "test"
            )

    def test_malformed_parameters_and_quotes_fail(self):
        for tail in ["--param", "--param name", "--param==1", "--param=name=", '"']:
            with self.subTest(tail=tail), self.assertRaises(SystemExit):
                audit.check_flags(valid_flags() + " " + tail, "test")


if __name__ == "__main__":
    unittest.main()

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

import argparse
import contextlib
import io
import json
import pathlib
import tempfile
import unittest

from benchmark_results import load_timings
from compare_benchmarks.main import compute_ratio, load_json_results, loader, relabel_for_printing
from compare_implementations.main import compute_speedup, load_results


def benchmark(name, time=1, unit="ns", **extra):
    return {"name": name, "real_time": time, "cpu_time": time, "time_unit": unit, **extra}


class ComparisonTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = pathlib.Path(temp.name)

    def report(self, name, *rows):
        path = self.root / name
        path.write_text(json.dumps({"benchmarks": rows}))
        return path

    def compare(self, before, after, *, aggregate=False, kind="run"):
        args = argparse.Namespace(aggregate=aggregate, type=kind, implementation="compiler")
        return compute_ratio(load_json_results(loader(args), before, after))

    def test_units_and_iterations(self):
        before = self.report("base", benchmark("execute/a/compiler", 2, "us"), benchmark("execute/a/compiler", 4, "us"))
        after = self.report("new", benchmark("execute/a/compiler", 1500))
        result = self.compare(before, after)
        self.assertEqual(result.loc["execute/a", "change"], 2)
        self.assertEqual(relabel_for_printing(result).loc["`execute/a`", "Before (ns)"], 3000)

    def test_aggregate_metadata_selects_mean_and_resolves_run_name(self):
        def entry(name, amount, aggregate):
            return benchmark(
                name, amount, run_name="execute/a/compiler/repeats:5", run_type="aggregate", aggregate_name=aggregate
            )

        before = self.report(
            "base",
            entry("execute/a/compiler/repeats:5_mean", 4, "mean"),
            entry("execute/a/compiler/repeats:5_median", 99, "median"),
        )
        after = self.report("new", entry("execute/a/compiler/repeats:5_mean", 2, "mean"))
        self.assertEqual(self.compare(before, after, aggregate=True).loc["execute/a", "change"], 2)

    def test_skips_failed_runs_and_reports_unmatched_pairs(self):
        before = self.report(
            "base",
            benchmark("execute/a/compiler", 10),
            benchmark("execute/old/compiler"),
            {"name": "execute/failed/compiler", "error_occurred": True},
        )
        after = self.report("new", benchmark("execute/a/compiler", 5))
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            result = self.compare(before, after)
        self.assertEqual(result.index.to_list(), ["execute/a"])
        self.assertIn("Excluded 1 benchmark", stderr.getvalue())

    def test_no_matching_or_empty_data(self):
        before = self.report("base", benchmark("execute/a/compiler"))
        with self.assertRaisesRegex(ValueError, "No matching benchmarks"):
            self.compare(before, self.report("new", benchmark("execute/b/compiler")))
        with self.assertRaisesRegex(ValueError, "No benchmark data"):
            self.compare(before, self.report("empty"))

    def test_reports_invalid_timing(self):
        for row in (benchmark("compile/a", 0), benchmark("compile/a", 1, "ticks")):
            with self.subTest(row=row), self.assertRaisesRegex(ValueError, "compile/a"):
                load_timings(self.report("bad", row), "real_time", aggregate=False, prefix="compile/")

    def test_compile_names_and_no_aggregate_in_raw_mode(self):
        before = self.report("base", benchmark("compile/a", 20), benchmark("compile/a_mean", 99))
        after = self.report("new", benchmark("compile/a", 10))
        self.assertEqual(self.compare(before, after, kind="compile").loc["a", "change"], 2)

    def test_implementation_cutoff_is_in_nanoseconds(self):
        path = self.report(
            "all",
            benchmark("execute/a/interpreter_mean", 4, "us"),
            benchmark("execute/a/compiler_mean", 2, "us"),
            benchmark("execute/a/unrelated_mean", 9, "us"),
        )
        data = load_results(path)
        result = compute_speedup(data, "interpreter", "compiler", cutoff=1500)
        self.assertEqual(result.loc["a", "speedup"], 2)
        with self.assertRaisesRegex(ValueError, "minimum time"):
            compute_speedup(data, "interpreter", "compiler", cutoff=2100)


if __name__ == "__main__":
    unittest.main()

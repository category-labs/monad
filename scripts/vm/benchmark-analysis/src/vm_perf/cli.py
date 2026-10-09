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
import json
import pathlib
import sys

from vm_perf.compare import diff
from vm_perf.suites import CORE, measure_build


def main() -> None:
    parser = argparse.ArgumentParser(prog="vm-perf", description="Deterministic VM performance measurements")
    sub = parser.add_subparsers(dest="command", required=True)

    m = sub.add_parser("measure", help="Measure one build directory")
    m.add_argument("build", type=pathlib.Path)
    m.add_argument("-o", "--output", type=pathlib.Path, required=True)
    m.add_argument("--cases", type=pathlib.Path, required=True, help="Micro benchmark case list, created if missing")
    m.add_argument("--micro", default=CORE, help="Regex selecting micro benchmarks")

    c = sub.add_parser("compare", help="Compare two reports")
    c.add_argument("before", type=pathlib.Path)
    c.add_argument("after", type=pathlib.Path)
    c.add_argument("--threshold", type=float, default=0.1, help="Ignore changes below this percentage")
    c.add_argument("--top", type=int, default=5, help="Functions to report per change")
    args = parser.parse_args()

    if args.command == "measure":
        args.output.write_text(json.dumps(measure_build(args.build, args.cases, args.micro), indent=1))
        return
    before, after = json.loads(args.before.read_text()), json.loads(args.after.read_text())
    if unmatched := sorted(before.keys() ^ after.keys()):
        print(f"Only in one report: {', '.join(unmatched)}", file=sys.stderr)
    changes = diff(before, after, args.threshold, args.top)
    print(json.dumps(changes, indent=2))
    sys.exit(1 if any(c["after"] > c["before"] for c in changes) else 0)

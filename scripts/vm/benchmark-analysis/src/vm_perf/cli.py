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
import re
import sys
from typing import Any

from vm_perf.commits import VM_PATHS, git, history_plot, measure_commit
from vm_perf.compare import diff, slower, summary
from vm_perf.suites import CORE, MICRO, measure_build, micro_name
from vm_perf.timing import time_pair


def add_timing(args: argparse.Namespace, base: str, head: str, changes: list[dict[str, Any]]) -> None:
    changed = {c["benchmark"] for c in changes if c["benchmark"].startswith("micro/")}
    cases_file = args.cases or args.output / "cases.json"
    cases = [(c[0], c[1], c[2]) for c in json.loads(cases_file.read_text())]
    cases = [c for c in cases if micro_name(c) in changed]
    binaries = [args.output / "bin" / sha / pathlib.Path(MICRO).name for sha in (base, head)]
    timing = time_pair(binaries[0], binaries[1], cases, args.repeats, args.core)
    for change in changes:
        if timed := timing.get(change["benchmark"]):
            change["time"] = timed
            change["time_disagrees"] = timed["significant"] and slower(change) != (change["after"] > change["before"])


def main() -> None:
    parser = argparse.ArgumentParser(prog="vm-perf", description="Deterministic VM performance measurements")
    sub = parser.add_subparsers(dest="command", required=True)

    m = sub.add_parser("measure", help="Measure one build directory")
    m.add_argument("build", type=pathlib.Path)
    m.add_argument("-o", "--output", type=pathlib.Path, required=True)
    m.add_argument("--cases", type=pathlib.Path, required=True, help="Micro benchmark case list, created if missing")

    t = sub.add_parser("time", help="Time micro benchmarks natively, base and head interleaved")
    t.add_argument("base", type=pathlib.Path, help="Base vm-micro-benchmarks binary")
    t.add_argument("head", type=pathlib.Path, help="Head vm-micro-benchmarks binary")
    t.add_argument("--cases", type=pathlib.Path, required=True, help="Micro benchmark case list")
    t.add_argument("--repeats", type=int, default=5)
    t.add_argument("--core", type=int, default=7, help="CPU to pin to")

    c = sub.add_parser("compare", help="Compare two reports")
    c.add_argument("before", type=pathlib.Path)
    c.add_argument("after", type=pathlib.Path)

    for name, help in [
        ("impact", "Measure two commits and compare them"),
        ("history", "Measure every commit in a range"),
        ("validate", "Check that known changes are detected"),
    ]:
        s = sub.add_parser(name, help=help)
        s.add_argument("--source", type=pathlib.Path, required=True, help="Spare worktree with submodules")
        s.add_argument("--build", type=pathlib.Path, required=True, help="Build directory it owns")
        s.add_argument("-o", "--output", type=pathlib.Path, required=True, help="Directory for cached reports")
        s.add_argument("--cases", type=pathlib.Path, help="Micro benchmark case list to share across runs")
    sub.choices["impact"].add_argument("base", nargs="?", default="origin/main")
    sub.choices["impact"].add_argument("head", nargs="?", default="HEAD")
    for name in ("impact", "validate"):
        sub.choices[name].add_argument("--timing", action="store_true", help="Also time changed micro benchmarks")
        sub.choices[name].add_argument("--repeats", type=int, default=7, help="Timing rounds")
        sub.choices[name].add_argument("--core", type=int, default=7, help="CPU to pin timing to")
    sub.choices["history"].add_argument("revisions")
    sub.choices["history"].add_argument("paths", nargs="*", default=VM_PATHS)
    sub.choices["validate"].add_argument("truth", type=pathlib.Path)
    for s in sub.choices.values():
        s.add_argument("--micro", default=CORE, help="Regex selecting micro benchmarks")
        s.add_argument("--threshold", type=float, default=0.1, help="Ignore changes below this percentage")
        s.add_argument("--top", type=int, default=5, help="Functions to report per change")
    args = parser.parse_args()

    if args.command == "measure":
        args.output.write_text(json.dumps(measure_build(args.build, args.cases, args.micro), indent=1))
        return
    if args.command == "time":
        cases = [
            (c[0], c[1], c[2])
            for c in json.loads(args.cases.read_text())
            if re.search(args.micro, micro_name((c[0], c[1], c[2])))
        ]
        print(json.dumps(time_pair(args.base, args.head, cases, args.repeats, args.core), indent=1))
        return
    if args.command == "compare":
        before, after = json.loads(args.before.read_text()), json.loads(args.after.read_text())
        if unmatched := sorted(before.keys() ^ after.keys()):
            print(f"Only in one report: {', '.join(unmatched)}", file=sys.stderr)
        changes = diff(before, after, args.threshold, args.top)
        print(json.dumps(changes, indent=2))
        sys.exit(1 if any(c["after"] > c["before"] for c in changes) else 0)

    args.output.mkdir(parents=True, exist_ok=True)
    here = pathlib.Path.cwd()
    if args.command == "impact":
        base, head = (git(here, "rev-parse", r).strip() for r in (args.base, args.head))
        before, after = measure_commit(args, base), measure_commit(args, head)
        if not before or not after:
            print(f"{base[:9] if not before else head[:9]} was not measured", file=sys.stderr)
            sys.exit(2)
        changes = diff(before, after, args.threshold, args.top)
        if args.timing:
            add_timing(args, base, head, changes)
        (args.output / f"impact-{base[:9]}-{head[:9]}.md").write_text(summary(changes) + "\n")
        print(json.dumps(changes, indent=2))
        sys.exit(1 if any(slower(c) for c in changes) else 0)
    if args.command == "history":
        log = ["log", "--first-parent", "--reverse", "--format=%H %cs %s", args.revisions, "--", *args.paths]
        commits = [line.split(" ", 2) for line in git(here, *log).splitlines()]
        measured = [(c, r) for c in commits if (r := measure_commit(args, c[0]))]
        steps = [
            {"since": p[0], "commit": c[0], "subject": c[2], "changes": changes}
            for (p, before), (c, after) in zip(measured, measured[1:])
            if (changes := diff(before, after, args.threshold, args.top))
        ]
        print(json.dumps(steps, indent=2))
        if measured:
            names = sorted(set.intersection(*(set(r) for _, r in measured)))
            html = history_plot([c for c, _ in measured], [r for _, r in measured], names)
            (args.output / "index.html").write_text(html)
        return

    rows = []
    for entry in json.loads(args.truth.read_text()):
        commit = git(here, "rev-parse", entry["commit"]).strip()
        parent = git(here, "rev-parse", entry.get("base", f"{commit}^1")).strip()
        before, after = measure_commit(args, parent), measure_commit(args, commit)
        changes = diff(before, after, args.threshold, args.top) if before and after else []
        if changes and args.timing:
            add_timing(args, parent, commit, changes)
        (args.output / f"validate-{parent[:9]}-{commit[:9]}.json").write_text(json.dumps(changes, indent=1))
        hits = [c for c in changes if re.search(entry["expect"], c["benchmark"])]
        worse = sum(slower(c) for c in hits)
        better = len(hits) - worse
        if not before or not after:
            verdict = "not measured"
        elif entry["direction"] == "none":
            verdict = "pass" if not changes else f"{len(changes)} unexpected changes"
        elif entry["direction"] == "any":
            verdict = f"{better} faster, {worse} slower"
        else:
            right = better if entry["direction"] == "faster" else worse
            verdict = f"pass ({right} benchmarks)" if right else "missed"
        best = max(hits, key=lambda c: abs(c["change_percent"]), default=None)
        rows.append(
            {
                "commit": f"{parent[:9]}..{commit[:9]}",
                "note": entry.get("note", ""),
                "direction": entry["direction"],
                "verdict": verdict,
                "largest": f"{best['change_percent']:+.2f}% {best['benchmark']}" if best else "",
                "other_changes": len(changes) - len(hits),
            }
        )
    print(json.dumps(rows, indent=2))
    failed = ("not measured", "missed", "unexpected")
    sys.exit(1 if any(any(f in row["verdict"] for f in failed) for row in rows) else 0)

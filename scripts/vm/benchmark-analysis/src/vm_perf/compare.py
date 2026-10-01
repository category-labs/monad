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

import re
from typing import Any

from vm_perf.suites import Report

NOISY = re.compile(r"/(BASIC_TERN_MATH|EXP), random input")


def cost(result: Report) -> int:
    return int(result["total"] + result.get("baseline", 0))


def diff(before: Report, after: Report, threshold: float, top: int) -> list[dict[str, Any]]:
    changes = []
    for name in sorted(before.keys() & after.keys()):
        b, a = before[name], after[name]
        percent = 100 * (cost(a) - cost(b)) / max(cost(b), 1)
        if abs(percent) < (max(threshold, 1.0) if NOISY.search(name) else threshold):
            continue
        deltas = {f: a["functions"].get(f, 0) - b["functions"].get(f, 0) for f in b["functions"] | a["functions"]}
        functions = sorted((f for f in deltas if deltas[f]), key=lambda f: -abs(deltas[f]))[:top]
        change = {"benchmark": name, "before": cost(b), "after": cost(a), "change_percent": round(percent, 2)}
        if "baseline" in b:
            change["sequence_before"], change["sequence_after"] = b["total"], a["total"]
        changes.append(change | {"functions": [{"function": f, "delta": deltas[f]} for f in functions]})
    return sorted(changes, key=lambda c: -c["change_percent"])


def summary(changes: list[dict[str, Any]], limit: int = 8) -> str:
    groups: dict[str, list[dict[str, Any]]] = {}
    for c in changes:
        kind = (
            c["benchmark"].split("/")[0]
            if c["benchmark"].startswith("compile/")
            else "/".join(c["benchmark"].split("/")[:2])
        )
        groups.setdefault(kind, []).append(c)
    titles = {"compile": "Compile time", "micro/compiler": "Compiled code", "micro/interpreter": "Interpreter"}
    lines = []
    for kind in ["compile", "micro/compiler", "micro/interpreter"]:
        rows = groups.get(kind, [])
        slower, faster = sum(c["after"] > c["before"] for c in rows), sum(c["after"] < c["before"] for c in rows)
        lines.append(f"## {titles[kind]}: {slower} slower, {faster} faster")
        for c in sorted(rows, key=lambda c: -abs(c["change_percent"]))[:limit]:
            name = c["benchmark"].split("/", 2)[-1] if kind != "compile" else c["benchmark"]
            top = c["functions"][0]["function"][:80] if c["functions"] else ""
            time = ""
            if t := c.get("time"):
                time = f", time {t['change_percent']:+.1f}%" + ("" if t["significant"] else " (noise)")
                time += " **disagrees**" if c.get("time_disagrees") else ""
            lines.append(f"- {c['change_percent']:+.2f}% instructions{time} `{name}` ({top})")
    return "\n".join(lines)

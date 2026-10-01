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

import pathlib
import re
import subprocess
from typing import Any

from vm_perf.suites import Case, micro_name, parse_results, tool


def run_titles(binary: pathlib.Path, titles: list[tuple[str, str]], core: int) -> dict[str, float]:
    best = {}
    for impl, title in titles:
        cmd = [tool("taskset"), "-c", str(core), str(binary), "--impl-filter", f"^{impl}$"]
        cmd += ["--title-filter", f"^{re.escape(title)}$"]
        for _, _, seq, ms in parse_results(subprocess.run(cmd, capture_output=True, text=True).stdout):
            best[micro_name((impl, title, seq))] = ms * 1e6
    return best


def time_pair(base: pathlib.Path, head: pathlib.Path, cases: list[Case], repeats: int, core: int) -> dict[str, Any]:
    titles = sorted({(impl, title) for impl, title, _ in cases})
    samples: dict[str, dict[str, list[float]]] = {"base": {}, "head": {}}
    for _ in range(repeats):
        for label, binary in (("base", base), ("head", head)):
            for name, ns in run_titles(binary, titles, core).items():
                samples[label].setdefault(name, []).append(ns)
    result = {}
    for name in sorted(samples["base"].keys() & samples["head"].keys()):
        b, h = samples["base"][name], samples["head"][name]
        spread = max((max(s) - min(s)) / min(s) for s in (b, h))
        change = 100 * (min(h) - min(b)) / min(b)
        result[name] = {
            "base_ns": round(min(b), 1),
            "head_ns": round(min(h), 1),
            "change_percent": round(change, 2),
            "noise_percent": round(100 * spread, 2),
            "significant": abs(change) > max(1.0, 200 * spread),
        }
    return result

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

import json
import math
import re
import sys
from pathlib import Path

import pandas as pd

NANOSECONDS = {"ns": 1, "us": 1_000, "ms": 1_000_000, "s": 1_000_000_000}


def load_timings(path: Path, metric: str, *, aggregate: bool, prefix: str) -> pd.DataFrame:
    with path.open(encoding="utf-8") as file:
        report = json.load(file)

    rows = []
    for record in report["benchmarks"]:
        name = record["name"]
        if not name.startswith(prefix) or record.get("error_occurred"):
            continue
        if "run_type" in record:
            is_aggregate = record["run_type"] == "aggregate"
            is_mean = is_aggregate and record.get("aggregate_name") == "mean"
        else:
            is_mean = name.endswith("_mean")
            is_aggregate = name.endswith(("_mean", "_median", "_stddev", "_cv"))
        if (aggregate and not is_mean) or (not aggregate and is_aggregate):
            continue

        run_name = record.get("run_name", name.removesuffix("_mean") if is_mean else name)
        run_name = re.sub(r"/repeats:[0-9]+$", "", run_name)
        unit = record.get("time_unit")
        if unit not in NANOSECONDS:
            raise ValueError(f"{path}: {name}: unsupported time unit {unit!r}")
        elapsed = record.get(metric)
        if (
            isinstance(elapsed, bool)
            or not isinstance(elapsed, (int, float))
            or not math.isfinite(elapsed)
            or elapsed <= 0
        ):
            raise ValueError(f"{path}: {name}: {metric} must be finite and positive")
        rows.append((run_name, elapsed * NANOSECONDS[unit]))

    return pd.DataFrame(rows, columns=["name", metric])


def split_implementations(df: pd.DataFrame) -> pd.DataFrame:
    rows = df["name"].str.rsplit("/", n=1)
    return df.assign(name=rows.str[0], implementation=rows.str[1])


def select_pairs(table: pd.DataFrame, baseline: str, candidate: str) -> pd.DataFrame:
    if baseline == candidate:
        raise ValueError("Choose two different comparison columns")
    if baseline not in table or candidate not in table:
        raise ValueError(f"No benchmark data for both {baseline!r} and {candidate!r}")

    pairs = table[[baseline, candidate]].dropna()
    if pairs.empty:
        raise ValueError(f"No matching benchmarks for {baseline!r} and {candidate!r}")
    unmatched = len(table[[baseline, candidate]].dropna(how="all")) - len(pairs)
    if unmatched:
        print(f"Excluded {unmatched} benchmark(s) missing one comparison result.", file=sys.stderr)
    return pairs

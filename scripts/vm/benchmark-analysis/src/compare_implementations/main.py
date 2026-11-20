# Copyright (C) 2025 Category Labs, Inc.
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
import pathlib

import pandas as pd
from scipy.stats import gmean

from benchmark_results import load_timings, select_pairs, split_implementations


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="compare-implementations",
        description="Compare benchmark results across implementations",
    )

    parser.add_argument(
        "filename",
        type=pathlib.Path,
        help="Google Benchmark JSON output",
    )

    parser.add_argument(
        "a_impl",
        type=str,
        help="Baseline implementation",
    )

    parser.add_argument(
        "b_impl",
        type=str,
        help="Secondary implementation",
    )

    parser.add_argument(
        "-m",
        "--min",
        dest="cutoff",
        type=int,
        required=False,
        default=0,
        help="Minimum time (ns) to consider",
    )

    return parser.parse_args()


def load_results(
    filename: pathlib.Path,
) -> pd.DataFrame:
    df = split_implementations(load_timings(filename, "cpu_time", aggregate=True, prefix="execute/"))
    return df.assign(name=df.name.str.removeprefix("execute/"))


def compute_speedup(
    df: pd.DataFrame,
    a_impl: str,
    b_impl: str,
    *,
    cutoff: int = 0,
) -> pd.DataFrame:
    values = df.pivot_table(index="name", columns="implementation", values="cpu_time", aggfunc="mean")
    pairs = select_pairs(values, a_impl, b_impl)
    pairs = pairs[pairs[b_impl] >= cutoff]
    if pairs.empty:
        raise ValueError("No paired benchmarks meet the minimum time")
    return pairs.assign(speedup=pairs[a_impl] / pairs[b_impl])


def main() -> None:
    args = parse_args()
    try:
        df = compute_speedup(load_results(args.filename), args.a_impl, args.b_impl, cutoff=args.cutoff)
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit(str(error)) from None
    print(df.to_markdown())
    print(f"Geomean: {gmean(df['speedup'])}")

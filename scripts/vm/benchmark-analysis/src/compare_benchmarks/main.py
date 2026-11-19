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
from collections.abc import Callable

import pandas as pd
import scipy.stats

from benchmark_results import load_timings, select_pairs, split_implementations


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="compare_benchmarks",
        description="Compare compiler benchmark results",
    )

    parser.add_argument(
        "--before",
        type=pathlib.Path,
        required=True,
        help="Old benchmark results (before PR applied)",
    )
    parser.add_argument(
        "--after",
        type=pathlib.Path,
        required=True,
        help="New benchmark results (after PR applied)",
    )

    parser.add_argument(
        "-i",
        "--implementation",
        type=str,
        required=False,
        default="compiler",
        help="Implementation to compare",
    )

    parser.add_argument(
        "-a",
        "--aggregate",
        required=False,
        default=False,
        help="Report from aggregate stats",
        action="store_true",
    )

    parser.add_argument(
        "--type",
        choices=["run", "compile"],
        required=True,
        help="Which set of benchmark data to compare",
    )

    return parser.parse_args()


def load_single_runtime_results(
    args: argparse.Namespace,
) -> Callable[[pathlib.Path, str], pd.DataFrame]:
    def _curried(path: pathlib.Path, label: str) -> pd.DataFrame:
        df = split_implementations(load_timings(path, "real_time", aggregate=args.aggregate, prefix="execute/"))
        return df[df.implementation == args.implementation].assign(version=label)

    return _curried


def load_single_compile_results(
    args: argparse.Namespace,
) -> Callable[[pathlib.Path, str], pd.DataFrame]:
    def _curried(path: pathlib.Path, label: str) -> pd.DataFrame:
        df = load_timings(path, "real_time", aggregate=args.aggregate, prefix="compile/")
        return df.assign(name=df.name.str.removeprefix("compile/"), version=label)

    return _curried


def load_json_results(
    loader: Callable[[pathlib.Path, str], pd.DataFrame],
    before: pathlib.Path,
    after: pathlib.Path,
) -> pd.DataFrame:
    return pd.concat([loader(before, "before"), loader(after, "after")], ignore_index=True)


def compute_ratio(df: pd.DataFrame) -> pd.DataFrame:
    values = df.pivot_table(index="name", columns="version", values="real_time", aggfunc="mean")
    pairs = select_pairs(values, "before", "after")
    return pairs.assign(change=pairs["before"] / pairs["after"])


def relabel_for_printing(df: pd.DataFrame) -> pd.DataFrame:
    result = df.rename(columns={"before": "Before (ns)", "after": "After (ns)", "change": "Change (×)"})
    return result.rename(index=lambda name: f"`{name}`").rename_axis("Benchmark")


def to_markdown_with_stats(df: pd.DataFrame) -> str:
    main_table = df.to_markdown()

    geomean = scipy.stats.gmean(df["Change (×)"])
    geomean_row = f"| **Geometric Mean** | | | **{geomean:.6g}** |"
    return f"{main_table}\n{geomean_row}"


def loader(args: argparse.Namespace) -> Callable[[pathlib.Path, str], pd.DataFrame]:
    if args.type == "run":
        return load_single_runtime_results(args)
    elif args.type == "compile":
        return load_single_compile_results(args)
    else:
        raise ValueError


def main() -> None:
    args = parse_args()

    try:
        df = compute_ratio(load_json_results(loader(args), args.before, args.after))
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit(str(error)) from None
    df = relabel_for_printing(df)
    print(to_markdown_with_stats(df))


if __name__ == "__main__":
    main()

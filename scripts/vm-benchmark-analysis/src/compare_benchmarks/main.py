import argparse
import json
import pathlib
from collections.abc import Callable

import pandas as pd
import scipy.stats


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
    def _split_benchmark_impl(row: pd.Series) -> tuple[str, str]:
        parts = row["name"].split("/")
        return ("/".join(parts[:-1]), parts[-1])

    def _curried(path: pathlib.Path, label: str) -> pd.DataFrame:
        with open(path, "r") as f:
            json_data = json.load(f)

        df = pd.json_normalize(json_data["benchmarks"])

        if args.aggregate:
            df = df[df.name.str.endswith("_mean")]
            df.name = df.name.str.removesuffix("_mean")

        df["version"] = label
        df[["name", "implementation"]] = df.apply(_split_benchmark_impl, axis="columns", result_type="expand")
        df = df[df.implementation == args.implementation]

        return df

    return _curried


def load_single_compile_results(
    args: argparse.Namespace,
) -> Callable[[pathlib.Path, str], pd.DataFrame]:
    def _compile_benchmark(row: pd.Series) -> str:
        parts = row["name"].split("/")
        return parts[1]

    def _curried(path: pathlib.Path, label: str) -> pd.DataFrame:
        with open(path, "r") as f:
            json_data = json.load(f)

        df = pd.json_normalize(json_data["benchmarks"])

        df = df[~df.name.str.startswith("complexity")]

        if args.aggregate:
            df = df[df.name.str.endswith("mean")]
            df.name = df.name.str.removesuffix("_mean")

        df["version"] = label
        df["name"] = df.apply(_compile_benchmark, axis="columns", result_type="expand")

        return df

    return _curried


def load_json_results(
    loader: Callable[[pathlib.Path, str], pd.DataFrame],
    before: pathlib.Path,
    after: pathlib.Path,
) -> pd.DataFrame:
    df = pd.concat(
        [
            loader(before, "before"),
            loader(after, "after"),
        ]
    ).reset_index(drop=True)
    assert len(set(df.time_unit.tolist())) == 1
    return df


def compute_ratio(df: pd.DataFrame) -> pd.DataFrame:
    df = df[["name", "version", "real_time", "time_unit"]].pivot(index="name", columns=["version"])
    df["change"] = df["real_time"]["before"] / df["real_time"]["after"]
    return df


def relabel_for_printing(df: pd.DataFrame) -> pd.DataFrame:
    df["Before (ns)"] = df["real_time"]["before"]
    df["After (ns)"] = df["real_time"]["after"]
    df["Change (×)"] = df["change"]

    cols = pd.Index(["Before (ns)", "After (ns)", "Change (×)"])
    df = df[cols]
    df.columns = cols
    df.index = pd.Index(map(lambda s: f"`{s}`", df.index.tolist()))
    df.index.names = ["Benchmark"]

    return df


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

    df = load_json_results(loader(args), args.before, args.after)
    df = compute_ratio(df)
    df = relabel_for_printing(df)
    print(to_markdown_with_stats(df))


if __name__ == "__main__":
    main()

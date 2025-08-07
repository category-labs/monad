import argparse
import json
import pathlib

import pandas as pd
from scipy.stats import gmean


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
    def _split_benchmark_impl(row: pd.Series) -> tuple[str, str]:
        parts = row["name"].split("/")
        return ("/".join(parts[:-1]), parts[-1])

    with open(filename, "r") as f:
        json_data = json.load(f)

    df = pd.json_normalize(json_data["benchmarks"])

    df = df[df.name.str.endswith("_mean")]
    df.name = df.name.str.removesuffix("_mean")
    df.name = df.name.str.removeprefix("execute/")
    df[["name", "implementation"]] = df.apply(_split_benchmark_impl, axis="columns", result_type="expand")

    return df


def compute_speedup(
    df: pd.DataFrame,
    a_impl: str,
    b_impl: str,
    *,
    cutoff: int = 0,
) -> pd.DataFrame:
    df = df.pivot(index="name", columns="implementation", values="cpu_time")
    df["speedup"] = df[a_impl] / df[b_impl]
    df = df[df[b_impl] >= cutoff]

    cols = pd.Index([a_impl, b_impl, "speedup"])
    df = df[cols]
    df.columns = cols

    return df


def main() -> None:
    args = parse_args()
    df = load_results(args.filename)
    df = compute_speedup(df, args.a_impl, args.b_impl, cutoff=args.cutoff)
    print(df.to_markdown())
    print(f"Geomean: {gmean(df['speedup'])}")

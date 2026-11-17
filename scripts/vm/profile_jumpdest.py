#!/usr/bin/env python3
"""Compare saved execution-benchmarks binaries on a pinned CPU.

Example:
  python3 scripts/vm/profile_jumpdest.py --binary baseline=/tmp/baseline \
      --binary candidate=/tmp/candidate --output build/jumpdest-profile/compare

Build with Release, AVX2, MONAD_COMPILER_TESTING=OFF and
MONAD_COMPILER_BENCHMARKS=ON. Copy each binary before rebuilding its successor.
Run without concurrent builds/proofs. This script never edits or builds code.
"""

import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", action="append", required=True, metavar="LABEL=PATH")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--min-time", default="0.1s")
    parser.add_argument("--filter", default="jumpdest_scan")
    args = parser.parse_args()
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is not in the current affinity set")
    if args.rounds < 1 or args.repetitions < 1:
        parser.error("rounds and repetitions must be positive")
    binaries = {}
    for item in args.binary:
        label, sep, filename = item.partition("=")
        if not sep or not label or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-" for c in label):
            parser.error("use LABEL=PATH with an alphanumeric, underscore or hyphen label")
        if label in binaries:
            parser.error(f"duplicate label: {label}")
        path = Path(filename).resolve(strict=True)
        binaries[label] = path
    # Refuse to overwrite measurements from an earlier experiment.
    args.output.mkdir(parents=True, exist_ok=False)
    metadata = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "cpuinfo": Path("/proc/cpuinfo").read_text(),
        "cpu": args.cpu,
        "rounds": args.rounds,
        "repetitions": args.repetitions,
        "min_time": args.min_time,
        "filter": args.filter,
        "ld_library_path": os.environ.get("LD_LIBRARY_PATH", ""),
        "binaries": {label: {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                     for label, path in binaries.items()},
        "commands": [],
    }
    for label, path in binaries.items():
        metadata["binaries"][label]["libraries"] = subprocess.check_output(
            ["ldd", str(path)], text=True)
    results = {label: {} for label in binaries}
    rng = random.Random(0xC0FFEE)
    for round_index in range(args.rounds):
        order = list(binaries)
        rng.shuffle(order)
        for label in order:
            output = (args.output / f"{round_index:02d}-{label}.json").resolve()
            command = ["taskset", "-c", str(args.cpu), str(binaries[label]),
                       f"--benchmark_filter={args.filter}",
                       f"--benchmark_min_time={args.min_time}",
                       "--benchmark_min_warmup_time=0.05",
                       f"--benchmark_repetitions={args.repetitions}",
                       "--benchmark_enable_random_interleaving=true",
                       "--benchmark_display_aggregates_only=true",
                       f"--benchmark_out={output}", "--benchmark_out_format=json"]
            metadata["commands"].append(command)
            (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
            print(f"Round {round_index + 1}/{args.rounds}: {label}", flush=True)
            with output.with_suffix(".log").open("w") as log:
                subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
            runs = json.loads(output.read_text())["benchmarks"]
            samples = {}
            for run in runs:
                if run.get("error_occurred"):
                    raise RuntimeError(run.get("error_message", str(run)))
                if run.get("run_type", "iteration") != "iteration":
                    continue
                factor = {"ns": 1, "us": 1000, "ms": 1000000, "s": 1000000000}[run["time_unit"]]
                samples.setdefault(run["name"], []).append(run["cpu_time"] * factor)
            if not samples:
                raise RuntimeError(f"No benchmark iterations matched; see {output.with_suffix('.log')}")
            for name, values in samples.items():
                results[label].setdefault(name, []).append(statistics.median(values))
    names = set(results[next(iter(binaries))])
    if any(set(rows) != names for rows in results.values()):
        raise RuntimeError("Binaries ran different benchmark sets")
    reference = next(iter(binaries))
    with (args.output / "summary.csv").open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(["benchmark", "binary", "median_cpu_ns", "min_round_ns", "max_round_ns", "speedup_vs_first"])
        for name in sorted(names):
            baseline = statistics.median(results[reference][name])
            for label in binaries:
                rounds = results[label][name]
                median = statistics.median(rounds)
                writer.writerow([name, label, median, min(rounds), max(rounds), baseline / median])
                print(f"{name:40s} {label:20s} {median:12.1f} ns  {baseline / median:6.3f}x")
    (args.output / "round-medians.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()

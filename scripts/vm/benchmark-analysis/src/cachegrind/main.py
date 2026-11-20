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

#!/usr/bin/env python3
"""
## Synopsis

This program benchmarks a given program using cachegrind to generate low-noise measurements.

usage: cachegrind.py [-h] [--config FILE] [-o FILE] [-v,--verbose] ...

Cachegrind benchmark runner

positional arguments:
  program        Program to benchmark along with its arguments

options:
  -h, --help     show this help message and exit
  --config FILE  Cache details config
  -o FILE        Save the full report to this file; otherwise print the estimated time
  -v,--verbose   Toggle verbose output

## Acknowledgements

Based on Itamar Turner-Trauring's "CI for performance: Reliable benchmarking in noisy environments".
https://pythonspeed.com/articles/consistent-benchmarking-in-ci/

"""

import argparse
import datetime
import json
from subprocess import DEVNULL, CalledProcessError, check_call, check_output
from tempfile import NamedTemporaryFile
from typing import IO, Dict, List

DataT = Dict[str, int]
RawT = Dict[str, str | int]
MetadataT = Dict[str, str]
ReportT = Dict[str, RawT | DataT | MetadataT]


def git_rev() -> str:
    try:
        return check_output(["git", "rev-parse", "HEAD"], stderr=DEVNULL, text=True).strip()
    except (CalledProcessError, OSError):
        return "unknown"


def estimate_time(data: DataT) -> int:
    """
    This formula is taken directly from https://pythonspeed.com/articles/consistent-benchmarking-in-ci/

    It may be prudent to conduct some experiments ourselves to construct a formula that fits our setup better.
    """
    return data['l1'] + (5 * data['ll']) + (35 * data['ram'])


def generate_report(cg: RawT) -> ReportT:
    """
    Generates a report with l1, ll, ram hits, the estimated execution time, and some metadata (timestamp and commit hash). The raw cachegrind log is embedded too.
    """
    data: DataT = {}
    metadata: MetadataT = {}
    report: ReportT = {'raw': cg, 'data': data, 'metadata': metadata}

    counters: DataT = {}
    for name in ("DLmr", "DLmw", "ILmr", "I1mr", "D1mw", "D1mr", "Ir", "Dr", "Dw"):
        value = cg.get(name)
        if not isinstance(value, int):
            raise ValueError(f"Cachegrind report is missing an integer {name} counter")
        counters[name] = value

    ram_hits = counters["DLmr"] + counters["DLmw"] + counters["ILmr"]
    ll_hits = counters["I1mr"] + counters["D1mw"] + counters["D1mr"] - ram_hits
    total_memory_rw = counters["Ir"] + counters["Dr"] + counters["Dw"]
    l1_hits = total_memory_rw - ll_hits - ram_hits
    assert total_memory_rw == l1_hits + ll_hits + ram_hits

    data['l1'] = l1_hits
    data['ll'] = ll_hits
    data['ram'] = ram_hits
    data['time_estimate'] = estimate_time(data)

    metadata['timestamp'] = str(datetime.datetime.now())
    metadata['commit'] = git_rev()

    return report


def parse_cachegrind_file(cg_file: IO[str]) -> RawT:
    """Return the summary counters and raw log from a Cachegrind output file."""
    events: list[str] = []
    summary: list[str] = []
    for line in cg_file:
        if line.startswith("events:"):
            events = line.partition(":")[2].split()
        elif line.startswith("summary:"):
            summary = line.partition(":")[2].split()

    if not events or not summary:
        raise ValueError("Cachegrind output is missing an events or summary record")
    if len(events) != len(summary) or len(set(events)) != len(events):
        raise ValueError("Cachegrind events and summary do not identify the same counters")

    try:
        report: RawT = dict(zip(events, map(int, summary)))
    except ValueError:
        raise ValueError("Cachegrind summary contains a non-integer counter") from None
    cg_file.seek(0)
    report["log"] = cg_file.read()
    return report


def cachegrind(verbose: bool, cache_config: list[str], args_list: List[str]) -> RawT:
    """
    Runs cachegrind with the provided cache config on the given program.

    We disable Address Space Layout Randomization (ASLR) using `setarch $(uname -m) -R`.
    """
    verbose_flag: List[str] = list([x for x in ['-v'] if verbose])
    march: str = check_output(["uname", "-m"]).strip().decode('ascii')
    with NamedTemporaryFile("r+", encoding="utf-8") as temp_file:
        cmd: List[str] = (
            [
                "setarch",
                march,
                "-R",
                "valgrind",
                "--instr-at-start=no",
                "--tool=cachegrind",
                "--cache-sim=yes",
                "--branch-sim=yes",
                "--cachegrind-out-file=" + temp_file.name,
            ]
            + cache_config
            + verbose_flag
            + args_list
        )
        check_call(cmd)
        return parse_cachegrind_file(temp_file.file)


def prepare_cache_args(config: Dict[str, Dict[str, int]]) -> List[str]:
    """
    Constructs the cache detail arguments, e.g. --I1=A,B,C --D1=P,Q,R --LL=X,Y,Z
    """
    i1 = config['I1']
    d1 = config['D1']
    ll = config['LL']
    args = [
        f"--I1={i1['size']},{i1['assoc']},{i1['line_size']}",
        f"--D1={d1['size']},{d1['assoc']},{d1['line_size']}",
        f"--LL={ll['size']},{ll['assoc']},{ll['line_size']}",
    ]
    return args


def load_cache_config(file: str) -> List[str]:
    """
    Loads and prepares the cache detail arguments.
    """
    data: Dict[str, Dict[str, int]] = {}
    with open(file, "r") as config:
        data = json.load(config)
    return prepare_cache_args(data)


def main() -> None:
    # Commandline interface
    argparser = argparse.ArgumentParser(description="Cachegrind benchmark runner")
    argparser.add_argument("--config", metavar="FILE", type=str, help="Cache details config", required=False)
    argparser.add_argument(
        "-o",
        metavar="FILE",
        type=str,
        help="Save the full report to this file; otherwise print the estimated time",
        required=False,
    )
    argparser.add_argument("-v", "--verbose", action="store_true", help="Toggle verbose output")
    argparser.add_argument("program", nargs=argparse.REMAINDER, help="Program to benchmark along with its arguments")
    args = argparser.parse_args()

    program = args.program
    if program and program[0] == "--":
        program = program[1:]
    if not program:
        argparser.error("a program to benchmark is required")

    try:
        cache_config = load_cache_config(args.config) if args.config else []
        report = generate_report(cachegrind(args.verbose, cache_config, program))
    except (ValueError, OSError, CalledProcessError, KeyError) as error:
        argparser.exit(1, f"{argparser.prog}: {error}\n")
    if args.o:
        with open(args.o, 'w') as outfile:
            json.dump(report, outfile, indent=2)
    else:
        print(json.dumps(report['data']['time_estimate'], indent=2))


if __name__ == "__main__":
    main()

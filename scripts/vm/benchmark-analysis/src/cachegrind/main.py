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
  -o FILE        Save the report to this file (default: /dev/stdout)
  -v,--verbose   Toggle verbose output

## Acknowledgements

Based on Itamar Turner-Trauring's "CI for performance: Reliable benchmarking in noisy environments".
https://pythonspeed.com/articles/consistent-benchmarking-in-ci/

"""

import argparse
import datetime
import json
from subprocess import check_call, check_output
from tempfile import NamedTemporaryFile, _TemporaryFileWrapper
from typing import Dict, List

DataT = Dict[str, int]
RawT = Dict[str, str | int]
MetadataT = Dict[str, str]
ReportT = Dict[str, RawT | DataT | MetadataT]


def git_rev() -> str:
    return check_output(["git", "rev-parse", "HEAD"]).strip().decode('ascii')


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

    assert (
        isinstance(cg['DLmr'], int)
        and isinstance(cg['DLmw'], int)
        and isinstance(cg['ILmr'], int)
        and isinstance(cg['I1mr'], int)
        and isinstance(cg['D1mw'], int)
        and isinstance(cg['D1mr'], int)
        and isinstance(cg['Ir'], int)
        and isinstance(cg['Dr'], int)
        and isinstance(cg['Dw'], int)
    )
    ram_hits = cg['DLmr'] + cg['DLmw'] + cg['ILmr']
    ll_hits = cg['I1mr'] + cg['D1mw'] + cg['D1mr'] - ram_hits
    total_memory_rw = cg['Ir'] + cg['Dr'] + cg['Dw']
    l1_hits = total_memory_rw - ll_hits - ram_hits
    assert total_memory_rw == l1_hits + ll_hits + ram_hits

    data['l1'] = l1_hits
    data['ll'] = ll_hits
    data['ram'] = ram_hits
    data['time_estimate'] = estimate_time(data)

    metadata['timestamp'] = str(datetime.datetime.now())
    metadata['commit'] = git_rev()

    return report


def parse_cachegrind_file(cg_file: _TemporaryFileWrapper) -> RawT:
    """
    Parses a cachegrind out file and returns a dictionary with the summary data.
    """

    lines = iter(cg_file)
    for line in lines:
        if line.startswith("events: "):
            header = line[len("events: ") :].strip()
            break
    *_, last_line = lines
    assert last_line.startswith("summary: ")
    last_line = last_line[len("summary:") :].strip()
    report: RawT = dict(zip(header.split(), [int(i) for i in last_line.split()]))
    cg_file.seek(0)
    report['log'] = cg_file.read()
    return report


def cachegrind(verbose: bool, cache_config: list[str], args_list: List[str]) -> RawT:
    """
    Runs cachegrind with the provided cache config on the given program.

    We disable Address Space Layout Randomization (ASLR) using `setarch $(uname -m) -R`.
    """
    verbose_flag: List[str] = list([x for x in ['-v'] if verbose])
    march: str = check_output(["uname", "-m"]).strip().decode('ascii')
    temp_file = NamedTemporaryFile("r+")
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
    return parse_cachegrind_file(temp_file)


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
        "-o", metavar="FILE", type=str, help="Save the report to this file (default: /dev/stdout)", required=False
    )
    argparser.add_argument(
        "-v,--verbose", dest='verbose', action='store_true', help="Toggle verbose output", required=False
    )
    argparser.add_argument("program", nargs=argparse.REMAINDER, help="Program to benchmark along with its arguments")
    args = argparser.parse_args()

    # Load cache config, if any
    cache_config = []
    if args.config:
        cache_config = load_cache_config(args.config)
    report = generate_report(cachegrind(args.verbose, cache_config, args.program))
    if args.o:
        with open(args.o, 'w') as outfile:
            json.dump(report, outfile, indent=2)
    else:
        print(json.dumps(report['data']['time_estimate'], indent=2))


if __name__ == "__main__":
    main()

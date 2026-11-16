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

"""Run clang-tidy in parallel, largest files first.

LLVM's run-clang-tidy starts files in a random order, so the slowest files
often start last and the run waits on them. This takes the run-clang-tidy
options that check-clang-tidy.sh uses, and only checks: LLVM's driver applies
fixes.
"""

import argparse
import json
import os
import subprocess
import sys
import time
from multiprocessing.pool import ThreadPool

parser = argparse.ArgumentParser()
parser.add_argument("files", nargs="+")
parser.add_argument("-p", dest="build_dir", required=True)
parser.add_argument("-j", dest="jobs", type=int, default=os.cpu_count())
parser.add_argument("-clang-tidy-binary", default="clang-tidy")
parser.add_argument("-checks")
parser.add_argument("-header-filter")
parser.add_argument("-load", action="append", default=[])
parser.add_argument("-extra-arg", action="append", default=[])
parser.add_argument("-quiet", action="store_true")
args = parser.parse_args()

with open(os.path.join(args.build_dir, "compile_commands.json")) as f:
    database = {
        os.path.realpath(os.path.join(e["directory"], e["file"]))
        for e in json.load(f)
    }
files = sorted(
    {f for f in map(os.path.realpath, args.files) if f in database},
    key=lambda f: (-os.path.getsize(f), f),
)

command = [args.clang_tidy_binary, f"-p={args.build_dir}"]
if args.checks:
    command.append(f"-checks={args.checks}")
if args.header_filter:
    command.append(f"-header-filter={args.header_filter}")
command += [f"-load={p}" for p in args.load]
command += [f"-extra-arg={a}" for a in args.extra_arg]
if args.quiet:
    command.append("-quiet")


def run(file):
    start = time.monotonic()
    result = subprocess.run(
        [*command, file], capture_output=True, text=True
    )
    return file, result, time.monotonic() - start


print(f"Running clang-tidy on {len(files)} files", flush=True)
failed = False
with ThreadPool(args.jobs) as pool:
    results = pool.imap_unordered(run, files)
    for n, (file, result, seconds) in enumerate(results, 1):
        print(f"[{n}/{len(files)}][{seconds:.1f}s] {file}")
        print(result.stdout, end="")
        if result.returncode != 0:
            failed = True
            print(result.stderr, end="")
        sys.stdout.flush()

sys.exit(1 if failed else 0)

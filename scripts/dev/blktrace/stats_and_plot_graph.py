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
import re
from collections.abc import Iterable
from pathlib import Path

import pandas as pd
import pygal

MAX_PLOT_POINTS = 1_000_000
MAX_VALID_LATENCY = 1_000_000_000
LATENCY = re.compile(r"\((\s*\d+\s*)\)")


def read_latencies(lines: Iterable[str]) -> list[int]:
    latencies = []
    for line in lines:
        for match in LATENCY.finditer(line):
            latency = int(match.group(1))
            # blkparse can emit wrapped unsigned latencies.
            if latency < MAX_VALID_LATENCY:
                latencies.append(latency)
    return latencies


def main() -> None:
    parser = argparse.ArgumentParser(description="Summarize and plot blkparse read latencies")
    parser.add_argument("trace", type=Path, help="Text output from blkparse")
    parser.add_argument("-o", "--output", type=Path, default=Path("io_latencies.svg"), help="Output SVG path")
    args = parser.parse_args()

    print(f"Reading {args.trace} ...")
    try:
        with args.trace.open(encoding="utf-8") as file:
            latencies = read_latencies(file)
    except (OSError, UnicodeError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")

    if not latencies:
        parser.exit(1, f"{parser.prog}: no valid latencies found in {args.trace}\n")

    percentiles = [.25, .50, .75, .90, .99, .999]
    frame = pd.DataFrame(latencies, columns=["latency"])
    print(frame.describe(percentiles=percentiles).to_string(float_format="{:.2f}".format))

    # Zero is a valid measurement for the summary, but has no logarithm.
    points = [latency or None for latency in latencies[:MAX_PLOT_POINTS]]
    if all(latency is None for latency in points):
        print("No positive latencies in the plot range; skipped the logarithmic chart.")
        return

    print(f"Rendering {args.output} ...")
    chart = pygal.Line(stroke=False, logarithmic=True)
    chart.title = "I/O latencies"
    chart.add("reads", points, dots_size=0.12)
    chart.render_to_file(args.output)


if __name__ == "__main__":
    main()

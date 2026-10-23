#!/usr/bin/env python3
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

"""Reads a .graph file for monad-bench with graph_fixture.py, which parses the
graph language, and prints, one per line, in hex:

    graphcode <graphcode>
    account <address> <code>    per account whose code the graph's tensorrefs
                                read
    input <elements>            per input of the call, little-endian
    expected <elements>         per output, the reference evaluator's,
                                little-endian, unless --no-reference

graph_fixture.py reads the graph language's opcodes and constants from the
C++ sources of the repository it's in.

Usage: graph_inputs.py <graph_fixture.py> <file.graph> [--call N]
                       [--no-reference]
"""

import argparse
import importlib
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("graph_fixture", type=Path)
    parser.add_argument("graph", type=Path)
    parser.add_argument("--call", type=int, default=0)
    parser.add_argument("--no-reference", action="store_true")
    args = parser.parse_args()

    # Imported from its own directory, as it's a script, not a package
    sys.path.insert(0, str(args.graph_fixture.resolve().parent))
    gf = importlib.import_module(args.graph_fixture.stem)

    graph = gf.parse(args.graph.read_text())
    if not 0 <= args.call < len(graph.calls):
        sys.exit(f"{args.graph} has {len(graph.calls)} calls, no call "
                 f"{args.call}")
    call = graph.calls[args.call]
    inputs = [call.inputs[name].tensor for name, _, _ in graph.inputs]

    out = sys.stdout
    out.write(f"graphcode {gf.graphcode(graph).hex()}\n")
    for address, code in graph.accounts.items():
        out.write(f"account {address.hex()} {code.hex()}\n")
    for tensor in inputs:
        out.write(f"input {tensor.dtype.encode(tensor.values, 'little').hex()}"
                  "\n")
    if not args.no_reference:
        for tensor in gf.evaluate(graph, inputs):
            out.write("expected "
                      f"{tensor.dtype.encode(tensor.values, 'little').hex()}\n")


if __name__ == "__main__":
    main()

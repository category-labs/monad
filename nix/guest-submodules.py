#!/usr/bin/env python3
# Copyright (C) 2026 Category Labs, Inc.
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

"""Pin the submodules the zkVM guest build reads, for nix/zisk-elf.nix.

nix exports a git tree without its submodules unless asked for all of them,
nested test-vector repositories included, so the guest build fetches the few
it needs by itself. Their URLs and revisions are written to
guest-submodules.json from .gitmodules and the gitlinks of HEAD. `--check`
fails when that file is stale, so CI catches a submodule bump that forgot it.
"""

import json
import pathlib
import subprocess
import sys

PATHS = [
    "third_party/blst",
    "third_party/cthash",
    "third_party/evmc",
    "third_party/immer",
    "third_party/komihash",
    "third_party/nlohmann_json",
    "third_party/unordered_dense",
    "third_party/zkevm-standards",
]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parent.parent

    def git(*args: str) -> str:
        return subprocess.check_output(["git", "-C", repo, *args], text=True).strip()

    # Submodule names need not match their paths; key the URLs by path.
    urls = {}
    for line in git("config", "-f", ".gitmodules", "--get-regexp", r"^submodule\..*\.path$").splitlines():
        key, path = line.split(maxsplit=1)
        name = key[len("submodule.") : -len(".path")]
        urls[path] = git("config", "-f", ".gitmodules", "--get", f"submodule.{name}.url")

    pins = {}
    for path in PATHS:
        if path not in urls:
            sys.exit(f"{path} is not declared in .gitmodules")
        fields = git("ls-tree", "HEAD", path).split()
        if len(fields) < 3 or fields[1] != "commit":
            sys.exit(f"{path} is not a submodule of HEAD")
        pins[path] = {"url": urls[path], "rev": fields[2]}
    text = json.dumps(pins, indent=2) + "\n"

    out = repo / "nix" / "guest-submodules.json"
    if sys.argv[1:] == ["--check"]:
        if not out.is_file() or out.read_text() != text:
            sys.exit(f"{out.relative_to(repo)} is stale: run {sys.argv[0]}")
    elif sys.argv[1:]:
        sys.exit(f"usage: {sys.argv[0]} [--check]")
    else:
        out.write_text(text)


if __name__ == "__main__":
    main()

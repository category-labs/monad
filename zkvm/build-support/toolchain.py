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

"""Shared toolchain fingerprint for Cargo and standalone archive builds."""

import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess


def fingerprint(gcc):
    gcc = Path(gcc)
    prefix = gcc.name.removesuffix("gcc")
    cxx = gcc.with_name(prefix + "g++")
    files = [gcc, cxx]
    for driver, program in ((gcc, "cc1"), (cxx, "cc1plus"), (gcc, "as")):
        name = subprocess.check_output(
            [str(driver), "-print-prog-name=" + program], text=True
        ).strip()
        path = Path(name)
        if not path.is_file():
            found = shutil.which(name)
            if found is None:
                raise FileNotFoundError(f"cannot locate {program}: {name}")
            path = Path(found)
        files.append(path)
    files.extend(gcc.with_name(prefix + name) for name in ("ar", "ranlib"))
    digest, paths = fingerprint_files(files)
    # Watch the directory too: a higher-priority compiler prefix may appear.
    return digest, [gcc.parent, *paths]


def fingerprint_files(files):
    digest = hashlib.sha256()
    paths = []
    for path in files:
        # Watch and hash both the symlink path and its target.
        for name in (path, path.resolve(strict=True)):
            paths.append(name)
            digest.update(os.fsencode(name))
            digest.update(b"\0")
        content = hashlib.sha256()
        with path.open("rb") as source:
            for chunk in iter(lambda: source.read(64 * 1024), b""):
                content.update(chunk)
        digest.update(content.digest())
    return digest.hexdigest(), paths


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("gcc", type=Path)
    parser.add_argument(
        "--watch-paths", action="store_true",
        help="print Cargo's watched paths after the fingerprint, one per line",
    )
    args = parser.parse_args()
    digest, paths = fingerprint(args.gcc)
    print(digest)
    if args.watch_paths:
        for path in paths:
            print(path)

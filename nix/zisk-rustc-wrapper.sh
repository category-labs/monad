#!/bin/sh
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

# RUSTC_WRAPPER for guest builds that must not depend on where they were
# built. Two things would otherwise carry nix's randomly named build
# directory into the ELF:
#
# - Panic locations in the vendored crates name their source files: remap
#   $NIX_BUILD_TOP to /build in every path rustc records.
# - Cargo derives a crate's -C metadata from the absolute path of any path
#   dependency outside the workspace root, and that hash names the crate's
#   codegen unit in the symbol table: pin the metadata of the crate named
#   in $ZISK_ROOT_CRATE, which nothing else links against.
#
# The remap goes through this wrapper rather than RUSTFLAGS because cargo
# folds those into its fingerprints, and the mapping itself names the
# random directory.
set -eu

if [ -n "${ZISK_ROOT_CRATE:-}" ]; then
    root=0
    for a in "$@"; do
        [ "$a" = "$ZISK_ROOT_CRATE" ] && root=1
    done
    if [ $root = 1 ]; then
        n=$#
        while [ $n -gt 0 ]; do
            a=$1
            shift
            case "$a" in metadata=*) a="metadata=$ZISK_ROOT_CRATE" ;; esac
            set -- "$@" "$a"
            n=$((n - 1))
        done
    fi
fi

if [ -n "${NIX_BUILD_TOP:-}" ]; then
    set -- "$@" --remap-path-prefix="$NIX_BUILD_TOP=/build"
fi

exec "$@"

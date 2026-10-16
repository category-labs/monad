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

# Keep temporary build paths out of panic locations and crate symbols:
# - Remap NIX_BUILD_TOP to /build.
# - Fix ZISK_ROOT_CRATE's metadata, which Cargo derives from dependency
#   paths. Only the root crate is changed; no other crate links against it.
# Use a wrapper rather than RUSTFLAGS, whose changing path would affect
# Cargo fingerprints.
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

#!/bin/sh
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

#!/bin/sh

# Prefixes every global symbol defined in the library archive with the given
# input string, followed by a '_' separator
#
# Usage:
#   prefix_symbols.sh <nm-executable> <objcopy-executable> <archive> <prefix>
set -e

nm=$1
objcopy=$2
archive=$3
prefix=$4

"$nm" --defined-only --extern-only --format=posix "$archive" > "$archive.symbols"
awk -v p="$prefix" 'NF > 1 && $1 !~ /^_/ { print $1, p "_" $1 }' "$archive.symbols" > "$archive.renames"
rm -f "$archive.symbols"
sort -u -o "$archive.renames" "$archive.renames"
"$objcopy" --redefine-syms="$archive.renames" "$archive"

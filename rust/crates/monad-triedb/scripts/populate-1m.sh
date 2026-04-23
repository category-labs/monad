#!/usr/bin/env bash
#
# Populate a triedb at ./test_db/ with keys 1..1048576.
#
# Key format (8 bytes = 16 hex chars):
#   big-endian encoding of the index i, i.e. sprintf("%016x", i)
#
# Value format (16 bytes = 32 hex chars):
#   the 8-byte key repeated twice, i.e. sprintf("%016x%016x", i, i)
#
# Per pair in argv: 16 + 1 + 32 + 1 = 50 chars. Linux enforces a
# per-argument size limit (MAX_ARG_STRLEN = 128 KB) that's tighter than
# ARG_MAX overall. CHUNK=1024 pairs = ~50 KB, well under that ceiling.
#
# For 1M keys at CHUNK=1024 that's 1024 invocations. Each `write` builds
# a new version inheriting from the previous via `--base latest`.
#
# Usage:
#   ./populate-1m.sh                    # defaults (TOTAL=1048576, CHUNK=32000)
#   TOTAL=10000 CHUNK=1000 ./populate-1m.sh
#   DB_DIR=./foo.db ./populate-1m.sh    # override output directory
#   CLI=/path/to/monad-triedb-cli ./populate-1m.sh

set -euo pipefail

TOTAL=${TOTAL:-1048576}
CHUNK=${CHUNK:-1024}
DB_DIR=${DB_DIR:-./test_db}

# Locate the CLI binary.
if [[ -z "${CLI:-}" ]]; then
    script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
    candidate="$script_dir/../../../target/debug/examples/monad-triedb-cli"
    if [[ -x "$candidate" ]]; then
        CLI="$candidate"
    elif command -v monad-triedb-cli &>/dev/null; then
        CLI=monad-triedb-cli
    else
        echo "error: monad-triedb-cli not found; set CLI=<path>" >&2
        exit 1
    fi
fi

DB_FILE="$DB_DIR/db"

mkdir -p "$DB_DIR"
rm -f "$DB_FILE"

echo "creating empty triedb at $DB_FILE"
"$CLI" create --path "$DB_FILE"

num_blocks=$(( (TOTAL + CHUNK - 1) / CHUNK ))
echo "populating $TOTAL keys in $num_blocks blocks of up to $CHUNK each"

for (( block = 1; block <= num_blocks; block++ )); do
    start=$(( (block - 1) * CHUNK + 1 ))
    end=$(( block * CHUNK ))
    if (( end > TOTAL )); then
        end=$TOTAL
    fi

    # Build `k1:v1,k2:v2,...` in one awk pass.
    # key = sprintf("%016x", i)    -- 8 bytes, BE u64
    # value = key repeated twice    -- 16 bytes
    pairs=$(awk -v start="$start" -v end="$end" 'BEGIN {
        sep = "";
        for (i = start; i <= end; i++) {
            key = sprintf("%016x", i);
            printf "%s%s:%s%s", sep, key, key, key;
            sep = ",";
        }
    }')

    if (( block == 1 )); then
        base="empty"
    else
        base="latest"
    fi

    echo "  block $block: keys $start..$end (base $base)"
    "$CLI" write --path "$DB_FILE" --block "$block" --base "$base" "$pairs"
done

echo
echo "done. db at $DB_DIR/ has $TOTAL keys across $num_blocks versions."
echo "verify with:  $CLI info --path $DB_DIR"

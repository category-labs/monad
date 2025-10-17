#! /bin/sh
#
# compile-smart-contracts.sh: Gather statistics on the compilation of smart
#                             contracts in directory using mce's -o option.
# Usage: compile-smart-contracts.sh <directory>

set -e -u

if [ $# -ne 2 ]; then
  echo "Usage: $0 <directory> <output_dir>"
  exit 1
fi

log() {
  printf "%s\n" "$1" 2>&1
}

DIR="$1"
OUT_DIR="$2"
N=64 # Number of parallel mce processes to run

# Count number of non-empty files to process
N_FILES=0
for file in "$DIR"/*; do
  # Skip if file is empty
  if [ ! -s "$file" ]; then
    continue
  fi
  N_FILES=$((N_FILES + 1))
done

go() {
  HEX_FILE="$OUT_DIR/$(basename "$file").hex"
  JSON_FILE="$OUT_DIR/$(basename "$file").json"
  xxd -c 0 -ps "$file" > "$HEX_FILE"
  ./build/cmd/vm/mce/mce --compile-only -o "$HEX_FILE" > "$JSON_FILE"
}

# Process files
ix=0
for file in "$DIR"/*; do
  # Skip if file is empty
  if [ ! -s "$file" ]; then
    log "Skipping empty file: $file"
    continue
  else
    : $((ix = ix + 1))
    log "Processing file: $file ($ix/$N_FILES)"
  fi

  go "$file" &

  # If we've started N tasks, wait for them to finish
  [ $((ix % N)) -eq 0 ] && wait
done

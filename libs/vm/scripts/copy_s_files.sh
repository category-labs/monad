#!/bin/bash

set -e

SOURCE_DIR=$(realpath "$1")
TARGET_DIR=$(realpath "$2")

mkdir -p "$TARGET_DIR"

find "$SOURCE_DIR" -type f -name '*.s' -print0 | while IFS= read -r -d '' src_file; do
    # Skip files already in the target directory
    if [[ "$src_file" == "$TARGET_DIR"* ]]; then
        continue
    fi

    filename=$(basename "$src_file")
    dest_file="$TARGET_DIR/$filename"

    # Copy only if destination doesn't exist or files differ
    if [[ ! -e "$dest_file" ]] || ! cmp -s "$src_file" "$dest_file"; then
        cp "$src_file" "$dest_file"
    fi
done
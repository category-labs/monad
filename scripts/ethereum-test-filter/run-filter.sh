#!/bin/bash

set -x
set -e

TMP=$(mktemp)
sed '$a\' "$2" > "$TMP"

# Read input line by line
while IFS= read -r line; do
	# skip empty lines or commented lines
	if [[ -z "$line" || "$line" == '#'* ]]; then
		continue
	fi
	# Split the line by space
	read -r fork filter <<<"$line"
	$1 --gtest_filter=$filter --fork $fork
done < "$TMP"

rm "$TMP"

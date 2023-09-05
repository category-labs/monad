#!/bin/bash

set -x
set -e

# add a new line so parsing does not
# get confused if the filter file does not
# end in a new line
sed -i '$a\' "$2"

# Read input line by line
while IFS= read -r line; do
	# skip empty lines or commented lines
	if [[ -z "$line" || "$line" == '#'* ]]; then
		continue
	fi
	# Split the line by space
	read -r fork filter <<<"$line"
	$1 --gtest_filter=$filter --fork $fork
done <"$2"

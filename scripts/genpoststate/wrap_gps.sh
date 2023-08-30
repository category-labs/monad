#!/usr/bin/env bash

set -e

#!/bin/bash

if [ $# -ne 3 ]; then
	echo "Usage: $0 <path_to_json_test_file> <fork_name> <transaction index>"
	exit 1
fi

json_file="$1"

if [ ! -f "$json_file" ]; then
	echo "Error: The specified file does not exist."
	exit 1
fi

fork_name="$2"
transaction_index="$3"

(cd scripts/genpoststate &&
	docker build -t gps \
		--build-arg USER_ID="$(id -u)" \
		--build-arg GROUP_ID="$(id -g)" .) 2>&1 >/dev/null

cat "$json_file" | docker run -i gps $fork_name $transaction_index

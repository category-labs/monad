#!/usr/bin/env bash
set -uxo pipefail

script_dir=$(dirname "$0")

"$script_dir/tmux-fuzzer.sh" start --base-seed=143
# Waiting 10 mins should be sufficient to find most VM issues in CI:
sleep 600

"$script_dir/tmux-fuzzer.sh" status | grep "TERMINATED"
if [ $? -eq 0 ]; then
    exit 1
fi
#!/usr/bin/env bash
set -uxo pipefail

script_dir=$(dirname "$0")

# One session per vCPU; 7 minutes is ~3,700 fuzz runs, enough to find most VM
# issues in CI:
export FUZZER_COMPILER_SESSIONS=26
export FUZZER_INTERPRETER_SESSIONS=5
"$script_dir/tmux-fuzzer.sh" start --base-seed=143
sleep 420

runs=$(cat "$script_dir"/../../tmux-fuzzer-log/* | grep -c "Fuzzing with seed")
if [ "$runs" -eq 0 ]; then
    exit 1
fi

"$script_dir/tmux-fuzzer.sh" status | grep "TERMINATED"
if [ $? -eq 0 ]; then
    exit 1
fi
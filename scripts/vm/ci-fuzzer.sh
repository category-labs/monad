#!/usr/bin/env bash
set -uxo pipefail

script_dir=$(dirname "$0")
log_dir="$script_dir/../../tmux-fuzzer-log"

# One session per vCPU; the default 7 minutes is ~3,700 fuzz runs, enough to
# find most VM issues in CI:
export FUZZER_COMPILER_SESSIONS=26
export FUZZER_INTERPRETER_SESSIONS=5
"$script_dir/tmux-fuzzer.sh" start --base-seed="${FUZZER_BASE_SEED:-143}"
sleep "${FUZZER_SECONDS:-420}"

runs=$(cat "$log_dir"/* | grep -c "Fuzzing with seed")
if [ "$runs" -eq 0 ]; then
    exit 1
fi

failed=$("$script_dir/tmux-fuzzer.sh" status | grep TERMINATED | cut -d: -f1)
for s in $failed; do
    tac "$log_dir/$s" | sed '/Fuzzing with seed/q' | tac
done
if [ -n "$failed" ]; then
    exit 1
fi

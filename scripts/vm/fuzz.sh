#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat >&2 <<USAGE
Usage: $0 [-c COMPILER] [-i INTERPRETER] [-s SEED] [-t SECONDS] [-- FUZZER_ARGS...]

Runs COMPILER (default 11) and INTERPRETER (default 2) fuzzer sessions with
consecutive seeds starting at SEED (default 0), logging to fuzzer-log/. Stops
at the first failing session, or after SECONDS if given.
USAGE
  exit 1
}

compiler=11
interpreter=2
seed=0
seconds=
while getopts c:i:s:t:h opt; do
  case "$opt" in
    c) compiler=$OPTARG ;;
    i) interpreter=$OPTARG ;;
    s) seed=$OPTARG ;;
    t) seconds=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))

script_dir=$(dirname "$0")
log_dir=$script_dir/../../fuzzer-log
rm -rf "$log_dir"
mkdir -p "$log_dir"

declare -A sessions=()
timer=
trap 'kill "${!sessions[@]}" ${timer:+"$timer"} 2>/dev/null || true' EXIT

start() {
  local name=$1_$2
  "$script_dir/fuzzer.sh" --implementation "$1" --seed "$seed" "${@:3}" \
    > "$log_dir/$name" 2>&1 &
  sessions[$!]=$name
  echo "Started $name with seed $seed"
  seed=$((seed + 1))
}

for ((i = 1; i <= compiler; i++)); do start compiler "$i" "$@"; done
for ((i = 1; i <= interpreter; i++)); do start interpreter "$i" "$@"; done

if [ -n "$seconds" ]; then
  sleep "$seconds" &
  timer=$!
fi

while [ ${#sessions[@]} -gt 0 ]; do
  status=0
  wait -n -p pid "${!sessions[@]}" $timer || status=$?
  if [ "$pid" = "$timer" ]; then
    if [ "$status" -ne 0 ]; then
      echo "Timer failed: sleep $seconds" >&2
      exit 1
    fi
    if ! grep -qs "Fuzzing with seed" "$log_dir"/*; then
      echo "No fuzzer session started a run" >&2
      exit 1
    fi
    echo "All sessions ran for ${seconds}s without failing"
    exit 0
  fi
  name=${sessions[$pid]}
  unset "sessions[$pid]"
  if [ "$status" -ne 0 ]; then
    echo "$name failed:" >&2
    tac "$log_dir/$name" | sed '/Fuzzing with seed/q' | tac >&2
    exit 1
  fi
done

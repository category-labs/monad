#!/usr/bin/env bash

set -e

script_dir=`dirname "$0"`

n=$1
shift

if [ -z "$n" ] || [ $n -gt 100 ] || [ $n -lt 1 ]; then
    echo "Usage: $0 N FUZZER_ARGS..."
    echo "  where 1 <= N <= 100"
    exit 1
fi

pids=
for i in `seq 1 $n`; do
    "$script_dir"/fuzzer.sh --seed $i $@ &
    pids+=($!)
done

trap 'kill ${pids[@]} 2>/dev/null' EXIT INT TERM

wait -n

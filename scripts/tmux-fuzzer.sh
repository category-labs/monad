#!/usr/bin/env bash

script_dir=`dirname "$0"`
root_dir="$script_dir"/..
log_dir="$root_dir/tmux-fuzzer-log"

if [ $# -lt 1 ]; then
    echo "Usage: $0 start|status|kill [--base-seed=<seed>]"
    exit 1
fi

sub_command=$1
shift

if [ "$sub_command" = start ]; then
    base_seed=0

    while [ $# -gt 0 ]; do
        case "$1" in
            --base-seed)
                base_seed=$2
                shift
                shift
                ;;
            --base-seed=*)
                base_seed="${1#*=}"
                shift
                ;;
            *)
                echo "Unknown option for start: $1"
                exit 1
                ;;
        esac
    done

    if [ -z "$base_seed" ] || ! [[ "$base_seed" =~ ^[0-9]+$ ]]; then
        echo "Error: --base-seed requires a non-empty numeric argument"
        exit 1
    fi
fi

compiler_sessions=11
interpreter_sessions=2

start_command() {
    if [ -z "$base_seed" ]; then
        exit 1
    fi

    mkdir -p "$log_dir"

    seed=$base_seed
    for i in `seq 1 $compiler_sessions`; do
        s=fuzzer_compiler_$i
        tmux new-session -d -s $s \
            "$script_dir/fuzzer.sh --implementation compiler --seed $seed > \"$log_dir/$s\" 2>&1"
        if [ $? -ne 0 ]; then
            echo Unable to start Tmux session $s
        else
            echo Started fuzzer Tmux session $s with seed $seed
        fi
        seed=$((seed + 1))
    done

    for i in `seq 1 $interpreter_sessions`; do
        s=fuzzer_interpreter_$i
        tmux new-session -d -s $s \
            "$script_dir/fuzzer.sh --implementation interpreter --seed $seed > \"$log_dir/$s\" 2>&1"
        if [ $? -ne 0 ]; then
            echo Unable to start Tmux session $s
        else
            echo Started fuzzer Tmux session $s with seed $seed
        fi
        seed=$((seed + 1))
    done
}

status_command() {
    list=`tmux ls | awk -F ':' '{ print $1 }'`
    for i in `seq 1 $compiler_sessions`; do
        s=fuzzer_compiler_$i
        if grep $s <<< $list >/dev/null; then
            echo $s: RUNNING
        else
            echo $s: TERMINATED
        fi
    done
    for i in `seq 1 $interpreter_sessions`; do
        s=fuzzer_interpreter_$i
        if grep $s <<< $list >/dev/null; then
            echo $s: RUNNING
        else
            echo $s: TERMINATED
        fi
    done
}

kill_command() {
    list=`tmux ls | awk -F ':' '{ print $1 }'`
    for s in $list; do
        grep fuzzer_ <<< $s >/dev/null
        if [ $? -eq 0 ]; then
            if tmux kill-session -t $s; then
                echo Killed Tmux session $s
            else
                echo Unable to kill Tmux session $s
            fi
        fi
    done
}

if [ "$sub_command" = start ]; then
    start_command
elif [ "$sub_command" = status ]; then
    status_command
elif [ "$sub_command" = kill ]; then
    kill_command
else
    echo Invalid sub-command: $sub_command >&2
    exit 1
fi

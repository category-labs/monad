#!/usr/bin/env bash

script_dir=`dirname "$0"`
root_dir="$script_dir"/..
log_dir="$root_dir/tmux-fuzzer-log"

if [ $# -ne 1 ]; then
    echo "Usage: $0 start|status|kill"
    exit 1
fi

sub_command=$1
shift

compiler_sessions=11
interpreter_sessions=2

start_command() {
    mkdir -p "$log_dir"
    for i in `seq 1 $compiler_sessions`; do
        s=fuzzer_compiler_$i
        tmux new-session -d -s $s \
            "$script_dir/fuzzer.sh --implementation compiler > \"$log_dir/$s\" 2>&1"
        if [ $? -ne 0 ]; then
            echo Unable to start Tmux session $s
        else
            echo Started fuzzer Tmux session $s
        fi
    done
    for i in `seq 1 $interpreter_sessions`; do
        s=fuzzer_interpreter_$i
        tmux new-session -d -s $s \
            "$script_dir/fuzzer.sh --implementation interpreter > \"$log_dir/$s\" 2>&1"
        if [ $? -ne 0 ]; then
            echo Unable to start Tmux session $s
        else
            echo Started fuzzer Tmux session $s
        fi
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

#!/usr/bin/env bash

script_dir="$(dirname "$0")"
root_dir="$(realpath "$script_dir/..")"

clang-format-19 \
  -i $(\
    find \
      "${root_dir}"/category \
      "${root_dir}"/cmd      \
      "${root_dir}"/test     \
        -name '*.hpp' -or \
        -name '*.cpp' -or \
        -name '*.c'   -or \
        -name '*.h')
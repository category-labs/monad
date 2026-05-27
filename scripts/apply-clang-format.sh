#!/usr/bin/env bash

set -euo pipefail

script_dir="$(dirname "$0")"
root_dir="$(realpath "$script_dir/..")"

# Only format unignored files.
cd "${root_dir}"
rg --files -0 -g '*.hpp' -g '*.cpp' -g '*.c' -g '*.h' \
  "${root_dir}/category" \
  "${root_dir}/cmd" \
  "${root_dir}/test" \
  "${root_dir}/zkvm" \
  | xargs -0 -r clang-format-19 -i

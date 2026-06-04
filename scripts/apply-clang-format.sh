#!/usr/bin/env bash

set -euo pipefail

script_dir="$(dirname "$0")"
root_dir="$(realpath "$script_dir/..")"

# Only format unignored files.
cd "${root_dir}"
rg --files -0 -g '*.hpp' -g '*.cpp' -g '*.c' -g '*.h' \
  category cmd test \
  | xargs -0 -r clang-format-19 -i

#!/usr/bin/env bash

set -euo pipefail

source "$(dirname "$0")/ubuntu-build/toolchain.env"

case "${1:-}" in
  "") mode=(-i) ;;
  --check) mode=(--dry-run --Werror) ;;
  *) echo "Usage: $0 [--check]" >&2; exit 1 ;;
esac

# Only format unignored files.
cd "$(dirname "$0")/.."
rg --files -0 -g '*.hpp' -g '*.cpp' -g '*.c' -g '*.h' \
  category \
  cmd \
  test \
  zkvm \
  | xargs -0 -r "clang-format-${LLVM_VERSION}" "${mode[@]}"

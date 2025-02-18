#!/usr/bin/env bash

set -euxo pipefail

LLVM_VERSION=18
BUILD_DIR=build

mapfile -t inputs < <(\
  find libs \
    \( -name '*.cpp' -or -name '*.c' \) \
    -and -not -path '*third_party*')

"run-clang-tidy-$LLVM_VERSION"                    \
  "${inputs[@]}"                                  \
  -header-filter ".*/src/monad/.*"                \
  -clang-tidy-binary "clang-tidy-$LLVM_VERSION"   \
  -j "$(nproc)"                                   \
  -p "${BUILD_DIR}" "$@"                          \
  2>&1 | awk '!/(^Suppressed|^Use -header|^[0-9]+ warnings)/'
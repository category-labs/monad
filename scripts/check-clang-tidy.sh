#!/usr/bin/env bash

set -euo pipefail

source "$(dirname "$0")/ubuntu-build/toolchain.env"

BUILD_DIR=build
RUN_CLANG_TIDY="run-clang-tidy-$LLVM_VERSION"
CACHE_DIR=

usage() {
  cat >&2 <<EOF
Usage: $0 [options...] [-- CLANG_TIDY_ARGS...]
Options:
  -p|--build-dir BUILD_DIR
  -d|--driver RUN_CLANG_TIDY
  -c|--cache-dir CACHE_DIR  skip files whose inputs match a clean run
                            recorded in CACHE_DIR, and record clean runs
EOF
  exit 1
}

while [[ "$#" -gt 0 ]]; do
  case "$1" in
    -p|--build-dir)
      BUILD_DIR="$2"
      shift
      shift
      ;;
    -d|--driver)
      RUN_CLANG_TIDY="$2"
      shift
      shift
      ;;
    -c|--cache-dir)
      CACHE_DIR="$2"
      shift
      shift
      ;;
    --)
      shift
      break
      ;;
    *)
      usage
      ;;
  esac
done

CUSTOM_PASS_OPTIONS=()

CONST_CORRECTNESS_PLUGIN="${BUILD_DIR}/utils/clang-tidy-auto-const/libConstCorrectnessChecks.so"

if [ -f "$CONST_CORRECTNESS_PLUGIN" ]; then
  CUSTOM_PASS_OPTIONS=(-load "$CONST_CORRECTNESS_PLUGIN"
                       -checks='-misc-const-correctness,misc-auto-const-correctness')
fi

# Restrict linting to files that aren't in a .gitignore.
mapfile -d '' -t inputs < <(\
    rg --files -0 \
    -g '*.cpp' -g '*.c' \
    category/async \
    category/core  \
    category/crypto \
    category/event \
    category/execution \
    category/mpt   \
    category/rpc   \
    category/statesync \
    category/vm    \
    zkvm)

CACHE_OPTIONS=()

if [ -n "$CACHE_DIR" ]; then
  mkdir -p "$CACHE_DIR"
  touch "$CACHE_DIR/.start"
  export CLANG_TIDY="clang-tidy-$LLVM_VERSION" CLANG_TIDY_CACHE_DIR="$CACHE_DIR"
  CACHE_OPTIONS=(-clang-tidy-binary "$(dirname "$0")/clang-tidy-cached")
fi

status=0
"${RUN_CLANG_TIDY}"                               \
  "${inputs[@]}"                                  \
  "${CUSTOM_PASS_OPTIONS[@]}"                     \
  "${CACHE_OPTIONS[@]}"                           \
  -header-filter "category/.*"                    \
  -j "$(nproc)"                                   \
  -p "${BUILD_DIR}" "$@"                          \
  -extra-arg='-Wno-unknown-warning-option'        \
  -quiet || status=$?

if [ -n "$CACHE_DIR" ]; then
  # Keep only the results this run used or added.
  find "$CACHE_DIR" -type f ! -newer "$CACHE_DIR/.start" -delete
fi

exit "$status"

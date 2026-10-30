#!/usr/bin/env bash

set -euo pipefail

LLVM_VERSION=19

BUILD_DIR=build
RUN_CLANG_TIDY="run-clang-tidy-$LLVM_VERSION"

usage() {
  cat >&2 <<EOF
Usage: $0 [options...] [-- CLANG_TIDY_ARGS...]
Options:
  -p|--build-dir BUILD_DIR
  -d|--driver RUN_CLANG_TIDY
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
    category/event \
    category/mpt   \
    category/rpc   \
    category/statesync \
    category/vm    \
    zkvm)

"${RUN_CLANG_TIDY}"                               \
  "${inputs[@]}"                                  \
  "${CUSTOM_PASS_OPTIONS[@]}"                     \
  -header-filter "category/.*"                    \
  -j "$(nproc)"                                   \
  -p "${BUILD_DIR}" "$@"                          \
  -extra-arg='-Wno-unknown-warning-option'        \
  -quiet

# These directories are not yet clean under the full set of checks, so lint
# them for bugs only.
mapfile -d '' -t bug_inputs < <(\
    rg --files -0 \
    -g '*.cpp' -g '*.c' \
    category/crypto    \
    category/execution \
    cmd                \
    test)

BUG_CHECKS=-*,bugprone-*,performance-move-const-arg
BUG_CHECKS+=,-bugprone-branch-clone
BUG_CHECKS+=,-bugprone-easily-swappable-parameters
BUG_CHECKS+=,-bugprone-implicit-widening-of-multiplication-result
BUG_CHECKS+=,-bugprone-unchecked-optional-access
BUG_CHECKS+=,-bugprone-unhandled-self-assignment
BUG_CHECKS+=,-bugprone-assignment-in-if-condition
BUG_CHECKS+=,-bugprone-exception-escape
BUG_CHECKS+=,-bugprone-macro-parentheses
BUG_CHECKS+=,-bugprone-suspicious-stringview-data-usage
BUG_CHECKS+=,-bugprone-switch-missing-default-case
BUG_CHECKS+=,-bugprone-too-small-loop-variable
BUG_CHECKS+=,-bugprone-use-after-move

"${RUN_CLANG_TIDY}"                               \
  "${bug_inputs[@]}"                              \
  -checks="${BUG_CHECKS}"                         \
  -header-filter "category/.*"                    \
  -j "$(nproc)"                                   \
  -p "${BUILD_DIR}" "$@"                          \
  -extra-arg='-Wno-unknown-warning-option'        \
  -quiet

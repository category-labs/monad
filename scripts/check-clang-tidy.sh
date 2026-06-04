#!/usr/bin/env bash

set -euo pipefail

LLVM_VERSION=19

BUILD_DIR=build
RUN_CLANG_TIDY="run-clang-tidy-$LLVM_VERSION"

usage() {
  echo "Usage: $0 [options...] [-- CLANG_TIDY_ARGS...]" 1>&2
  echo "Options:"
  echo "  -p|--build-dir BUILD_DIR"
  echo "  -d|--driver RUN_CLANG_TIDY"
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
    -*)
      usage
      ;;
  esac
done


CUSTOM_PASS_OPTIONS=( )

CONST_CORRECTNESS_PLUGIN="${BUILD_DIR}/utils/clang-tidy-auto-const/libConstCorrectnessChecks.so"

if [ -f $CONST_CORRECTNESS_PLUGIN ]; then
  CUSTOM_PASS_OPTIONS=( -load $CONST_CORRECTNESS_PLUGIN \
                        -checks='-misc-const-correctness,misc-auto-const-correctness' )
fi


# Restrict linting to files that aren't in a .gitignore.
mapfile -d '' -t inputs < <(\
    rg --files -0 \
    -g '*.cpp' -g '*.c' \
    category/async \
    category/core  \
    category/mpt   \
    category/rpc   \
    category/vm)

"${RUN_CLANG_TIDY}"                               \
  "${inputs[@]}"                                  \
  "${CUSTOM_PASS_OPTIONS[@]}"                     \
  -header-filter "category/.*"                    \
  -j "$(nproc)"                                   \
  -p "${BUILD_DIR}" "$@"                          \
  -extra-arg='-Wno-unknown-warning-option'        \
  -quiet

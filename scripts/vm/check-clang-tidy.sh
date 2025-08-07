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

mapfile -t inputs < <(\
  find \
    category/vm \
    \( -name '*.cpp' -or -name '*.c' \) \
    -and -not -path '*third_party*')

"${RUN_CLANG_TIDY}"                               \
  "${inputs[@]}"                                  \
  -header-filter "category/vm/.*"                \
  -j "$(nproc)"                                   \
  -p "${BUILD_DIR}" "$@"                          \
  -extra-arg='-Wno-unknown-warning-option'        \
  -quiet

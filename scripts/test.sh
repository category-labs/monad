#!/bin/bash

set -Eeuo pipefail

CTEST_PARALLEL_LEVEL=${CTEST_PARALLEL_LEVEL:-$(nproc)} \
  ctest --output-on-failure --timeout 1500 --no-tests=error --test-dir build

# Read the actual build settings even when configuration happened in a
# different shell or CC is set to a different compiler now.
compiler=
build_type=
while IFS= read -r line; do
  case "$line" in
    CMAKE_CXX_COMPILER:*=*) compiler=${line#*=} ;;
    CMAKE_BUILD_TYPE:*=*) build_type=${line#*=} ;;
  esac
done < build/CMakeCache.txt

# test_disas pins x86-64 codegen and is only stable under clang* + RelWithDebInfo
# (goldens captured with Clang 19; regenerate on a compiler upgrade). On the
# supported toolchain we require collection and all tests to pass; on everything
# else we filter it out and tolerate an empty collection (exit 5), since the
# dir currently holds no non-disas tests.
if [[ "$(uname -m)" == x86_64 && "${compiler##*/}" == clang* && "$build_type" == RelWithDebInfo ]]; then
  pytest-3 category/core/monad/tests/
else
  pytest-3 category/core/monad/tests/ -k "not test_disas" || [ $? -eq 5 ]
fi

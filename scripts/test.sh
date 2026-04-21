#!/bin/bash

set -Eeuo pipefail

CTEST_PARALLEL_LEVEL=${CTEST_PARALLEL_LEVEL:-$(nproc)} \
  ctest --output-on-failure --timeout 500 --test-dir build

# test_disas pins x86-64 codegen and is only stable under clang* + RelWithDebInfo
# (goldens captured with Clang 19; regenerate on a compiler upgrade). On the
# supported toolchain we require collection and all tests to pass; on everything
# else we filter it out and tolerate an empty collection (exit 5), since the
# dir currently holds no non-disas tests.
if [[ "${CC}" == clang* ]] && [ "${CMAKE_BUILD_TYPE}" = "RelWithDebInfo" ]; then
  pytest-3 category/core/monad/tests/
else
  pytest-3 category/core/monad/tests/ -k "not test_disas" || [ $? -eq 5 ]
fi

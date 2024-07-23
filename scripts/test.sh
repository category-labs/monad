#!/bin/bash

set -Eeuo pipefail

BUILD_DIR="${1:-build}"

CTEST_PARALLEL_LEVEL=${CTEST_PARALLEL_LEVEL:-$(nproc)} \
  ctest --output-on-failure --timeout 300 --test-dir "${BUILD_DIR}"

PYTEST_MATCH_ARGS=""
if [ "${CC}" != "clang" ] || [ "${CMAKE_BUILD_TYPE}" != "RelWithDebInfo" ]; then
  PYTEST_MATCH_ARGS="-k not test_callgrind and not test_disas"
fi

pytest-3 --pyargs monad ${PYTEST_MATCH_ARGS:+"${PYTEST_MATCH_ARGS}"} || [ $? -eq 5 ]

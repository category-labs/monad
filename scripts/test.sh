#!/bin/bash

set -Eeuo pipefail

CTEST_PARALLEL_LEVEL=${CTEST_PARALLEL_LEVEL:-$(nproc)} \
  ctest --output-on-failure --timeout 500 --test-dir build

PYTEST_MATCH_ARGS=""
if [ "${CMAKE_BUILD_TYPE}" != "RelWithDebInfo" ]; then
  PYTEST_MATCH_ARGS="-k not test_callgrind and not test_disas"
elif [ "${CC}" != "clang" ]; then
  PYTEST_MATCH_ARGS="-k not test_callgrind"
fi

pytest-3 --pyargs category ${PYTEST_MATCH_ARGS:+"${PYTEST_MATCH_ARGS}"} || [ $? -eq 5 ]

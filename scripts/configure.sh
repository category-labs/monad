#!/bin/bash

ADDITIONAL_ARGS=
if [ "${CMAKE_BUILD_TYPE}" != "RelWithDebInfo" ]; then
  # Only enable in Debug, otherwise the python tests fail
  # due to the coverage instrumentation
  ADDITIONAL_ARGS=-DMONAD_EMIT_CODE_COVERAGE:BOOL=TRUE
fi

cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -B build \
  -G Ninja \
  $ADDITIONAL_ARGS

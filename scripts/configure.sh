#!/bin/bash

cmake_args=(
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE
  -DCMAKE_BUILD_TYPE:STRING=${CMAKE_BUILD_TYPE:-RelWithDebInfo}
  -B build
  -G Ninja
)

if [ -n "${CMAKE_TOOLCHAIN_FILE:-}" ]; then
  cmake_args+=("-DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}")
fi

cmake "${cmake_args[@]}"
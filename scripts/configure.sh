#!/bin/bash

cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_BUILD_TYPE:STRING=${CMAKE_BUILD_TYPE:-RelWithDebInfo} \
  -B build \
  -G Ninja

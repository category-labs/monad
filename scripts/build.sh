#!/bin/bash

VERBOSE=1 \
cmake \
  --build build \
  --config ${CMAKE_BUILD_TYPE:-RelWithDebInfo} \
  --target all

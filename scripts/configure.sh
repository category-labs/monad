#!/bin/bash

cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DBoost_USE_STATIC_LIBS=ON \
  -B build \
  -G Ninja

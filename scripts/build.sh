#!/bin/bash

VERBOSE=1 \
cmake \
  --build build \
  --config RelWithDebInfo \
  --target all

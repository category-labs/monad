#!/bin/bash

VERBOSE=1 \
cmake \
  --build build \
  --config RelWithDebInfo \
  --target vm-unit-tests \
  --target compiler-blockchain-tests \
  --target llvm-blockchain-tests \
  --target interpreter-blockchain-tests

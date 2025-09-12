#!/usr/bin/env bash

set -euxo pipefail

export UBSAN_OPTIONS="halt_on_error=1"
ulimit -s 131072

if [[ $SKIP_LLVM_TESTS == false ]]; then
  ./build/test/vm/blockchain/llvm-blockchain-tests
else
  echo skipping llvm tests
fi

./build/test/vm/unit/vm-unit-tests
./build/test/vm/blockchain/compiler-blockchain-tests
./build/test/vm/blockchain/interpreter-blockchain-tests



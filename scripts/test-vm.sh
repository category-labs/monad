#!/usr/bin/env bash

set -euxo pipefail

export UBSAN_OPTIONS="halt_on_error=1"
ulimit -s 131072

./build/category/vm/test/unit/vm-unit-tests
./build/category/vm/test/blockchain/compiler-blockchain-tests
./build/category/vm/test/blockchain/interpreter-blockchain-tests
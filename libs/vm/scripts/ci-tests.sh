#!/usr/bin/env bash

set -euxo pipefail

export UBSAN_OPTIONS="halt_on_error=1"
ulimit -s 131072

./build/test/unit/unit-tests
./build/test/blockchain/compiler-blockchain-tests
./build/test/blockchain/interpreter-blockchain-tests
#!/usr/bin/env bash

set -euxo pipefail

export UBSAN_OPTIONS="halt_on_error=1"
ulimit -s 131072

# Exclude tests that expect 0xDE (PLOAD) and 0xDF (PSTORE) to be invalid opcodes
# These opcodes are valid MONAD-specific opcodes
EXCLUDE_FILTER="-*opcDEDiffPlaces:*opcDFDiffPlaces:*testOpcode_d0"

./build/test/vm/unit/vm-unit-tests
./build/test/vm/blockchain/compiler-blockchain-tests --gtest_filter="$EXCLUDE_FILTER"
./build/test/vm/blockchain/interpreter-blockchain-tests --gtest_filter="$EXCLUDE_FILTER"

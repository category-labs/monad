#!/usr/bin/env bash

set -euxo pipefail

export UBSAN_OPTIONS="halt_on_error=1"
export LSAN_OPTIONS="suppressions=$(dirname "$0")/lsan.supp"
ulimit -s 131072

./build/test/vm/unit/vm-unit-tests


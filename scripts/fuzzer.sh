#!/usr/bin/env bash

root_dir=`dirname "$0"`/..
fuzzer="$root_dir"/build/category/vm/test/fuzzer/monad-compiler-fuzzer

MONAD_COMPILER_FUZZING=1 exec -a "$0" "$fuzzer" $@

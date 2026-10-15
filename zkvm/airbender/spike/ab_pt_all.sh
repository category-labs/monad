#!/bin/bash
# Per-precompile scoreboard: ab_pt_all.sh <elf>
# (the vectors: zkvm/test/precompile_tests' blob, in work/airbender/out)
cd "$(dirname "$0")"
VEC=${VEC:-${MONAD_ZKVM_WORK:-../../../../..}/airbender/out/precompile_vectors.bin}
for a in ${ADDRS:-1 2 3 5 6 7 8 9 a b c d e f 10 11 100}; do
  printf "0x%-4s " $a; python3 ab_pt.py "$1" "$VEC" $a 2>&1 | head -1
done

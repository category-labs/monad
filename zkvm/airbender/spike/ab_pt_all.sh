#!/bin/bash
# Per-precompile scoreboard: ab_pt_all.sh <elf>
cd "$(dirname "$0")"
for a in 1 2 3 5 6 7 8 9 a b c d e f 10 11 100; do
  printf "0x%-4s " $a; python3 ab_pt.py "$1" out/precompile_vectors.bin $a 2>&1 | head -1
done

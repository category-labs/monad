#!/bin/bash
# Builds keccak_align_test.cpp (the guest's keccak at every offset in a word
# against an aligned copy) into a guest ELF and runs it in the runner.
set -e
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
W=${MONAD_ZKVM_WORK:-$REPO/../..}/airbender
TC=${TC_DIR:-$HOME/.local/xPacks/xpack-riscv-none-elf-gcc-15.2.0-1}/bin/riscv-none-elf
$TC-g++ -march=rv32im_zicsr -mabi=ilp32 -mstrict-align -mcmodel=medany -O2 -w -std=gnu++23 \
  -fno-exceptions -fno-rtti -fno-pic "-D__INT32_TYPE__=int" "-D__UINT32_TYPE__=unsigned int" \
  "-D__INT_LEAST32_TYPE__=int" "-D__UINT_LEAST32_TYPE__=unsigned int" \
  -c $REPO/zkvm/airbender/spike/keccak_align_test.cpp -o $W/out/keccak_align_test.o
OUT=$W/out/keccak_align_test.elf $REPO/zkvm/airbender/spike/link.sh $W/out/keccak_align_test.o $W/out/stubs.o > /dev/null
$TC-objcopy -O binary $W/out/keccak_align_test.elf $W/out/keccak_align_test.bin
$TC-objcopy -O binary --only-section=.text $W/out/keccak_align_test.elf $W/out/keccak_align_test.text
echo -n "00000000" > $W/out/empty.hex
$W/stack/airbender-platform/target/release/monad-airbender-runner run $W/out/keccak_align_test.bin \
  --input $W/out/empty.hex --text-path $W/out/keccak_align_test.text 2>&1 | grep -v AIRBENDER_COUNTERS

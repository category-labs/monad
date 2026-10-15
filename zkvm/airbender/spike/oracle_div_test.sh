#!/bin/bash
# Builds oracle_div_test.cpp into a guest ELF (the test in place of the
# guest's entry) and runs it in zkvm/airbender/runner: the output words are
# checks, failures and the first failing case (0xffffffff if none).
#   usage: oracle_div_test.sh [runner options, e.g. --corrupt 5:inc]
# Needs the guest library built (build-rv32) and the runner built.
set -e
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
W=${MONAD_ZKVM_WORK:-$REPO/../..}/airbender
TC=${TC_DIR:-$HOME/.local/xPacks/xpack-riscv-none-elf-gcc-15.2.0-1}/bin/riscv-none-elf
FLAGS=(-march=rv32im_zicsr -mabi=ilp32 -mstrict-align -mcmodel=medany -O3 -w -std=gnu++23
       -fno-exceptions -fno-rtti -ffunction-sections -fdata-sections -fno-pic
       -DMONAD_ZKVM_AIRBENDER -DNDEBUG
       "-D__INT32_TYPE__=int" "-D__UINT32_TYPE__=unsigned int"
       "-D__INT_LEAST32_TYPE__=int" "-D__UINT_LEAST32_TYPE__=unsigned int"
       -I$REPO/zkvm -I$REPO -I$REPO/third_party/evmc/include -I/opt/homebrew/include)
$TC-g++ "${FLAGS[@]}" -c $REPO/zkvm/airbender/spike/oracle_div_test.cpp -o $W/out/oracle_div_test.o
OUT=$W/out/oracle_div_test.elf $REPO/zkvm/airbender/spike/link.sh $W/out/oracle_div_test.o $W/out/stubs.o > /dev/null
$TC-objcopy -O binary $W/out/oracle_div_test.elf $W/out/oracle_div_test.bin
$TC-objcopy -O binary --only-section=.text $W/out/oracle_div_test.elf $W/out/oracle_div_test.text
echo -n "00000000" > $W/out/empty.hex
$W/stack/airbender-platform/target/release/monad-airbender-runner run $W/out/oracle_div_test.bin \
  --input $W/out/empty.hex --text-path $W/out/oracle_div_test.text "$@" 2>&1 | grep -v AIRBENDER_COUNTERS

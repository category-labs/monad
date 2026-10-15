#!/bin/bash
# Link the Airbender spike guest: runtime + guest archive + libgcc.
# usage: link.sh [extra objects...]   -> out/guest.elf, out/guest.map
set -e
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
W=${MONAD_ZKVM_WORK:-$REPO/../..}/airbender
TC=${TC_DIR:-$HOME/.local/xPacks/xpack-riscv-none-elf-gcc-15.2.0-1}/bin/riscv-none-elf
RT=$REPO/zkvm/airbender
FLAGS=(-march=rv32im_zicsr -mabi=ilp32 -mstrict-align -mcmodel=medany -O2 -ffunction-sections -fdata-sections -fno-pic
       "-D__INT32_TYPE__=int" "-D__UINT32_TYPE__=unsigned int" "-D__INT_LEAST32_TYPE__=int" "-D__UINT_LEAST32_TYPE__=unsigned int")
mkdir -p $W/out
$TC-gcc "${FLAGS[@]}" -w -c $RT/start.S -o $W/out/start.o
$TC-gcc "${FLAGS[@]}" -ffreestanding -fno-builtin -w ${RT_CFLAGS:-} -c $RT/runtime.c -o $W/out/runtime.o
$TC-gcc -march=rv32im_zicsr -mabi=ilp32 -nostdlib -nostartfiles -static \
  -T ${LINKX:-$RT/link.x} -Wl,--gc-sections -Wl,-Map=${OUT:-$W/out/guest.elf}.map \
  -o ${OUT:-$W/out/guest.elf} $W/out/start.o $W/out/runtime.o "$@" \
  ${GUESTLIB:-$W/build-rv32/libmonad-zkvm-guest-airbender.a} ${RUSTLIB:-} -lgcc
echo "linked ${OUT:-$W/out/guest.elf}"

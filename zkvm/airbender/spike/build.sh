#!/bin/bash
# Spike build of the Airbender guest: configure + build the rv32im archive,
# link it with the runtime and accelerator stubs, report ROM use and any
# instruction Airbender cannot prove.
#   usage: zkvm/airbender/spike/build.sh <out_dir> [MONAD_ETH_OSAKA]
# Needs: xPack riscv-none-elf-gcc 15.2 (TC_DIR), brew Boost (CMAKE_PREFIX_PATH),
# and work/fatal_hook.h (BOOST_OUTCOME_SYSTEM_ERROR2_FATAL -> trap) as FATAL_HOOK.
set -e
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
OUT=$(mkdir -p "$1" && cd "$1" && pwd)
REV=${2:-}
TC_DIR=${TC_DIR:-$HOME/.local/xPacks/xpack-riscv-none-elf-gcc-15.2.0-1}
TC=$TC_DIR/bin/riscv-none-elf
FATAL_HOOK=${FATAL_HOOK:-$REPO/../../fatal_hook.h}
BUILD=$OUT/build
CFLAGS="-w" CXXFLAGS="-w -include $FATAL_HOOK" cmake -G Ninja -S "$REPO/zkvm/guest" -B "$BUILD" \
  -DMONAD_ZKVM_GUEST_TARGET=airbender ${REV:+-DMONAD_ZKVM_EVM_REV=$REV} \
  -DCMAKE_TOOLCHAIN_FILE="$REPO/category/core/toolchains/riscv32-elf.cmake" \
  -DRISCV_TOOLCHAIN_DIR="$TC_DIR" -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_PREFIX_PATH=${CMAKE_PREFIX_PATH:-/opt/homebrew} > "$OUT/configure.log"
ninja -C "$BUILD" monad-zkvm-guest-airbender > "$OUT/build.log"
FLAGS=(-march=rv32im_zicsr -mabi=ilp32 -mstrict-align -mcmodel=medany -O2 -w
       -ffunction-sections -fdata-sections -fno-pic
       "-D__INT32_TYPE__=int" "-D__UINT32_TYPE__=unsigned int"
       "-D__INT_LEAST32_TYPE__=int" "-D__UINT_LEAST32_TYPE__=unsigned int")
$TC-gcc "${FLAGS[@]}" -c "$REPO/zkvm/airbender/start.S" -o "$OUT/start.o"
$TC-gcc "${FLAGS[@]}" -ffreestanding -fno-builtin -c "$REPO/zkvm/airbender/runtime.c" -o "$OUT/runtime.o"
$TC-gcc "${FLAGS[@]}" -c "$REPO/zkvm/airbender/spike/stubs.c" -o "$OUT/stubs.o"
$TC-gcc -march=rv32im_zicsr -mabi=ilp32 -nostdlib -nostartfiles -static \
  -T "$REPO/zkvm/airbender/link.x" -Wl,--gc-sections -Wl,-Map="$OUT/guest.map" \
  -o "$OUT/guest.elf" "$OUT/start.o" "$OUT/runtime.o" "$OUT/stubs.o" \
  "$BUILD/libmonad-zkvm-guest-airbender.a" -lgcc
$TC-size -A "$OUT/guest.elf" | awk '$1 ~ /^\.(text|rodata|data)$/ {printf "%-8s %9d\n", $1, $2; s+=$2} END {printf "ROM      %9d bytes (%.2f of 4 MiB)\n", s, s/1048576}'
$TC-objdump -d --no-show-raw-insn "$OUT/guest.elf" > "$OUT/guest.dis"
echo "instructions: $(grep -cE '^\s+[0-9a-f]+:\s' "$OUT/guest.dis")"
echo "signed mul/div (unprovable): $(grep -cE '^\s+[0-9a-f]+:\s+(mulh|mulhsu|div|rem)\s' "$OUT/guest.dis" || true)"
echo "ebreak/ecall/fence/atomics: $(grep -cE '^\s+[0-9a-f]+:\s+(ebreak|ecall|fence|lr\.|sc\.|amo)' "$OUT/guest.dis" || true)"

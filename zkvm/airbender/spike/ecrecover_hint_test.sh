#!/bin/bash
# Builds the accel crate's ecrecover self-test (feature ecrecover-selftest:
# the hinted recovery against the default hooks, see accel/src/lib.rs) into a
# guest ELF and runs it in zkvm/airbender/runner. The output words are the
# cases, the disagreements, the keys recovered and the first disagreement
# (0xffffffff if none).
#   usage: ecrecover_hint_test.sh [runner options, e.g. --corrupt 1:flag]
set -e
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
W=${MONAD_ZKVM_WORK:-$REPO/../..}/airbender
ACCEL=$REPO/zkvm/airbender/accel
TC=${TC_DIR:-$HOME/.local/xPacks/xpack-riscv-none-elf-gcc-15.2.0-1}/bin/riscv-none-elf
(cd $ACCEL && CARGO_TARGET_DIR=$ACCEL/target-selftest cargo +nightly-2026-08-09 build -q --release \
   --target riscv32im-unknown-none-elf --features ecrecover-selftest)
GUESTLIB=$ACCEL/target-selftest/riscv32im-unknown-none-elf/release/libmonad_zkvm_airbender_accel.a \
  RUSTLIB= OUT=$W/out/ecrecover_selftest.elf $REPO/zkvm/airbender/spike/link.sh > /dev/null
$TC-objcopy -O binary $W/out/ecrecover_selftest.elf $W/out/ecrecover_selftest.bin
$TC-objcopy -O binary --only-section=.text $W/out/ecrecover_selftest.elf $W/out/ecrecover_selftest.text
echo -n "00000000" > $W/out/empty.hex
$W/stack/airbender-platform/target/release/monad-airbender-runner run $W/out/ecrecover_selftest.bin \
  --input $W/out/empty.hex --text-path $W/out/ecrecover_selftest.text "$@" 2>&1 | grep -v AIRBENDER_COUNTERS

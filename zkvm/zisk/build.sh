#!/usr/bin/env bash
# Build the ZisK guest ELF through cargo-zisk.
#
#   zkvm/zisk/build.sh [--official]
#
# --official  the reference configuration for published benchmarks and
#             releases: a clean worktree, the HEAD commit and GCC 15.2.0.
# (default)   the development profile.
#
# Requires CMake and Python 3.
# Environment: RISCV_TOOLCHAIN_DIR (default ~/.local/xPacks/zisk-dma-gcc-15.2.0),
# CARGO_ZISK (default ~/.zisk/bin/cargo-zisk), CMAKE_PREFIX_PATH for Boost
# (default /usr).
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OFFICIAL=0
for arg in "$@"; do
    case $arg in
        --official) OFFICIAL=1 ;;
        -h | --help) sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
        *) echo "unknown argument: $arg (see --help)" >&2; exit 2 ;;
    esac
done

TC=${RISCV_TOOLCHAIN_DIR:-$HOME/.local/xPacks/zisk-dma-gcc-15.2.0}
if test -x "$TC/bin/riscv64-none-elf-g++"; then
    PREFIX=riscv64-none-elf-
elif test -x "$TC/bin/riscv64-unknown-elf-g++"; then
    PREFIX=riscv64-unknown-elf-
elif test -x "$TC/bin/riscv-none-elf-g++"; then
    PREFIX=riscv-none-elf-
else
    echo "missing RISC-V g++ under $TC/bin" >&2
    exit 1
fi

if [ "$OFFICIAL" = 1 ]; then
    test -z "$(git -C "$REPO" status --porcelain --untracked-files=normal)" || {
        echo "official build requires a clean worktree, including untracked files" >&2
        exit 1
    }
    COMMIT=$(git -C "$REPO" rev-parse HEAD)
fi

CARGO_ZISK=${CARGO_ZISK:-$HOME/.zisk/bin/cargo-zisk}
test -x "$CARGO_ZISK" || {
    echo "missing cargo-zisk: $CARGO_ZISK" >&2
    exit 1
}
export RISCV_TOOLCHAIN_DIR=$TC
export CC_riscv64ima_zisk_zkvm_elf=$TC/bin/${PREFIX}gcc
export CXX_riscv64ima_zisk_zkvm_elf=$TC/bin/${PREFIX}g++
if [ "$OFFICIAL" = 1 ]; then
    export MONAD_ZKVM_OFFICIAL_PROFILE=ON
    export MONAD_ZKVM_GIT_COMMIT=$COMMIT
else
    unset MONAD_ZKVM_OFFICIAL_PROFILE
fi
cd "$HERE"
"$CARGO_ZISK" build --release
ELF=$HERE/target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk
test -f "$ELF" || {
    echo "ELF not found: $ELF" >&2
    exit 1
}

echo "$ELF"

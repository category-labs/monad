#!/usr/bin/env bash
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
TC=${RISCV_TOOLCHAIN_DIR:-$HOME/.local/xPacks/zisk-dma-gcc-15.2.0}
CARGO_ZISK=${CARGO_ZISK:-$HOME/.zisk/bin/cargo-zisk}
COMMIT=$(git -C "$REPO" rev-parse HEAD)

test -x "$CARGO_ZISK" || { echo "missing cargo-zisk: $CARGO_ZISK" >&2; exit 1; }
if test -x "$TC/bin/riscv64-unknown-elf-g++"; then
    PREFIX=riscv64-unknown-elf-
elif test -x "$TC/bin/riscv64-none-elf-g++"; then
    PREFIX=riscv64-none-elf-
else
    echo "missing RISC-V g++ under $TC/bin" >&2
    exit 1
fi

export RISCV_TOOLCHAIN_DIR=$TC
export CC_riscv64ima_zisk_zkvm_elf=$TC/bin/${PREFIX}gcc
export CXX_riscv64ima_zisk_zkvm_elf=$TC/bin/${PREFIX}g++
export MONAD_ZKVM_GIT_COMMIT=$COMMIT
export MONAD_ZKVM_CMAKE_DEFINES="MONAD_ZKVM_OFFICIAL_PROFILE=ON;MONAD_ZKVM_GIT_COMMIT=$COMMIT;MONAD_ZKVM_ZISK_DMA=ON;MONAD_ZKVM_TABLE_ARG=ON;MONAD_ZKVM_KECCAKF_MEMO=ON;MONAD_ZKVM_FUSE=ON;MONAD_ZKVM_KECCAK_SITES=OFF;MONAD_ZKVM_SELFTEST=OFF"

cd "$HERE"
"$CARGO_ZISK" build --release

ELF=$HERE/target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk
test -f "$ELF" || { echo "official ELF not found: $ELF" >&2; exit 1; }

BUILD_ROOT=$HERE/target/elf/riscv64ima-zisk-zkvm-elf/release/build
MANIFEST=${MONAD_ZKVM_MANIFEST:-$ELF.build.json}

python3 "$HERE/audit-official-build.py" \
    --elf "$ELF" --build-root "$BUILD_ROOT" --repo "$REPO" --manifest "$MANIFEST"

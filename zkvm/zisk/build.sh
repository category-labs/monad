#!/usr/bin/env bash
# Build the ZisK guest: the linked ELF through cargo-zisk, or the guest
# archive alone through CMake.
#
#   zkvm/zisk/build.sh [--official] [--archive] [-DNAME=VALUE ...]
#
# --official  the reference configuration for published benchmarks and
#             releases: MONAD_ZKVM_OFFICIAL_PROFILE, a clean worktree, the
#             HEAD commit, patched GCC 15.2.0. The ELF is audited after the
#             link (audit-official-build.py) and gets its <elf>.build.json.
#             Takes no -D arguments: the profile fixes its configuration.
# (default)   the development profile, for A/B experiments. -DNAME=VALUE
#             arguments reach the guest's CMake configuration, e.g.
#             -DMONAD_ZKVM_ZISK_DMA=OFF.
# --archive   build libmonad-zkvm-guest-zisk.a without Rust or cargo-zisk,
#             using the same build_archive.py helper as Cargo.
#             test-build-archive.sh compares the two archives.
#
# Requires CMake and Python 3.
# Environment: RISCV_TOOLCHAIN_DIR (default ~/.local/xPacks/zisk-dma-gcc-15.2.0),
# CARGO_ZISK (default ~/.zisk/bin/cargo-zisk), CMAKE_PREFIX_PATH for Boost
# (default /usr), MONAD_ZKVM_MANIFEST for the official manifest's path.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OFFICIAL=0
ARCHIVE=0
DEFS=()
for arg in "$@"; do
    case $arg in
        --official) OFFICIAL=1 ;;
        --archive) ARCHIVE=1 ;;
        -D?*=*) DEFS+=("$arg") ;;
        -h | --help) sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
        *) echo "unknown argument: $arg (see --help)" >&2; exit 2 ;;
    esac
done
if [ "$OFFICIAL" = 1 ] && [ ${#DEFS[@]} -gt 0 ]; then
    echo "--official takes no -D arguments: the profile fixes its configuration" >&2
    exit 2
fi

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

export RISCV_TOOLCHAIN_DIR=$TC
export CC_riscv64ima_zisk_zkvm_elf=$TC/bin/${PREFIX}gcc
export CXX_riscv64ima_zisk_zkvm_elf=$TC/bin/${PREFIX}g++
if [ "$OFFICIAL" = 1 ]; then
    export MONAD_ZKVM_OFFICIAL_PROFILE=ON
    export MONAD_ZKVM_GIT_COMMIT=$COMMIT
    unset MONAD_ZKVM_CMAKE_ARGS
else
    unset MONAD_ZKVM_OFFICIAL_PROFILE
    # Preserve argument boundaries, including spaces and quotes in values.
    MONAD_ZKVM_CMAKE_ARGS=$(python3 -c \
        'import shlex, sys; print(shlex.join(sys.argv[1:]))' ${DEFS[@]+"${DEFS[@]}"})
    export MONAD_ZKVM_CMAKE_ARGS
fi
if [ "$ARCHIVE" = 1 ]; then
    exec python3 "$REPO/zkvm/build-support/build_archive.py"
fi

CARGO_ZISK=${CARGO_ZISK:-$HOME/.zisk/bin/cargo-zisk}
test -x "$CARGO_ZISK" || {
    echo "missing cargo-zisk: $CARGO_ZISK" >&2
    exit 1
}
cd "$HERE"
"$CARGO_ZISK" build --release
ELF=$HERE/target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk
test -f "$ELF" || {
    echo "ELF not found: $ELF" >&2
    exit 1
}
if [ "$OFFICIAL" = 1 ]; then
    python3 "$HERE/audit-official-build.py" \
        --elf "$ELF" \
        --build-root "$HERE/target/guest-build" \
        --repo "$REPO" \
        --cargo-zisk "$CARGO_ZISK" \
        --manifest "${MONAD_ZKVM_MANIFEST:-$ELF.build.json}"
fi
echo "$ELF"

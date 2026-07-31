#!/bin/bash
set -euo pipefail

REPO="https://github.com/riscv-collab/riscv-gnu-toolchain"
BRANCH="2026.05.06"
SRC="/riscv-gnu-toolchain"
PREFIX="/root/riscv"

git clone --depth 1 --branch "${BRANCH}" "${REPO}" "${SRC}"
cd "${SRC}"

# Multilib: rv64ima/lp64 is the default variant (ZisK) and rv64im/lp64 covers
# SP1, which has no atomics; both are served by the rv64 default plus flags. The
# rv32im/ilp32 variant exists for OpenVM, which is a 32-bit ISA — without it the
# compiler still accepts -march=rv32im -mabi=ilp32, but -print-file-name and
# -print-libgcc-file-name hand back the rv64 libc.a/libgcc.a, and the newlib and
# libgcc objects the guest archive extracts from them (setjmp, strcmp,
# __popcountdi2) are then the wrong ABI and will not link.
./configure --prefix="${PREFIX}" \
  --with-arch=rv64ima \
  --with-abi=lp64 \
  --with-multilib-generator="rv64ima-lp64--;rv32im-ilp32--"

# Fetch the submodules the newlib toolchain needs, one at a time, before the
# parallel build starts. Two reasons, both of which fail the build on a cold
# tree otherwise:
#   - `make -j` clones several submodules at once and sourceware.org answers
#     HTTP 429 (rate limited).
#   - the pinned submodule commits are not branch tips, so a shallow clone does
#     not contain them; git then asks sourceware for those exact commits, which
#     it refuses. These are deliberately full clones for that reason.
# Listed explicitly because the repo also carries qemu, llvm, glibc and musl
# submodules that this toolchain does not need.
for _module in binutils gcc newlib gdb; do
    git -C "${SRC}" submodule update --init "${_module}"
done

make -j"$(nproc)"

# Keep the cross compiler in lockstep with the x86 host compiler.
HOST_CC="${CC:-gcc-15}"
HOST_VERSION="$("${HOST_CC}" -dumpfullversion)"
CROSS_VERSION="$("${PREFIX}/bin/riscv64-unknown-elf-gcc" -dumpfullversion)"
if [ "${CROSS_VERSION}" != "${HOST_VERSION}" ]; then
    echo "error: cross compiler GCC ${CROSS_VERSION} does not match host" \
        "${HOST_CC} GCC ${HOST_VERSION}; update BRANCH (currently ${BRANCH})" \
        "to a tag whose GCC matches the host, or align the host compiler." >&2
    exit 1
fi

# Strip debug info from the installed toolchain (kept artifacts).
find "${PREFIX}" -type f -executable -exec strip --strip-unneeded {} + 2>/dev/null || true

# Remove the entire build tree — only ${PREFIX} is consumed downstream.
cd /
rm -rf "${SRC}"

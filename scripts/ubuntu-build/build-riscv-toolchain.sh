#!/bin/bash
set -euo pipefail

REPO="https://github.com/riscv-collab/riscv-gnu-toolchain"
BRANCH="2026.05.06"
SRC="/riscv-gnu-toolchain"
PREFIX="/root/riscv"

git clone --depth 1 --branch "${BRANCH}" "${REPO}" "${SRC}"
cd "${SRC}"

./configure --prefix="${PREFIX}" \
  --with-arch=rv64ima \
  --with-abi=lp64

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

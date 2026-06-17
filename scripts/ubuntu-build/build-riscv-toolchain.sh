#!/bin/bash
set -euo pipefail

REPO="https://github.com/riscv-collab/riscv-gnu-toolchain"
BRANCH="2026.06.06"
SRC="/riscv-gnu-toolchain"
PREFIX="/root/riscv"

git clone --depth 1 --branch "${BRANCH}" "${REPO}" "${SRC}"
cd "${SRC}"

./configure --prefix="${PREFIX}" \
  --with-arch=rv64ima \
  --with-abi=lp64

make -j"$(nproc)"

# Strip debug info from the installed toolchain (kept artifacts).
find "${PREFIX}" -type f -executable -exec strip --strip-unneeded {} + 2>/dev/null || true

# Remove the entire build tree — only ${PREFIX} is consumed downstream.
cd /
rm -rf "${SRC}"

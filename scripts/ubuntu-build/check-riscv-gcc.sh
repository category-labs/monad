#!/bin/bash

set -euo pipefail

HOST_CC="${CC:-gcc-15}"
HOST_VERSION="$("${HOST_CC}" -dumpfullversion)"
CROSS_VERSION="$("/riscv/bin/riscv64-none-elf-gcc" -dumpfullversion)"
if [ "${CROSS_VERSION}" != "${HOST_VERSION}" ]; then
    echo "error: cross compiler GCC ${CROSS_VERSION} does not match host" \
         "${HOST_CC} GCC ${HOST_VERSION}; update following the directions" \
         "in nix/README.md." >&2
    exit 1
fi

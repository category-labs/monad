#!/usr/bin/env bash
# Check that a GCC carrying the patches in this directory changes generated
# code the way the guest relies on, not merely that it accepts the options:
# compile each probe with its option and require the assembly the probe
# documents.
#
#   check-probes.sh <riscv64 gcc>
set -euo pipefail

gcc=${1:?usage: $0 <riscv64 gcc>}
here=$(cd "$(dirname "$0")" && pwd)
flags=(-O2 -march=rv64ima_zicsr -mabi=lp64 -mcmodel=medany)
asm=$(mktemp -d)
trap 'rm -r "$asm"' EXIT

"$gcc" "${flags[@]}" -mzisk-dma -S -o "$asm/dma.s" "$here/probe-dma.c"
if ! grep -Eq 'csrs?[[:space:]]+.*0x813' "$asm/dma.s"; then
    cat "$asm/dma.s"
    echo "-mzisk-dma emits no DMA marker for a block memcpy" >&2
    exit 1
fi

"$gcc" "${flags[@]}" -mzisk-clean-byte-stores -S -o "$asm/byte.s" \
    "$here/probe-byte-stores.c"
if ! grep -Eq 'li[[:space:]]+[a-z0-9]+,184$' "$asm/byte.s" ||
    ! grep -Eq 'addi[[:space:]]+[a-z0-9]+,[a-z0-9]+,128$' "$asm/byte.s"; then
    cat "$asm/byte.s"
    echo "-mzisk-clean-byte-stores leaves a byte store's source sign-extended" >&2
    exit 1
fi

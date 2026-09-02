# ZisK DMA lowering for GCC

These patches add `-mzisk-dma` to GCC's RISC-V backend, translating block memory
operations into ZisK DMA markers. They mirror the LLVM patch in ZisK's Rust fork
(`src/llvm-patches/0001-riscv-zisk-dma-lowering.patch`, enabled by `+zisk-dma`).

DMA lowering is off by default (`MONAD_ZKVM_ZISK_DMA=OFF`). The official ZisK
profile requires it: it forces the option on, rejects an explicit `OFF`, and
checks that a `memcpy` probe compiles to a DMA marker.

## Why the guest wants it

For `memcpy`, the compiler emits two adjacent markers. ZisK's cost depends on
whether the length is an immediate or a register:

| form | transpiles to | steps |
|---|---|---|
| `csrs 0x813,src` + `addi x0,dst,IMM` | count in the extended argument | 1 |
| `csrs 0x813,src` + `add x0,dst,reg` | count first written to `EXTRA_PARAMS_ADDR` | 2 |

Emitting these markers directly avoids the `ziskos` wrapper's call and return,
and lets a known length use the cheaper immediate form when it fits.

## The files

| File | Purpose |
|---|---|
| `0001-riscv-zisk-dma-lowering-14.3.0.patch` | the upstream patch, against GCC 14.3.0 |
| `0002-riscv.md-forward-port-15.2.0.diff` | adapts the memory patterns to GCC 15.2.0 |
| `build-gcc15.sh` | builds the compiler and verifies the lowering |

The interpreter needs GCC 15's `__attribute__((musttail))`. Keeping the original
14.3.0 patch separate from its 15.2.0 adaptation preserves its provenance.

## Building the compiler

Requires GCC 15.2.0 sources, the matching xPack, and host `gcc-13`/`g++-13`.
Apply both patches to GCC, then run the build script:

```bash
cd gcc-15.2.0
patch -p1 < .../0001-riscv-zisk-dma-lowering-14.3.0.patch   # applies with fuzz
patch -p1 < .../0002-riscv.md-forward-port-15.2.0.diff
ZISK_DMA_GCC_SRC=$PWD .../build-gcc15.sh
```

The script expects patched sources. It builds only GCC, reuses xPack's binutils,
headers and RV64 libraries, then compiles a 32-byte copy with `-mzisk-dma`.
The check requires `csrs 0x813` in the assembly, not just acceptance of the flag.

For official builds requesting `-mzisk-dma`, CMake also compiles a `memcpy` probe
and requires the DMA marker. It includes the two patches' combined SHA-256 in
`MONAD_ZKVM_BUILD_SIGNATURE` and the CMake profile JSON, identifying their content
independently of the compiler binary.

## Upstreaming

These patches belong beside ZisK's LLVM implementation. They are kept here so
the guest's compiler can be rebuilt from GCC sources and the matching xPack.

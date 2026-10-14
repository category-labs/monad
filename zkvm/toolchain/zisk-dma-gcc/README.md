# ZisK patches for GCC

These patches add two options to GCC's RISC-V backend:

- `-mzisk-dma` translates block memory operations into ZisK DMA markers. It
  mirrors the LLVM patch in ZisK's Rust fork
  (`src/llvm-patches/0001-riscv-zisk-dma-lowering.patch`, enabled by `+zisk-dma`).
- `-mzisk-clean-byte-stores` uses zero-extended byte constants and addition
  immediates to reduce ZisK's arithmetic and byte-store costs.

Both are off by default (`MONAD_ZKVM_ZISK_DMA=OFF`,
`MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES=OFF`). The official ZisK profile requires
them: it forces both options on, rejects an explicit `OFF`, and checks that a
probe compiles to the expected code for each.

## Why the guest wants DMA lowering

For `memcpy`, the compiler emits two adjacent markers. ZisK's cost depends on
whether the length is an immediate or a register:

| form | transpiles to | steps |
|---|---|---|
| `csrs 0x813,src` + `addi x0,dst,IMM` | count in the extended argument | 1 |
| `csrs 0x813,src` + `add x0,dst,reg` | count first written to `EXTRA_PARAMS_ADDR` | 2 |

Emitting these markers directly avoids the `ziskos` wrapper's call and return,
and lets a known length use the cheaper immediate form when it fits.

## Why the guest wants clean byte stores

ZisK prices a byte store by its whole source register: 66 cells when the
register holds a value below 0x100, 193 otherwise, as the prover then reads the
surrounding word. GCC sets the upper bits in two common cases:

| source | GCC | with `-mzisk-clean-byte-stores` |
|---|---|---|
| `*p = 0xb8` | `li a5,-72` | `li a5,184` |
| `*p = 0x80 + n` | `addiw a5,a1,-128` | `addi a5,a1,128` |

The low byte is unchanged. Small nonnegative operands can also use ZisK's
FROP path, avoiding the addition's arithmetic cost. This benefits byte
arithmetic such as PUSH-width computation, even without a store.

The option does not guarantee clear upper bits: a sum can exceed 255, and GCC
may still remove a mask such as `n & 0xff` before a byte store.

## The files

| File | Purpose |
|---|---|
| `0001-riscv-zisk-dma-lowering-14.3.0.patch` | the upstream patch, against GCC 14.3.0 |
| `0002-riscv.md-forward-port-15.2.0.diff` | adapts the memory patterns to GCC 15.2.0 |
| `0003-riscv-zisk-clean-byte-stores-15.2.0.diff` | adds `-mzisk-clean-byte-stores`, on top of the two above |
| `build-gcc15.sh` | builds the compiler and verifies both options |

The interpreter needs GCC 15's `__attribute__((musttail))`. Keeping the original
14.3.0 patch separate from its 15.2.0 adaptation preserves its provenance.

## Building the compiler

Requires GCC 15.2.0 sources, the matching xPack, and host `gcc-13`/`g++-13`.
Apply the three patches to GCC in order, then run the build script:

```bash
cd gcc-15.2.0
patch -p1 < .../0001-riscv-zisk-dma-lowering-14.3.0.patch   # applies with fuzz
patch -p1 < .../0002-riscv.md-forward-port-15.2.0.diff
patch -p1 < .../0003-riscv-zisk-clean-byte-stores-15.2.0.diff
ZISK_DMA_GCC_SRC=$PWD .../build-gcc15.sh
```

The script expects patched sources. It builds only GCC and reuses xPack's
binutils, headers and RV64 libraries. Assembly probes require `csrs 0x813`
for a 32-byte copy, `li ...,184` for a byte constant, and `addi ...,...,128`
for a byte addition.


## Upstreaming

These patches belong beside ZisK's LLVM implementation. They are kept here so
the guest's compiler can be rebuilt from GCC sources and the matching xPack.

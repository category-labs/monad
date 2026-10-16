# ZisK patches for GCC

These patches add two options to GCC's RISC-V backend:

- `-mzisk-dma` translates block memory operations into ZisK DMA markers. It
  mirrors the LLVM patch in ZisK's Rust fork
  (`src/llvm-patches/0001-riscv-zisk-dma-lowering.patch`, enabled by `+zisk-dma`).
- `-mzisk-clean-byte-stores` uses zero-extended byte constants and addition
  immediates to reduce ZisK's arithmetic and byte-store costs.

Both are off by default (`MONAD_ZKVM_ZISK_DMA=OFF`,
`MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES=OFF`). The official ZisK profile requires
them: it forces both options on and rejects an explicit `OFF`.

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
| `0001-riscv-zisk-dma-lowering.patch` | the upstream patch, written against GCC 14.3.0, with its context refreshed so it applies to 15.2.0 unchanged |
| `0002-riscv.md-forward-port-15.2.0.diff` | adapts the memory patterns to GCC 15.2.0 |
| `0003-riscv-zisk-clean-byte-stores-15.2.0.diff` | adds `-mzisk-clean-byte-stores`, on top of the two above |

## Building the compiler

`nix/riscv64-toolchain.nix` applies the three patches, in order, to the GCC
15.2.0 that nixpkgs builds for `riscv64-none-elf`, then checks the result
before the toolchain is usable: a 32-byte copy compiled with `-mzisk-dma`
must emit `csrs 0x813`, and a byte constant and a byte addition compiled
with `-mzisk-clean-byte-stores` must emit `li ...,184` and
`addi ...,...,128`. See `nix/README.md` for building and using it.

The interpreter needs GCC 15's `__attribute__((musttail))`. Keeping the
original patch separate from its 15.2.0 adaptation preserves its provenance:
only the context lines of the first file differ from the upstream patch.

## Upstreaming

These patches belong beside ZisK's LLVM implementation. They are kept here so
the guest's compiler can be rebuilt from GCC sources.

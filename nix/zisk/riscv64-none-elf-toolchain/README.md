# ZisK patches for GCC

Two patches add two options to GCC's RISC-V backend:

- `-mzisk-dma` translates block memory operations into ZisK DMA markers. It
  mirrors the LLVM patch in ZisK's Rust fork
  (`src/llvm-patches/0001-riscv-zisk-dma-lowering.patch`, enabled by `+zisk-dma`).
  The GCC version is maintained by ZisK in
  [ziskethone](https://github.com/0xPolygonHermez/ziskethone/tree/develop/cpp-guest/patches/gcc/gcc-15.2.0);
  `default.nix` here fetches it at a pinned commit.
- `-mzisk-clean-byte-stores` uses zero-extended byte constants and addition
  immediates to reduce ZisK's arithmetic and byte-store costs.

Both are off by default (`MONAD_ZKVM_ZISK_DMA=OFF`,
`MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES=OFF`). The reference Nix build enables
both explicitly. Its toolchain runs `check-probes.sh` to verify the expected
assembly for each option.

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
| ziskethone's `0001-riscv-zisk-dma-lowering.patch` (fetched, not vendored) | DMA lowering against GCC 15.2.0 |
| `patches/riscv-zisk-clean-byte-stores-15.2.0.diff` | adds `-mzisk-clean-byte-stores`, on top of the DMA patch |
| `tests/check-probes.sh` | verifies DMA and clean byte-store code generation with `probe-dma.c` and `probe-byte-stores.c` |
| `default.nix` | the toolchain package: patched GCC, binutils and soft-float newlib |

The interpreter needs GCC 15's `__attribute__((musttail))`. Earlier local
versions of the DMA patch, including the GCC 14.3.0 one, remain available in
Git history.

## Building the compiler

On x86_64 Linux, run from the repository root:

```bash
nix build .#riscv64-none-elf-toolchain
./result/bin/riscv64-none-elf-gcc --version
```

Nix pins GCC 15.2.0 from nixpkgs, applies the pinned ziskethone DMA patch and
then the vendored byte-store patch after nixpkgs's own, and provides binutils
and soft-float newlib. It runs `check-probes.sh` before
exposing the toolchain through `result`. The store path identifies the
compiler inputs, including both patches. See
[the Nix guide](../README.md) for setup and development commands.

## Upstreaming

The DMA patch now lives beside ZisK's LLVM implementation; updating it means
changing the pinned commit and hash in `default.nix`
and checking that the byte-store patch still applies on top. The byte-store
patch is kept here so the guest's compiler can be rebuilt from pinned GCC
sources with Nix.

The probes can also check a local compiler:

```bash
bash nix/zisk/riscv64-none-elf-toolchain/tests/check-probes.sh /path/to/riscv64-none-elf-gcc
```

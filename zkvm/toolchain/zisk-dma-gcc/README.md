# ZisK DMA lowering for GCC

The patch set that teaches the GCC RISC-V backend to lower block memory operations to ZisK's DMA
precompile markers instead of calling the `ziskos` mem\* thunks, plus the script that builds the
compiler. It is the GCC counterpart of the LLVM patch in ZisK's Rust fork
(`src/llvm-patches/0001-riscv-zisk-dma-lowering.patch`), which rustc reaches through the
`+zisk-dma` target feature.

The guest opts in with `-mzisk-dma`. Without the flag the compiler is the stock one, byte for byte.

## Why the guest wants it

The transpiler folds a `csrs 0x81x, src` marker and the `add`/`addi` after it into one DMA
operation, and the two forms do not cost the same:

| form | transpiles to | steps |
|---|---|---|
| `csrs 0x813,src` + `addi x0,dst,IMM` | one ZisK instruction, count in the extended arg | 1 |
| `csrs 0x813,src` + `add x0,dst,reg` | two — the first *writes* the count to `EXTRA_PARAMS_ADDR` | 2 |

A call into the `ziskos` thunk always pays the second form plus `jal` and `ret`, so a compile-time
length that reaches the precompile in place costs 1 step where the call costs 4.

## The files

| | |
|---|---|
| `0001-riscv-zisk-dma-lowering-14.3.0.patch` | the upstream patch, against GCC 14.3.0 |
| `0002-riscv.md-forward-port-15.2.0.diff` | `riscv.md` hunks whose context moved in 15.2.0 |
| `0003-guest-zicsr-15.2.0.patch` | the Zicsr guard the 15.2.0 backend needs |
| `build-gcc15.sh` | builds the compiler and verifies the lowering |

The forward port exists because upstream targets 14.3.0, which **cannot build this guest**: the
interpreter needs `__attribute__((musttail))`, which arrived in GCC 15. Both are kept rather than
consolidated into one 15.2.0 patch, so the provenance of the upstream half stays visible.

## Building the compiler

Apply the three in order to a GCC 15.2.0 source tree, then point the script at it:

```bash
cd gcc-15.2.0
patch -p1 < .../0001-riscv-zisk-dma-lowering-14.3.0.patch   # applies with fuzz
patch -p1 < .../0002-riscv.md-forward-port-15.2.0.diff
patch -p1 < .../0003-guest-zicsr-15.2.0.patch
ZISK_DMA_GCC_SRC=$PWD .../build-gcc15.sh
```

The script does not apply the patches; it refuses to run on a source tree where it cannot find
`riscv_zisk_expand_cpymem`. It builds only the compiler (`make all-gcc`) and grafts the target side
from the xPack the guest already uses, so binutils and headers match by construction. It then
compiles a witness translation unit with `-mzisk-dma` and fails unless the assembly contains
`csrs 0x813` — the flag parsing on its own is not evidence the lowering is present.

## Upstreaming

The natural home for this is ZisK itself, beside the LLVM patch it mirrors. Until it is there, it is
carried here so that the official guest profile is reproducible from this repository alone.

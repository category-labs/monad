# monad zkVM guest

Phase 0 scaffold for executing monad witnesses inside a zero-knowledge VM.
The C++ guest library is shared across backends. On ZisK a Rust guest crate
owns the entrypoint and the input/output ABI (via ziskos); on SP1 the
entrypoint (`program/main.c`) and the IO/accelerator ABI come from `libzkevm.a`,
leaving only the host-side driver in Rust.

## Layout

```
zkvm/
├── core/                 # bare-metal libc / libstdc++ shims and ABI headers
│   ├── zkvm_io.h         # eth-act standard I/O interface (read_input / write_output)
│   └── zkvm_halt.h
├── category/             # mirror tree shadowing host headers (BEFORE include path)
├── guest/                # C++ library called from every backend
│   ├── ffi.cpp           # stub monad_zkvm_execute_witness (Phase 0)
│   └── CMakeLists.txt
├── build-support/        # guest-build helpers (build_guest_lib / build_guest_elf)
├── zisk/                 # ZisK guest crate
└── sp1/                  # SP1 cargo workspace
    ├── program/          #   C guest entry (main.c)
    └── script/           #   host driver / prover (clap CLI)
```

Both backends drive the same C++ guest entry point: a parameterless
`monad_zkvm_execute_witness()` that reads the witness via `read_input` and
emits the post-state root via `write_output`, both from
[`zkvm_io.h`](core/zkvm_io.h). On ZisK the guest is a Rust crate and those
symbols are provided by `ziskos`; on SP1 there is no Rust guest — the entry is
`program/main.c`, and `read_input` / `write_output` (plus `_start`, the
allocator, and the `zkvm_*` accelerators) come from `libzkevm.a`, built from the
SP1 zkEVM SDK source at build time.

## Prerequisites

- A `riscv64-unknown-elf` (or `riscv64-none-elf`) GCC toolchain (e.g. installed
  under `~/riscv_gcc/`). Both backends locate it via the `RISCV_TOOLCHAIN_DIR`
  env var, set in a **local, gitignored** `zkvm/.cargo/config.toml`. This file
  is machine-specific and not checked in — create it before building:

  ```toml
  # zkvm/.cargo/config.toml
  [env]
  RISCV_TOOLCHAIN_DIR = "/absolute/path/to/riscv_gcc"
  ```

  (cargo merges `.cargo/config.toml` up the tree, so this one file covers both
  `zkvm/zisk` and `zkvm/sp1/script`.)
- [ZisK](https://github.com/0xPolygonHermez/zisk) ≥ v0.18.0
  (`ziskup` from <https://github.com/0xPolygonHermez/zisk>) — installs
  `cargo-zisk`, `ziskemu`.
- [SP1](https://docs.succinct.xyz/) ≥ v6.2.x (`sp1up` from
  <https://docs.succinct.xyz/getting-started/install.html>) — installs
  `cargo-prove` and the `+succinct` rust toolchain.

## ZisK

Build and run the guest in the emulator. ZisK expects inputs to be
length-prefixed: the first 8 bytes are the little-endian payload length,
followed by the payload itself.

```sh
# 1. Build the guest ELF.
cd zkvm/zisk
cargo-zisk build --release
#  → target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk

# 2. Wrap the witness with the 8-byte length prefix the emulator expects,
#    and zero-pad to an 8-byte multiple (ziskemu loads input as u64 words).
WITNESS=/path/to/witness.bin
python3 -c "
import struct, sys
p = open(sys.argv[1],'rb').read()
framed = struct.pack('<Q', len(p)) + p
framed += b'\x00' * ((-len(framed)) % 8)
sys.stdout.buffer.write(framed)
" $WITNESS > /tmp/zkvm-input.bin

# 3. Execute under the emulator. -o writes the public output buffer.
ziskemu \
    -e target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk \
    -i /tmp/zkvm-input.bin \
    -o /tmp/zkvm-output.bin

# 4. Inspect the computed state root (first 32 bytes of the output).
xxd /tmp/zkvm-output.bin | head -2
```

For proving, see ZisK's docs (`cargo-zisk prove ...`); the proving flow is
not exercised by Phase 0.

## SP1

The `script` crate is the host driver. Its `build.rs` builds the guest ELF as
part of its own build — cross-compiling the C++ guest archive and linking it
(plus `program/main.c`) against `libzkevm.a`, itself built from the SP1 zkEVM
SDK source — so you only run the script:

```sh
cd zkvm/sp1/script

# Execute (no proof).
cargo run --release -- --input /path/to/witness.bin
#  Output: 0x<32-byte hex>

# Generate and verify a proof. Use --profile prover for proving builds (see below).
cargo run --profile prover -- --input /path/to/witness.bin --prove

# Fast local iteration: skip real proving, use the mock prover.
SP1_PROVER=mock cargo run --release -- --input /path/to/witness.bin --prove
```

The default `release` profile disables LTO so relinking the host driver stays
fast (~20s vs ~4m) during iteration — the script binary statically links the
whole `sp1-sdk` prover graph, and fat LTO makes every relink a single-threaded
whole-program pass. **Any binary built for real proving should be compiled with
`--profile prover`**, which restores fat LTO + a single codegen unit for the
fastest proving runtime. Execution-only and mock-prover runs don't need it.

The `--input` path is read as raw bytes — no length prefix needed (SP1
takes care of framing internally via `SP1Stdin::write_vec`).

## Iterating on the C++ guest in isolation

The C++ guest library can be built independently of either Rust crate, for
fast iteration on `pipeline.cpp` / `execute_block_zkvm` (post-Phase 0):

```sh
cmake -B build-zkvm -S zkvm \
    -DCMAKE_TOOLCHAIN_FILE=$PWD/category/core/toolchains/riscv64-elf.cmake \
    -DRISCV_TOOLCHAIN_DIR=$HOME/riscv_gcc \
    -DMONAD_ZKVM_BACKEND=zisk \   # or sp1
    -DCMAKE_BUILD_TYPE=Release
cmake --build build-zkvm --target monad-zkvm-guest
```

The Rust crates pick this same target up through the
[`zkvm/build-support`](build-support/src/lib.rs) crate, which both
`zkvm/zisk/build.rs` and `zkvm/sp1/script/build.rs` delegate to.

## Testing

Besides block witnesses, both backends can be exercised against the
go-ethereum precompile golden vectors, which drive every crypto accelerator
directly — no witness needed. A test guest
([`precompile_test.cpp`](test/precompile_tests/precompile_test.cpp)) runs each
vector through the matching precompile `_execute` shim (which routes crypto
through the `zkvm_*` accelerators) and commits a pass/fail summary.

### 1. Generate the vector blob

[`gen_precompile_vectors.py`](test/precompile_tests/gen_precompile_vectors.py)
serializes the geth golden JSON (vendored at
`third_party/go-ethereum/core/vm/testdata/precompiles`) into a single binary
blob consumed by both backends. Run from the repo root:

```sh
python3 zkvm/test/precompile_tests/gen_precompile_vectors.py \
    third_party/go-ethereum/core/vm/testdata/precompiles \
    /tmp/pt-vectors.bin
#  → wrote 1847 cases, 3645425 bytes -> /tmp/pt-vectors.bin
# (pass --exclude 0x09,0x11 to skip specific precompile addresses)
```

### 2. Run on SP1

The `precompile-test` cargo feature swaps the witness executor for the test
guest (see [SP1](#sp1) above); the input is the vector blob:

```sh
cd zkvm/sp1/script
cargo run --release --features precompile-test -- --input /tmp/pt-vectors.bin
#  Output: 0x5052303137070000370700000000000000000000
```

### 3. Run on ZisK

ZisK builds the test guest as a separate binary
(`monad-zkvm-zisk-precompile-test`) and takes the same length-prefixed framing
as the witness run:

```sh
cd zkvm/zisk
cargo-zisk build --release --bin monad-zkvm-zisk-precompile-test

# Frame with the 8-byte LE length prefix (zero-padded to an 8-byte multiple).
python3 -c "
import struct, sys
p = open(sys.argv[1],'rb').read()
f = struct.pack('<Q', len(p)) + p
f += b'\x00' * ((-len(f)) % 8)
open(sys.argv[2],'wb').write(f)
" /tmp/pt-vectors.bin /tmp/pt-vectors.framed.bin

ziskemu \
    -e target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk-precompile-test \
    -i /tmp/pt-vectors.framed.bin \
    -o /tmp/pt-out.bin
xxd -p /tmp/pt-out.bin | head -1
#  → 50523031370700003707000000000000000000000000...  (zero-padded to 256 bytes)
```

### Reading the result

Both backends emit the same `PR01` summary (little-endian):

```
"PR01" | total u32 | passed u32 | failed u32 | logged u32 |
    logged * { index u32 | addr u16 | got_status u8 }
```

A full pass has `total == passed` and `failed == 0`. Above, both decode to
total = passed = `0x00000737` = 1847, failed = 0. On failure, up to 32 records
(capped to fit ZisK's 256-byte committed output) each name the failing vector's
index, precompile address, and returned status.

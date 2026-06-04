# monad zkVM guest

Phase 0 scaffold for executing monad witnesses inside a zero-knowledge VM.
The C++ guest library is shared across backends; the per-backend Rust crates
own the entrypoint, the input/output ABI shims, and the host-side driver
(for SP1).

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
├── build-support/        # Backend::{Zisk,Sp1}.build_guest_lib() helper
├── zisk/                 # ZisK guest crate
└── sp1/                  # SP1 cargo workspace
    ├── program/          #   guest binary
    └── script/           #   host driver / prover (clap CLI)
```

The two Rust crates share a single C ABI: a parameterless
`monad_zkvm_execute_witness()` that reads the witness via `read_input` and
emits the post-state root via `write_output`, both from
[`zkvm_io.h`](core/zkvm_io.h). On ZisK those symbols are provided by
`ziskos`; on SP1 the program crate ships a thin shim that maps them onto
`sp1_zkvm::io::read_vec` / `commit_slice`.

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

The `script` crate is the host driver. It builds the guest ELF as part of
its own build via `sp1_build::build_program_with_args`, so you only run
the script:

```sh
cd zkvm/sp1/script

# Execute (no proof).
cargo run --release -- --input /path/to/witness.bin
#  Output: 0x<32-byte hex>

# Generate and verify a proof.
cargo run --release -- --input /path/to/witness.bin --prove

# Fast local iteration: skip real proving, use the mock prover.
SP1_PROVER=mock cargo run --release -- --input /path/to/witness.bin --prove
```

The `--input` path is read as raw bytes — no length prefix needed (SP1
takes care of framing internally via `SP1Stdin::write_vec`).

## Iterating on the C++ guest in isolation

The C++ guest library can be built independently of either Rust crate, for
fast iteration on `pipeline.cpp` / `execute_block_zkvm` (post-Phase 0):

```sh
cmake -B build-zkvm -S zkvm \
    -DCMAKE_TOOLCHAIN_FILE=$PWD/category/core/toolchains/riscv64-elf-toolchain.cmake \
    -DRISCV_TOOLCHAIN_DIR=$HOME/riscv_gcc \
    -DMONAD_ZKVM_BACKEND=zisk \   # or sp1
    -DCMAKE_BUILD_TYPE=Release
cmake --build build-zkvm --target monad-zkvm-guest
```

The Rust crates pick this same target up through the
[`zkvm/build-support`](build-support/src/lib.rs) crate, which both
`zkvm/zisk/build.rs` and `zkvm/sp1/program/build.rs` delegate to.

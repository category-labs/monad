# monad zkVM guest

Executes block witnesses in a zkVM using a backend-agnostic C++ guest. ZisK is
currently the only backend. The guest uses Ethereum mainnet rules. It reads an
[RLP execution witness](../category/execution/ethereum/rlp/execution_witness.hpp),
executes the block, checks the computed state root against the witness header,
and outputs the 32-byte block hash.

## Layout

```
zkvm/
├── core/                 # bare-metal libc / libstdc++ shims and halt ABI
├── category/             # zkVM replacements for host headers and sources
├── boost/, quill/        # replacements for host-only library headers
├── guest/                # shared C++ witness executor
│   ├── execute_witness.cpp
│   ├── build_identity.cpp  # the ELF's commit marker
│   ├── execute_block.cpp
│   ├── x86_test_runner.cpp
│   └── CMakeLists.txt
├── build-support/        # Cargo/CMake build helpers
└── zisk/                 # ZisK guest crate
```

A backend calls `monad_zkvm_execute_witness()`, which uses `read_input` and
`write_output` from the vendored
[eth-act I/O interface](../third_party/zkevm-standards/standards/io-interface/zkvm_io.h).
ZisK enters through a Rust guest backed by `ziskos`.

## Prerequisites

- Initialize the repository's submodules with
  `git submodule update --init --recursive`.
- Install CMake, Python 3.9 or later, a build tool such as Make or Ninja,
  and Boost headers with their CMake package configuration.
- Use a `riscv64-unknown-elf` or `riscv64-none-elf` GCC toolchain with newlib
  and C++23 support. Set `RISCV_TOOLCHAIN_DIR` in the environment or in a
  local, gitignored `zkvm/.cargo/config.toml`:

  ```toml
  # zkvm/.cargo/config.toml
  [env]
  RISCV_TOOLCHAIN_DIR = "/absolute/path/to/riscv_gcc"
  ```

  Cargo reads this configuration when invoked from a backend directory.
- For ZisK, install `cargo-zisk` and `ziskemu` using
  [ziskup](https://github.com/0xPolygonHermez/zisk). The guest pins `ziskos`
  to **v1.4.0-alpha** in [Cargo.toml](zisk/Cargo.toml); use matching tools.

Start each section's commands from the repository root unless stated otherwise.

## ZisK

ZisK input is an 8-byte little-endian payload length followed by the witness,
zero-padded to an 8-byte boundary.

Published benchmarks and releases use the [reference Nix build](../nix/zisk/README.md#zisk-guest-elf):

```sh
nix build --option sandbox true --option sandbox-fallback false '.?submodules=1#zisk-elf'
# result/monad-zkvm-zisk and result/monad-zkvm-zisk.build.json
```

It pins the source and toolchains, records the build inputs and ELF hash in a
manifest, and verifies the identity embedded in the ELF. Keep the manifest
with the artifact. An x86_64 Linux builder is required. Check reproducibility
with independent rebuilds.

For local edits, use the [Nix development shell](../nix/zisk/README.md#development-shell).
It supplies the compilers and linker configuration and enables DMA and LTO.
No `cargo-zisk` is needed. Build-tool selection is fixed by the shell;
override `MONAD_ZKVM_ZISK_DMA` or `MONAD_ZKVM_ZISK_LTO` to compare options.

Cargo caches CMake builds by compiler path and configuration under
`OUT_DIR`. Nix's immutable compiler paths identify the toolchains.
Development builds default to `monad-zkvm;commit=none;build=none`.

```sh
# 1. Build the guest ELF in the development shell.
nix develop .#zisk
cd zkvm/zisk
cargo build --release --locked --target riscv64ima-zisk-zkvm-elf --target-dir target/elf --bin monad-zkvm-zisk
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
" "$WITNESS" > /tmp/zkvm-input.bin

# 3. Execute under the emulator. -o writes the public output buffer.
ziskemu \
    -e target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk \
    -i /tmp/zkvm-input.bin \
    -o /tmp/zkvm-output.bin

# 4. Inspect the block hash (first 32 bytes of the output).
xxd -p -l 32 /tmp/zkvm-output.bin
```

For proving, follow the ZisK documentation for the installed tool version.

## Iterating on the C++ guest in isolation

To build the ZisK C++ archive without Cargo:

```sh
cmake -B build-zkvm -S zkvm/guest \
    -DCMAKE_TOOLCHAIN_FILE="$PWD/category/core/toolchains/riscv64-elf.cmake" \
    -DRISCV_TOOLCHAIN_DIR="/absolute/path/to/riscv_gcc" \
    -DMONAD_ZKVM_GUEST_TARGET=zisk \
    -DCMAKE_BUILD_TYPE=Release
cmake --build build-zkvm --target monad-zkvm-guest-zisk --parallel
```

This produces a static archive, not a runnable guest ELF. The Cargo build
uses the same CMake project through [build-support](build-support/src/lib.rs).

For host iteration, configure the main build as described in the
[repository README](../README.md#compiling-the-execution-code), then run:

```sh
cmake --build build --target monad-zkvm-x86-test-runner --parallel
build/zkvm/guest/monad-zkvm-x86-test-runner \
    --input /path/to/witness.bin --output /tmp/zkvm-output.bin
xxd -p /tmp/zkvm-output.bin
```

The host runner accepts raw witness bytes and writes the block hash as binary
to `--output`, or to stdout if omitted.

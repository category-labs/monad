# monad zkVM guest

Executes block witnesses in ZisK and SP1 using a shared C++ guest. The guest
currently uses Ethereum mainnet rules. It reads an
[RLP execution witness](../category/execution/ethereum/rlp/execution_witness.hpp),
executes the block, and outputs the 32-byte block hash with the computed state
root sealed into the header.

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
├── build-support/        # shared Cargo/CMake build helpers
├── zisk/                 # ZisK guest crate
└── sp1/                  # SP1 cargo workspace
    ├── program/          #   C guest entry (main.c)
    └── script/           #   host driver / prover (clap CLI)
```

Both backends call `monad_zkvm_execute_witness()`, which uses `read_input` and
`write_output` from the vendored
[eth-act I/O interface](../third_party/zkevm-standards/standards/io-interface/zkvm_io.h).
ZisK enters through a Rust guest backed by `ziskos`. SP1 enters through
[`program/main.c`](sp1/program/main.c), linked with the SDK's `libzkevm.a`
for its runtime, I/O, and accelerators.

## Prerequisites

- Initialize the repository's submodules with
  `git submodule update --init --recursive`.
- Install CMake, Python 3.9 or later, a build tool such as Make or Ninja,
  and Boost headers with their CMake package configuration. Python also
  fingerprints the toolchain for direct Cargo builds.
- Use a `riscv64-unknown-elf` or `riscv64-none-elf` GCC toolchain with newlib
  and C++23 support. Set `RISCV_TOOLCHAIN_DIR` in the environment or in a
  local, gitignored `zkvm/.cargo/config.toml`:

  ```toml
  # zkvm/.cargo/config.toml
  [env]
  RISCV_TOOLCHAIN_DIR = "/absolute/path/to/riscv_gcc"
  ```

  Cargo reads this configuration when invoked from either backend directory.
- For ZisK, install `cargo-zisk` and `ziskemu` using
  [ziskup](https://github.com/0xPolygonHermez/zisk). The guest pins `ziskos`
  to **v1.3.2-alpha** in [Cargo.toml](zisk/Cargo.toml); use matching tools.
- For SP1, install the `succinct` Rust toolchain using
  [sp1up](https://docs.succinct.xyz/getting-started/install.html), and provide
  `ld.lld` on `PATH` or through that toolchain. The host SDK is **6.8.1**;
  [build-support/Cargo.toml](build-support/Cargo.toml) pins the guest SDK source
  to revision `9e94952a`, which includes accelerator ABI fixes. The host Rust
  version is pinned in [rust-toolchain.toml](sp1/rust-toolchain.toml).

Start each section's commands from the repository root unless stated otherwise.

## ZisK

ZisK input is an 8-byte little-endian payload length followed by the witness,
zero-padded to an 8-byte boundary.

Published benchmarks and releases use the [reference Nix build](../nix/README.md#zisk-guest-elf):

```sh
nix build --option sandbox true --option sandbox-fallback false './nix?submodules=1#zisk-elf'
# result/monad-zkvm-zisk and result/monad-zkvm-zisk.build.json
```

It pins the source and toolchains and checks the allocator assumptions and
linked ELF. Keep the manifest with the artifact. `zkvm/zisk/build.sh --official`
is a shortcut to this Nix build; it requires an x86_64 Linux builder.
Reproducibility must still be checked by independent rebuilds.

For development with locally installed tools, `zkvm/zisk/build.sh` accepts
`-DNAME=VALUE` CMake options, such as `-DMONAD_ZKVM_ZISK_DMA=ON`. DMA and clean byte stores are
off by default outside Nix; enable them with their CMake options or the
`MONAD_ZKVM_ZISK_DMA` and `MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES` environment variables.
With `--archive`, it builds only `libmonad-zkvm-guest-zisk.a`, using CMake and
Python 3 without Rust or `cargo-zisk`. Both paths share
`build-support/build_archive.py`; `test-build-archive.sh` compares their archives.
Without explicit stamps, development ELFs carry
`monad-zkvm;commit=none;build=none`. Initialize submodules recursively before
using the Nix build.

```sh
# 1. Build the guest ELF.
zkvm/zisk/build.sh
cd zkvm/zisk
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

## SP1

The `script` crate builds and embeds the guest ELF automatically, including
`libzkevm.a` from the pinned SDK source.

```sh
cd zkvm/sp1/script

# Execute (no proof).
cargo run --release -- --input /path/to/witness.bin
#  Output: 0x<32-byte hex>

# Add --cycles to report the instruction count (slower).
cargo run --release -- --input /path/to/witness.bin --cycles

# Generate and verify a proof.
cargo run --profile prover -- --input /path/to/witness.bin --prove

# Fast local iteration: skip real proving, use the mock prover.
SP1_PROVER=mock cargo run --release -- --input /path/to/witness.bin --prove
```

Use `release` for iteration: it disables LTO to shorten linking. Use `prover`
for real proofs: it enables fat LTO and one codegen unit.

Pass the raw witness file to `--input`. The driver uses `SP1Stdin::write_slice`;
do not add ZisK's length prefix.

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

This produces a static archive, not a runnable guest ELF. Both Cargo builds
use the same CMake project through [build-support](build-support/src/lib.rs).
Use the Cargo commands above for SP1 so cmake-rs selects its `rv64im` flags;
the standalone toolchain defaults to `rv64ima`.

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

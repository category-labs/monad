# monad zkVM guest

Executes block witnesses in ZisK and SP1 using a shared C++ guest. The guest
currently uses Ethereum mainnet rules. It reads an
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
  and Boost headers with their CMake package configuration.
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
  to **v1.4.0-alpha** in [Cargo.toml](zisk/Cargo.toml); use matching tools.
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

### ZisK build options

**Default** is the value with no overrides. **Reference** is the value in
`nix build .#zisk-elf`. For **Environment** rows, export the variable
directly before running Cargo. For **CMake** rows, pass a definition through
`MONAD_ZKVM_CMAKE_ARGS`, for example
`MONAD_ZKVM_CMAKE_ARGS="-DMONAD_ZKVM_GAS_SELFTEST=ON"`.
Cargo caches each configuration separately under `OUT_DIR`.

| Option | Default | Reference | Set via | Effect when ON |
| --- | --- | --- | --- | --- |
| `MONAD_ZKVM_FUSE_DUP` | ON | ON | Environment | Pass the source of DUP2–DUP16 to the following opcode. OFF removes the 40-byte DUP prefix and restores seven handler copies per slot. |
| `MONAD_ZKVM_FUSE_SWAP1` | ON | ON | Environment | Use SWAP1 follower prefixes and fused pairs. OFF frees 40 bytes per handler copy. PUSH1 followed by SWAP1 belongs to the PUSH1 family. |
| `MONAD_ZKVM_FUSE_SOLIDITY_SELECTOR` | ON | ON | Environment | Fuse the calldata-size prologue, selector extraction and EQ/GT selector tests. ABI argument bounds checks are independent. |
| `MONAD_ZKVM_FUSE_SOLIDITY_ALLOC_FINALIZE` | ON | ON | Environment | Fuse Solidity’s successful allocation finalization: check the new free-memory pointer, store it at 0x40 and jump back to the caller. |
| `MONAD_ZKVM_FUSE_SOLIDITY_COPY_LOOP` | ON | ON | Environment | Batch Solidity memory-copy loops that advance by 32 bytes per iteration. |
| `MONAD_ZKVM_ZISK_DMA` | OFF | ON | Environment | Use patched GCC to lower eligible memory operations to ZisK DMA. |
| `MONAD_ZKVM_ZISK_LTO` | OFF | ON | Environment | Optimize across C and C++ translation units before linking the guest archive into the ELF. |
| `MONAD_ZKVM_KECCAKF_MEMO` | ON | ON | CMake | Cache Keccak-f states using executor-supplied indices. The table occupies 100 MiB of BSS. |
| `MONAD_ZKVM_WIDE_MEMORY_SIZE` | OFF | ON | CMake | Use 64-bit EVM memory sizes and capacities. |
| `MONAD_ZKVM_VARCODE_CACHE` | OFF | ON | CMake | Reuse VM code wrappers by code hash. |
| `MONAD_ZKVM_NO_DIRTY_ACCOUNTS` | OFF | ON | CMake | Omit dirty-account tracking. Requires reserve-balance tracking to be inactive. |
| `MONAD_ZKVM_NO_MERGE_CONSTRAINTS` | OFF | ON | CMake | Skip recording conflict constraints during sequential transaction execution. |
| `MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE` | OFF | OFF | CMake | Assert that each sequential transaction can merge. Requires NO_MERGE_CONSTRAINTS=OFF. |
| `MONAD_ZKVM_SELFTEST` | OFF | OFF | CMake | Run the State self-test instead of executing a witness. |
| `MONAD_ZKVM_GAS_SELFTEST` | OFF | OFF | CMake | Run the interpreter gas-boundary and State rollback tests. |
| `MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE` | OFF | OFF | CMake | Check gas at every opcode. Requires GAS_SELFTEST=ON. |

To measure one fusion family, build once with all families enabled and once
with only that family set to OFF. Compare aggregate COST on the same witnesses
and check each public block hash. Report the fixed corpus and recent sample
separately.

### Running the guest


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

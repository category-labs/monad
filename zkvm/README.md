# monad zkVM guest

Executes monad witnesses inside a zero-knowledge VM: the guest ingests a
reth-format execution witness, rebuilds the partial state trie, runs the block
it carries, and commits the roots.
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
│   ├── ffi.cpp           # monad_zkvm_execute_witness: witness in, roots out
│   └── CMakeLists.txt
├── build-support/        # guest-build helpers (build_guest_lib / build_guest_elf)
├── zisk/                 # ZisK guest crate
└── sp1/                  # SP1 cargo workspace
    ├── program/          #   C guest entry (main.c)
    └── script/           #   host driver / prover (clap CLI)
```

Both backends drive the same C++ guest entry point: a parameterless
`monad_zkvm_execute_witness()` that reads the witness via `read_input` and
commits [the public output](#the-public-output) with one `write_output` a
value, both from [`zkvm_io.h`](core/zkvm_io.h). On ZisK the guest is a Rust
crate and those symbols are provided by `ziskos`; on SP1 there is no Rust
guest — the entry is `program/main.c`, and `read_input` / `write_output` (plus
`_start`, the allocator, and the `zkvm_*` accelerators) come from
`libzkevm.a`, built from the SP1 zkEVM SDK source at build time.

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
- [ZisK](https://github.com/0xPolygonHermez/zisk) at **tag v1.1.0-alpha**,
  which is what `zkvm/zisk/Cargo.toml` pins `ziskos` to (`ziskup` from
  <https://github.com/0xPolygonHermez/zisk>) — installs `cargo-zisk`,
  `ziskemu`. Not a floor to round down from: the guest links that `ziskos`, so
  a `cargo-zisk` or `ziskemu` from another release is a different precompile
  set and a different cost model, and every cell figure quoted in this tree is
  measured against this one.
- [SP1](https://docs.succinct.xyz/) at **v6.3.1**, pinned twice — `sp1-sdk` in
  `zkvm/sp1/script/Cargo.toml` and the `sp1-build` git tag in
  `zkvm/build-support/Cargo.toml`, the second being the source `libzkevm.a` is
  compiled from (`sp1up` from
  <https://docs.succinct.xyz/getting-started/install.html>) — installs
  `cargo-prove` and the `+succinct` rust toolchain, which `sp1-build` needs to
  cross-compile that staticlib.

## ZisK

Build and run the guest in the emulator. ZisK expects inputs to be
length-prefixed: the first 8 bytes are the little-endian payload length,
followed by the payload itself.

Report and release artifacts must use the audited profile:

```sh
zkvm/zisk/build-official.sh
```

It selects the patched GCC 15.2 toolchain (override `RISCV_TOOLCHAIN_DIR` if
needed), enables DMA lowering, dispatch-table threading, the Keccak-f memo and
the measured fusions together, then audits the effective flags and linked ELF.
Configuration fails if a required feature is explicitly disabled. A successful
build writes `<elf>.build.json`; keep that manifest beside any ELF used in a
published benchmark. Direct `cargo-zisk build` remains available for diagnostic
A/B builds and is deliberately not an official artifact.

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

# 4. Inspect the public output.
xxd /tmp/zkvm-output.bin | head -2
```

### The public output

| Offset | Size | Value |
|--------|------|-------|
| 0 | 32 | post-state root |
| 32 | 32 | pre-state root |
| 64 | 32 | block hash, over the header with the COMPUTED state root sealed in |
| 96 | 32 | message anchor — `MONAD_ZKVM_L2` only |
| 128 | 8 | block number, big-endian u64 — `MONAD_ZKVM_L2` only |

The third value is sufficient on its own: the computed root is sealed into the
header before it is hashed, so pinning the hash against the canonical chain at
that height pins the state root, the parent, and every other header field in
one comparison. The first two are published because they are useful to a caller
and to the corpus gate.

On an L2 build the last two give a verifier the tuple the L1 hub checks —
`stateTransitionDigest(chainId, blockNumber, newStateRoot, namespaceAnchor)`,
with `chainId` compiled into the guest — without it having to carry the header.
Neither adds anything to trust: the block number is a header field, and the
anchor is a deterministic function of the block's logs, which `receipts_root`
commits to.

```sh
xxd -s 0  -l 32 /tmp/zkvm-output.bin   # post-state root
xxd -s 32 -l 32 /tmp/zkvm-output.bin   # pre-state root
xxd -s 64 -l 32 /tmp/zkvm-output.bin   # block hash
xxd -s 96 -l 40 /tmp/zkvm-output.bin   # anchor || block number   (L2 only)
```

A diagnostic build appends the `MONAD_ZKVM_KECCAK_SITES` tail after these, so
their offsets never move. That tail is 152 bytes, which with the three roots
comes to 248 of ZisK's 256-byte committed output — which is why `MONAD_ZKVM_L2`
and `MONAD_ZKVM_KECCAK_SITES` are a configure-time error together.

## The L2 arm

`MONAD_ZKVM_L2` builds a guest for the L2: transactions arrive encrypted, an
end-of-block anchor of the messages emitted is published, and gas is metered
but not priced. It is a mode and not an optimisation — the witness grows a
seventh field, the chain changes, and the consensus rules with it — so a witness
built for one setting is rejected outright by the other.

Every deployment value is required and has none. A guest pointed at the wrong
spoke, or decrypting under the wrong operator key, emits proofs the L1 hub
accepts, so a missing value stops the build rather than picking a plausible
one; `cmake/l2.cmake` names them. They reach `cargo-zisk` through the same
channel as any other cmake define:

```sh
cd zkvm/zisk
MONAD_ZKVM_CMAKE_DEFINES="\
MONAD_ZKVM_L2=ON;\
MONAD_ZKVM_L2_CHAIN_ID=1;\
MONAD_ZKVM_L2_NAMESPACE_ID=<n>;\
MONAD_ZKVM_L2_REVISION=MONAD_ETH_PARIS;\
MONAD_ZKVM_L2_SPOKE=0x<40 hex>;\
MONAD_ZKVM_L2_PENDING_SLOT=<n>;\
MONAD_ZKVM_L2_OPERATOR_PK_X=0x<64 hex>;\
MONAD_ZKVM_L2_OPERATOR_PK_ODD=<0|1>;\
MONAD_ZKVM_L2_EPOCH_BLOCKS=<n>" \
    cargo-zisk build --release
```

The operator key is compiled in, so the order is: generate a keypair, configure
with its public half, and hand the witness rewriter the matching secret.

### Swapping the encryption

`MONAD_ZKVM_L2_CIPHER` selects the cipher suite and is the one L2 value with a
default (`ecdh-poseidon2`), because it names an implementation rather than a
deployment: getting it wrong cannot prove the wrong thing, it produces leaves
that do not decrypt. An unknown name fails configuration with the known ones
listed.

The encryption is explicitly not an audited construction, so the seam is there
from the start rather than extracted later:
[`l2_cipher_suite.hpp`](guest/l2_cipher_suite.hpp) holds the interface — two
associated types and two static functions — and a concept that a candidate
suite is `static_assert`ed against, so an incomplete one names itself once
instead of failing at whichever call site the compiler reaches first. Behind it
sit the wire format, the curve or the absence of one, the field, the sponge and
the tag; in front of it `decode_block_l2` and `ffi.cpp` name no cipher at all.
What the interface does NOT let a suite change is the decision rule — a leaf it
refuses is a deterministic rejection of one queue entry, never a halt — nor the
binding of the operator secret, which is the check the whole design rests on.

Selection is a compile-time alias, so a guest carries exactly one suite and an
unselected one is not compiled. **Comparing two therefore means two ELFs and two
runs**, like the corpus differential below, and what that yields is a total
rather than a breakdown: nothing in the cipher counts cells per phase, so the
ECDH / sponge / packing split quoted in this tree is computed from ZisK's cost
table and not measured. Instrumenting it needs a diagnostic mode of its own,
since the committed output region is already at 248 of 256 bytes in the
keccak-sites build.

### The corpus differential

Nothing in this repository produces witnesses, so the L2 arm gets its oracle by
REWRITING one rather than making one. Encrypting the leaves and recomputing
`transactions_root` changes nothing execution reads — `execute_block_header`
and `ExecuteTransaction` touch `prev_randao`, `beneficiary`, `timestamp`,
`number`, `gas_limit` and `base_fee_per_gas`, not that root — and the decrypted
transactions are byte for byte the originals. So the two runs must agree on the
first 64 bytes of the public output, exactly. Only the block hash differs, and
it differs by construction because the block is fabricated.

**`MONAD_ZKVM_L2_REVISION` has to be the revision mainnet's own schedule would
give the corpus blocks**, and getting it wrong costs the oracle rather than
announcing itself. The plaintext arm is `EthereumMainnet` and consults that
schedule; the L2 arm returns a compiled constant and ignores the block
entirely, which is the point of a chain with no fork schedule. Set the two to
different revisions and the arms execute under different EVM rules, so the
post-state roots differ for a reason that has nothing to do with the cipher --
the one signal this differential exists to give.

Both runs go through `ziskemu`, on two ELFs. Not through a host executor: an
x86 build of the guest is a different program, with the native Poseidon2
permutation instead of `csrs 0x812` and libsecp256k1 instead of zisklib, so two
host arms agreeing would say nothing about the arm being proved.

```sh
# The plaintext arm, saved aside before the L2 configure overwrites the ELF.
cd zkvm/zisk && cargo-zisk build --release
cp target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk /tmp/guest-plain

# The L2 arm, with the defines above.
MONAD_ZKVM_CMAKE_DEFINES="MONAD_ZKVM_L2=ON;..." cargo-zisk build --release
cp target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk /tmp/guest-l2

# Rewrite the witness. --check decrypts every leaf back before writing.
monad-zkvm-l2-witness --in plain.bin --out l2.bin --sk <64 hex> --check

# Frame both (8-byte LE length prefix, zero-padded to a multiple of 8) and run.
ziskemu -e /tmp/guest-plain -i plain.framed.bin -o /tmp/a.bin
ziskemu -e /tmp/guest-l2    -i l2.framed.bin    -o /tmp/b.bin

cmp <(head -c 64 /tmp/a.bin) <(head -c 64 /tmp/b.bin)   # must be identical
```

`monad-zkvm-l2-witness` is a host tool and legitimately so: it only rewrites
bytes, and it shares `l2_cipher` with the guest, so its keystream is the
guest's by construction rather than by agreement.

For proving, see ZisK's docs (`cargo-zisk prove ...`); nothing above proves,
it only executes under the emulator.

## SP1

The `script` crate is the host driver. Its `build.rs` builds the guest ELF as
part of its own build — cross-compiling the C++ guest archive and linking it
(plus `program/main.c`) against `libzkevm.a`, itself built from the SP1 zkEVM
SDK source — so you only run the script:

```sh
cd zkvm/sp1/script

# Execute (no proof).
cargo run --release -- --input /path/to/witness.bin
#  Output: 0x<96-byte hex>   -- the three roots, as on ZisK

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

The `--input` path is read as raw bytes and handed over verbatim with
`SP1Stdin::write_slice` — no length prefix, and **not** `write_vec`, which
prepends framing that libzkevm's `read_input` (`read_vec_raw`) does not strip
and which would therefore corrupt the RLP. The ZisK framing above is the
emulator's own convention and has no counterpart here.

## Iterating on the C++ guest in isolation

The C++ guest library can be built independently of either Rust crate, for
fast iteration on `ffi.cpp` / `execute_block_zkvm`:

```sh
cmake -B build-zkvm -S zkvm/guest \
    -DCMAKE_TOOLCHAIN_FILE=$PWD/category/core/toolchains/riscv64-elf.cmake \
    -DRISCV_TOOLCHAIN_DIR=$HOME/riscv_gcc \
    -DMONAD_ZKVM_GUEST_TARGET=zisk \
    -DCMAKE_BUILD_TYPE=Release
cmake --build build-zkvm --target monad-zkvm-guest-zisk
```

`MONAD_ZKVM_GUEST_TARGET` is `zisk` or `sp1`, and **defining it at all is what
selects cross-compile mode** — left undefined, `zkvm/guest/CMakeLists.txt` takes
its host-x86 branch, which expects to be an `add_subdirectory` of the root
project and will not configure standalone. It also names the archive, so the
target to build is `monad-zkvm-guest-<suffix>`; `monad-zkvm-guest` alone is the
cmake *project* name and not a target.

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

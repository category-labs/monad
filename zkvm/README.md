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

The two arms publish different things, because the L2's state is private and
the Ethereum arm's is not.

**Ethereum** — three values:

| Offset | Size | Value |
|--------|------|-------|
| 0 | 32 | post-state root |
| 32 | 32 | pre-state root |
| 64 | 32 | block hash, over the header with the COMPUTED state root sealed in |

The third is sufficient on its own: the computed root is sealed into the header
before it is hashed, so pinning the hash against the canonical chain at that
height pins the state root, the parent, and every other header field in one
comparison. The first two are published because they are useful to a caller and
to the corpus gate.

**L2** — four values, and **no state root**:

| Offset | Size | Value |
|--------|------|-------|
| 0 | 32 | parent block hash |
| 32 | 32 | block hash |
| 64 | 32 | message anchor |
| 96 | 8 | block number, big-endian u64 |

A root is a commitment, and a commitment to a guessable value confirms guesses.
On this chain the state IS guessable from public data: the participants are
registered on the L1, deposits are public L1 transfers, and the ciphertexts
were sequenced through the L1 in the clear. So an observer who can enumerate
the plausible sets of transfers computes each candidate root and compares.
Hashing is no defence — nothing is being inverted — which is why publishing
`keccak256(header)` instead would not have helped either: almost every other
header field is public or derivable, and the rest (`state_root`,
`receipts_root`, `logs_bloom`, `gas_used`) are all functions of one hypothesis
about what the block did.

What makes the two hashes safe to publish is a **per-block blinder** in the
header's `extra_data`, derived as
`keccak256("monad-l2/state-salt/v1" ‖ salt_secret ‖ number)`. The number is in
there because a constant blinder would leave two blocks of identical state
publishing the same hash, which on a low-volume chain says which blocks did
nothing.

`salt_secret` is witness field [7] and is checked against a compiled
`MONAD_ZKVM_L2_SALT_COMMITMENT`, which needs saying because the reason is not
soundness. An unbound blinder costs nothing there: the commitment chain forces
a prover to reuse whatever it chose and `keccak256` binds it, so every proof
still verifies and every block still chains. What an unbound blinder costs is
the confidentiality it exists for — a producer supplying zeros publishes an
unblinded hash and nothing anywhere says so.

Dropping the roots costs nothing, because the continuity they were published
for is established inside the circuit: the pre-state root is asserted equal to
the newest ancestor header's `state_root` and that header to hash to
`parent_hash`, and the post-state root is sealed into the header the block hash
covers. The hub therefore chains a block to its parent with one comparison —
this block's parent hash against the previous block's hash — and reads no root
to do it.

The **anchor is not blinded and cannot be**: the L1 verifies merkle proofs
against it to release withdrawals. It is guessable the same way a root is, so
the honest statement of the cost is that a message not yet relayed can be
confirmed early. That is inherent to a root the L1 must open.

### What the L1 hub must check, and what this branch does not establish

That argument does not carry over to the L2, and the difference is the whole
soundness question. It rests on there being a canonical chain to pin the hash
against. An L2 has none — the hub is what decides which block is canonical —
so publishing the hash of a header the prover wrote authenticates nothing by
itself. A prover can build any header, seal its own computed root into it, and
emit a perfectly consistent proof of a transition nobody asked for.

So a hub verifying one of these proofs has to check all of:

1. **Chain and height** — `chainId`, which is compiled into the guest, and the
   published block number is the next height it expects for that namespace.
2. **The pre-state it accepted** — the published parent block hash at offset 0
   equals the block hash the hub last accepted for this namespace. Without this
   a proof is a transition from *some* state, not from *the* state, and a
   prover picks the starting point. The hub compares hashes rather than roots,
   and that is a stronger check, not a weaker one: a block hash covers the
   state root and every other header field at once.
3. **The inputs it authorised** — the ciphertext list the guest executed is the
   one published to the data availability the hub trusts. The published block
   hash is `keccak256` of the header with this run's computed state root sealed
   in, so it already commits to `transactions_root` along with every other
   header field. The hub opens that commitment by being handed the header
   preimage, checking its hash against the published value, and reading the
   transactions root out of it — one comparison binds the lot. A header is a
   few hundred bytes, and the operator has it.
4. **The operator** — a signature over
   `stateTransitionDigest(chainId, blockNumber, newStateRoot, namespaceAnchor)`.

What the output has to publish, then, is whatever the header does NOT carry:
the anchor, because it is a function of the block's logs and the hub has no
receipts to recompute it from. It is there. The parent hash and the block
number are header fields, published so the hub can chain and index without
holding the header.

So the gap is not in the output format; it is that none of the four checks
above exists. The L2's soundness is conditional on an L1 side this branch does
not contain, and on the operator actually handing over the header rather than
only the tuple.

```sh
# Ethereum
xxd -s 0  -l 32 /tmp/zkvm-output.bin   # post-state root
xxd -s 32 -l 32 /tmp/zkvm-output.bin   # pre-state root
xxd -s 64 -l 32 /tmp/zkvm-output.bin   # block hash

# L2
xxd -s 0  -l 64 /tmp/zkvm-output.bin   # parent block hash || block hash
xxd -s 64 -l 40 /tmp/zkvm-output.bin   # anchor || block number
```

A diagnostic build appends the `MONAD_ZKVM_KECCAK_SITES` tail after these, so
their offsets never move. That tail is 152 bytes, which with the Ethereum
arm's 96 comes to 248 of ZisK's 256-byte committed output — one enumerator of
margin and no more. `MONAD_ZKVM_L2` and `MONAD_ZKVM_KECCAK_SITES` remain a
configure-time error together: the L2's four values are 104 bytes, so the two
would come to exactly 256, and a budget with no margin at all is not a
configuration to leave reachable.

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
MONAD_ZKVM_L2_EPOCH_BLOCKS=<n>;\
MONAD_ZKVM_L2_SALT_COMMITMENT=0x<64 hex>" \
    cargo-zisk build --release
```

The operator key is compiled in, so the order is: pick a secret, run
`monad-zkvm-corpus-gen --pubkey <secret>` for the two `OPERATOR_PK` values,
configure with those, and hand the generator the same secret with `--sk`. The
generator checks the pair at startup and refuses to produce a corpus nothing
can decrypt.

`MONAD_ZKVM_L2_SPOKE` comes from the same tool: `--spoke-address` prints where
the spoke scenario deploys. The address is CREATE-derived, so it follows the
deployer key and therefore the `--seed`. And `--salt-commitment <secret>`
prints `MONAD_ZKVM_L2_SALT_COMMITMENT` for a blinder secret, which the
generator then wants back as `--salt`.

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
unselected one is not compiled. **Comparing two therefore means two ELFs and
two runs.** Nothing in the cipher counts its own cells, so a phase breakdown
does not come from the guest; it comes from attributing an emulator trace to
symbols from outside.

That was done once, on `al/zkvm-r10-l2-corpus`, over a 200-block rewritten
mainnet corpus, and the result is worth carrying because it inverts what this
design assumed. The sponge outweighs the ECDH by **15.7x in steps** where the
plan predicted roughly 24x the other way. The Poseidon2 precompile is 19,386
steps on a whole block -- 0.3% of the cipher -- and the cost is the software
mode around it, of which `L2Sponge::charge`, validating that the declared SAFE
pattern is being followed, is 24% on its own. In cells the margin narrows to
about 7x, since the ECDH's work is precompiled and the sponge's is not. Nothing
here has been profiled against the generated corpus yet.

### The corpus

The blocks the L2 arm runs on are **generated, not borrowed**. `zkvm/test/corpus`
builds a genesis state, signs transactions, executes them on the host and emits
the witness the guest consumes -- so the blocks obey this chain's rules instead
of being made to fit them.

That distinction is the whole reason the section exists. An earlier approach
took mainnet witnesses and rewrote their leaves, which needed three levers to
make the guest accept a shape it has no rules for: withdrawals and a
`requests_hash` and blob transactions, a mainnet blob schedule, and gas pricing
put back because the header's `gas_used` was computed under L1 rules. A
generated block has none of those shapes, so none of the levers exist here.

**The corpus targets Paris, and the number is load-bearing.** The chain starts
at block 15,537,394 with a timestamp below 1,681,338,455 -- Shanghai's. Paris
is the one window with no withdrawals, no `requests_hash` and no blob fields,
which is exactly the shape this chain accepts unaided. `MONAD_ZKVM_L2_REVISION`
has to be `MONAD_ETH_PARIS` to match.

Three scenarios: EOA transfers with a contract that fills storage slots and
zeroes one; CREATE, logs, REVERT, SELFDESTRUCT and the legacy/2930/1559
transaction types; and the real `NamespaceSpoke`, vendored from
`eerkaijun/monad-namespaces` at `e6012d8cebf4` and deployed by CREATE, sending
namespace messages so the anchor has logs to harvest and a pending array to
clear.

```sh
# Configure an L2 host tree with the nine deployment values, then:
cmake --build build --target monad-zkvm-corpus-gen monad-zkvm-x86-test-runner
./build/zkvm/guest/monad-zkvm-corpus-gen --out /tmp/corpus \
    --sk <64 hex> --salt <64 hex>

# Each witness makes the guest republish what the manifest records: the
# parent block hash, the block hash, the anchor and the number.
./build/zkvm/guest/monad-zkvm-x86-test-runner \
    --input /tmp/corpus/spoke-15537396.witness --output /tmp/out.bin
```

Note that the manifest still records both state roots even on the L2 arm. They
are what the generator computed, not what the guest publishes -- and the corpus
check uses them for a second purpose: asserting that neither appears anywhere
in the published output, which is the property the blinder exists for and the
one worth checking directly rather than assuming.

**The oracle is not circular**, and that is the point of generating rather than
asserting. The generator computes its roots with `TrieDb`, the node's own
backend; the guest recomputes them with `OffsetTrie` from the blob. Two
implementations of the same trie, so their agreement is evidence. The anchor is
derived twice for the same reason -- the generator merkleises the receipts
itself, the guest merkleises them in the epilogue.

Building the same sources with `MONAD_ZKVM_L2=OFF` gives a plaintext corpus and
the three-value output, which is the cheaper check to run first: it exercises
the generator and the trie without the cipher in the way.

### Witnesses the guest must refuse

`test_witness_rejection` is the other half, and it is the half that rots
unnoticed. Everything above proves the guest accepts what it should; these
prove it rejects what it should, and they guard assertions whose absence
produces a **valid-looking proof rather than a crash** -- so nothing else
would ever report them missing.

| Tampering | What has to catch it |
|---|---|
| the parent is omitted from the ancestor list | `checked_pre_state_root` |
| an ancestor is removed from the middle of the run | the contiguity check |
| one bit of `salt_secret` is flipped | the compiled salt commitment |

They drive the real runner as a subprocess, because a bad witness is signalled
by aborting -- the thing under test is a process exit -- and they match on the
assertion text, not just a non-zero status, so a test cannot pass for the wrong
reason.

Two details that decide whether these test anything. The run starts from a
four-block chain and drops an ancestor from the MIDDLE: dropping the oldest
would just make a shorter, valid run and prove nothing. And the first test
asserts the untampered witness is accepted, without which a rejection below
says nothing about the tampering.

What this does NOT establish: that the gas surgery produces the right
`gas_used`, or that the anchor is what the deployed contract would compute.
Both sides here run the same rules, so their agreement says nothing about
either being right. The storage layout is at least read from the contract's own
source -- `_pendingNamespaceMessages` is slot 1 -- rather than assumed.

Running under `ziskemu` on the real ELF is the step that distinguishes "the C++
agrees with itself" from "the proved guest agrees": an x86 build has the native
Poseidon2 permutation instead of `csrs 0x812` and libsecp256k1 instead of
zisklib, so it is a different program.

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

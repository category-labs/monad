# OpenVM 2 guest — status

The third zkVM backend, targeting OpenVM v2 (`riscv32im-risc0-zkvm-elf`,
transpiled to OpenVM's native format). It executes real Ethereum mainnet
blocks to the correct post-state root, passes the full precompile
golden-vector suite, and proves. The design mirrors the ZisK backend: a Rust
guest crate links `libmonad-zkvm-guest-openvm.a` and supplies the eth-act
runtime ABI, with the difference that OpenVM has no eth-act runtime library, so
this crate provides *everything*: I/O (`src/runtime.rs`) and all 19
accelerators (`src/accel.rs`, `src/bls12_map.rs`).

## Building and running

```
cargo install --git https://github.com/powdr-labs/openvm.git \
    --tag v2.0.0-beta.2-powdr.1 cargo-openvm \
    --no-default-features --features parallel,jemalloc --locked
RISCV_TOOLCHAIN_DIR=~/riscv_gcc_multilib cargo openvm build
```

**The CLI must come from powdr's OpenVM fork, at the tag below.** That fork is
what `powdr-openvm` pins, and the version has to be the same in three places —
the guest, the host driver in `script/`, and the CLI that transpiles — because
the `.vmexe` serialisation is not compatible across it and openvm-org's v2.0.1
(a 2.0.1-transpiled executable fails to load with a bitcode error). Installing
the CLI replaces any upstream `cargo-openvm` on the PATH.

`RISCV_TOOLCHAIN_DIR` must point at a toolchain with an **rv32im/ilp32 multilib**
(see the rv32 port below); the usual `zkvm/.cargo/config.toml` value is rv64-only unless
it was built by the updated `scripts/ubuntu-build/build-riscv-toolchain.sh`.
`cargo openvm build` installs the guest Rust toolchain (`nightly-2026-01-18`,
overridable with `OPENVM_RUST_TOOLCHAIN`) plus `rust-src` on its own. The CLI's
default features drag in the halo2 and EVM-verifier stacks, which `build` and
`run` do not need.

`cargo openvm run` executes a transpiled guest in the VM interpreter with no
proving, which is what the precompile suite uses — see
[the zkvm README](../README.md#4-run-on-openvm) for the invocation.

For anything the CLI cannot express — witness framing, `num_public_values`,
proving — use the host driver in [`script/`](script/), the counterpart of
`zkvm/sp1/script`:

```
cd script
cargo run --release -- --input /path/to/witness.bin           # execute
cargo run --release -- --input ... --mode meter               # trace-cell cost
cargo run --release -- --input ... --mode segment             # proving segments
cargo run --release -- --input ... --prove                    # prove and verify
```

`--exe` defaults to the witness guest; point it at
`../openvm/release/monad-zkvm-openvm-precompile-test.vmexe` to drive the
precompile guest instead. Unlike the SP1 driver it does not build the guest:
OpenVM's guest build is a transpilation step owned by `cargo openvm build`, so
the `.vmexe` is an input.

## OpenVM version pin

Every OpenVM crate resolves to **`github.com/powdr-labs/openvm.git` tag
`v2.0.0-beta.2-powdr.1`**, not openvm-org upstream. This is deliberate: it is
the tag `powdr-openvm` pins, and this backend is meant to feed powdr's
autoprecompiles — automatically synthesised precompiles for hot basic blocks,
alongside (not replacing) the hand-written ones this guest already uses for
SHA-256, Keccak and the curve operations.

Three things follow from the pin and are worth knowing before changing it:

- **It must be the same in three places.** Guest, `script/`, and the
  `cargo-openvm` that transpiles. The `.vmexe` serialisation is not compatible
  with upstream v2.0.1 — a 2.0.1-transpiled executable fails to deserialise
  under the fork's SDK with a bitcode error, not a version warning.
- **`openvm.toml` needs no change.** The fork's
  `crates/sdk-config/src/openvm_standard.toml` is byte-identical to upstream
  v2.0.1's, so the extension set and the generated `openvm_init.rs` carry over.
- **Two API differences from v2.0.1**, both handled. `WeierstrassPoint`'s
  `from_xy` / `from_xy_nonidentity` / `from_xy_unchecked` are safe functions
  here and became `unsafe` later, so the call sites take no `unsafe` block.
  And `SystemConfig` spells the segment memory budget
  `segmentation_config.limits.max_memory` rather than
  `segmentation_max_memory`.

SP1 and this OpenVM cannot share a lockfile: SP1 v6.3.1 pins
`p3-field =0.4.3-succinct` while this OpenVM pins `=0.4.1`, two exact
requirements in one semver bucket. `zkvm/build-support` therefore keeps its
`sp1-build` dependency behind an `sp1` feature that only `zkvm/sp1/script`
enables — the ZisK and OpenVM guests build the archive and stop, so they never
pull SP1 in.

## What exists

| Piece | Status |
|---|---|
| `Backend::OpenVm` (build-support) + cmake target | done; builds `libmonad-zkvm-guest-openvm.a` clean for rv32im/ilp32 |
| `read_input` / `write_output` / `zkvm_halt` | done; exercised end to end by the precompile guest |
| `sys_alloc_aligned` | not ours — `openvm-platform` exports it, and it is the same bump allocator Rust's `#[global_allocator]` uses (see `src/runtime.rs`) |
| Proving | done; block 22200003 proves and verifies end to end in 1 h 48 m at 48.5 GiB peak, or 1 h 12 m with 16 autoprecompiles — see the baseline below |
| All 19 accelerators | done; 1961/1961 golden vectors pass. OpenVM extensions where they exist, software otherwise (ripemd160, modexp, blake2f, the BLS12-381 maps, KZG) |
| `openvm.toml` extension config | done; verified against the v2.0.1 schema and identical to `SdkVmConfig::standard()` |
| Host driver (`script/`) | done; executes, meters, and proves, splitting core from recursion |
| Witness execution | done; mainnet blocks 22200001-22200005 all reproduce their expected post-state root, in 1.9-7.2 s each |

## The rv32 port

OpenVM is rv32im-only (addresses capped at 2^29), and the shared C++ tree was
LP64 throughout. Three commits ahead of this backend made it compile for ILP32;
they are where to look when something ABI-shaped breaks.

- **`unsigned __int128` does not exist on 32-bit targets** — ~85% of the initial
  errors. A 64x64->128 multiply and a 128/64 divide are the only operations that
  need a wider type, so they are isolated as `mul64x64` / `div128by64` in
  `category/core/runtime/uint128.hpp` behind `MONAD_HAS_INT128`, with
  schoolbook-multiply and binary-long-division fallbacks. `uint128_t`'s
  operators, `uint256/portable.hpp`, `knuth_div`, and `storage_page.hpp`'s
  `bitmap_t` are all written once against those two, so there is one code path
  per target rather than a compiler conditional per call site. Define
  `MONAD_NO_INT128` to compile the fallbacks on a 64-bit host and test them
  there — worth wiring into CI, since every rv32 EVM word operation goes through
  them.
- **Layout assertions** are `MONAD_ASSERT_LP64_LAYOUT`
  (`category/core/config.hpp`): checks exactly as before on a 64-bit target,
  compiles out on a 32-bit one. 46 sizeof/alignof/offsetof budgets across 14
  headers went through it, rather than being restated as a second set of magic
  numbers that nothing would keep honest. Alignment properties that hold
  everywhere stay plain `static_assert`s.
- **`uint64_t` -> 32-bit `size_t` narrowing** is split by intent. Hash values
  and provably-small indices take a plain cast, since truncating is the point;
  lengths that derive from block or transaction input go through
  `narrow_to_size` (`category/core/int.hpp`), which asserts the value fits
  instead of truncating into an undersized allocation. `expmod_execute`
  (`ethereum/precompiles.cpp`) is the one call site where all three of a
  buffer's constituent lengths narrow, so they go through it together.
- **`std::min`/`std::max` deduction failures.** This toolchain's newlib makes
  `uint32_t` an `unsigned long` while `size_t` is `unsigned int`: same width,
  distinct types, so untyped literals like `128ul` break deduction in ways x86
  never shows. Typed at each site.

Two build-side consequences, both documented in place in
`zkvm/guest/CMakeLists.txt`: the toolchain needs an **rv32im/ilp32 multilib**
(`-print-file-name` resolves per multilib, and a wrong answer yields a silently
mixed-ABI archive — a configure-time ELF-class check now fails there instead of
at the final link), and libgcc members are located by the symbol they define
rather than by an ABI-dependent file name. The archive is deliberately *not*
self-contained for compiler-runtime routines: all three backends link Rust, and
`compiler_builtins` supplies the rest.

**To delete once upstream moves:** the immer patch in
`zkvm/guest/CMakeLists.txt`. `sizeof_values_n` in
`immer/detail/hamts/node.hpp` calls `std::max` with `size_t` and
`count_t`(=`uint32_t`) arguments — same width, distinct types here — so
deduction fails, and it propagates through `immer::set` to every TU that touches
`state3/account_substate.hpp`. Upstream master still had it on 2026-07-29, so
the workaround generates a patched copy of that one header at configure time and
puts it ahead of immer's own include directory, leaving the submodule clean.
Remove the block once upstream lands `std::max<std::size_t>` and the submodule
is bumped.

## Witnesses must carry real mainnet blocks

The guest picks its EVM revision from the block's number and timestamp on the
**mainnet fork schedule**, so a witness has to describe a real mainnet block.
Fixture witnesses dumped from the execution-spec tests (block 1, timestamp 1000,
Cancun-shaped header) hit `MONAD_ASSERT(false, "unsupported fork")` instead.
That is the documented design assumption rather than a defect, but it does mean
the spec-test corpus cannot be replayed without carrying the fork in the
witness.

Blocks 22200001-22200005 are Cancun-era, which bounds what the corpus
exercises. EIP-2537 activated with Prague, so the BLS12-381 shims (0x0b-0x11)
and `bls12_map.rs` are unreachable on this corpus and are covered only by the
golden vectors; reaching them needs a Prague-era block. Block 22200005 does
carry a blob transaction, so `zkvm_kzg_point_eval` runs against a real mainnet
input and not only the c-kzg vectors.

`BLOCKHASH` resolves from the witness rather than from a live chain.
`zkvm/guest/ffi.cpp` seeds the block-hash buffer from the witness's ancestor
headers, which arrive ascending and contiguous, ending at the parent — exactly
the order `BlockHashBufferFinalized::set` requires, since it rejects a number
that is not the one after the last. Three of the five corpus blocks read
`BLOCKHASH`, so the path is covered. The seeding lives in the shared C++ guest,
so it is backend-independent rather than specific to OpenVM.

## Where the rest of the rationale lives

Kept next to the code rather than restated here:

- Accelerator input validation, why scalar multiplication is a raw double-and-add
  rather than `IntrinsicCurve::msm`, why results are asserted reduced before
  serialisation, and how the isogeny and trusted-setup constants were generated
  — `src/accel.rs` and `src/bls12_map.rs` doc comments.
- The `.init_array` walk and why an empty range is safe rather than a skipped
  initializer — `runtime::run_init_array`.
- Input framing and `num_public_values` — the constraints section at the end of
  this file.

## Proving baseline

Measured 2026-07-30 on the pinned fork tag, 16 cores / 125 GB, `parallel` and
`jemalloc` on. Re-measure after any version bump: segment counts are
version-specific, because beta.2 restructured `SegmentationConfig` (the
`main_cell_weight` / `interaction_cell_weight` / `base_field_size` memory
model), and the same block segmented 59 ways on upstream v2.0.1 against 63
here.

Block 22200003 (1.4 MB witness, 454 M instructions, 63 segments), end to end:

| phase | time |
|---|---|
| keygen | 10.7 s |
| core proof | 5,817 s |
| recursion | 670 s |
| **end to end** | **6,487 s** |
| verify | 0.3 s |

Peak RSS for the run: **48.5 GiB**. The driver reports it once, at exit, rather
than per phase — it comes from `VmHWM`, a process-wide high-water mark, so a
per-phase column of it would repeat the largest phase's figure and read as a
measurement while carrying one number.

This is repeatable. Proved again later the same day as the control arm of the
autoprecompile comparison below: core 5,814 s, recursion 655 s, end to end
6,469 s, same 63 segments, same 48.5 GiB — every phase within 0.3% of the table
above except recursion, at 2.2%.

Three things follow.

**Core proving is ~90% of the cost, recursion ~10%.** Anything aimed at
per-block proving work — powdr's autoprecompiles, a bigger accelerator set —
acts on the dominant term. Verification is free.

**Only ~8 of 16 cores are used** (`user`/`real` = 8.0). Not a configuration
mistake: OpenVM proves segments strictly sequentially — its own doc comment on
`prove_continuations` says the next segment's proof does not start before the
current one finishes, there is no parallel variant, and no setting for it. Only
the inside of a single segment's proof is parallel. So per-block latency is
linear in segment count and cannot be tuned down; `--segment-memory-gib` makes
it *worse*, since smaller segments mean more of them.

**48.5 GiB peak caps this host at two concurrent block provers.** That, not the
idle CPU, is what limits throughput — the spare cores cannot be filled with more
blocks without lowering `--segment-memory-gib` to trade per-block latency for
host density. Keygen aside (2.2 GiB before core proving starts), the run reaches
that peak during core proving and stays there, so it is a per-block cost rather
than a transient.

At 92 s per segment, the rest of the corpus extrapolates as:

| block | witness | instructions | segments | core proof |
|---|---|---|---|---|
| 22200003 | 1.4 MB | 454,072,708 | 63 | **1.6 h (measured)** |
| 22200005 | 2.2 MB | 876,809,153 | 114 | ~2.9 h |
| 22200001 | 2.5 MB | 1,069,292,109 | 135 | ~3.5 h |
| 22200004 | 3.7 MB | 1,534,352,562 | 201 | ~5.2 h |
| 22200002 | 3.6 MB | 1,711,202,526 | 219 | ~5.6 h |

Segments are sized by a memory budget, so they are roughly equal-cost by
construction and the extrapolation is first-order sound — but instruction mix
varies, so treat the estimates as estimates.

What remains unmeasured is the **guest-side** ceiling: OpenVM gives 512 MB of
address space and a ~2 MB stack, and the bump allocator never frees. All five
blocks fit; nothing here says where the limit is. That wants a deliberately
large witness, not a sample of five.

## Autoprecompiles

`script/`'s second binary, `monad-zkvm-openvm-powdr` (behind the `powdr`
feature), runs the guest through powdr's autoprecompile pipeline: synthesise a
merged circuit per hot basic block, keep the top N, inject them, prove. The
hand-written precompiles are untouched — powdr's `allowed_opcodes()` allowlist
keeps the SHA-256, Keccak and curve opcodes out of the candidate set, which is
what lets the two coexist.

```
cd script
cargo run --release --features powdr --bin monad-zkvm-openvm-powdr -- \
    --input /path/to/22200003.witness --autoprecompiles 16 \
    --artifacts-dir /path/to/cache --recursion
```

Drop `--recursion` to stop after core proving, `--segments` to stop after
metering, `--mock` to check constraints without building a STARK.

Block 22200003, proved both ways back to back on the same host — the command
above against the baseline driver's `--prove`. Sequentially, not concurrently:
one prover peaks near 48 GiB and uses ~8 of 16 cores, so two would fit in 125 GB
and fill the machine, but they would contend and inflate both arms by an unknown
and not necessarily equal amount.

| phase | none | 16 APCs | |
|---|---|---|---|
| keygen | 10.3 s | 10.4 s | — |
| core proof | 5,814.1 s | 3,781.0 s | **1.54x** |
| recursion | 655.0 s | 514.9 s | 1.27x |
| **end to end** | **6,469.1 s** | **4,295.9 s** | **1.51x** |
| verify | 0.3 s | 0.3 s | — |
| segments | 63 | 43 | 1.47x fewer |
| peak RSS | 48.5 GiB | 48.3 GiB | — |
| CPU seconds | 55,010 | 35,755 | 1.54x less |

Both arms committed the expected post-state root and both proofs verified, so
this is a like-for-like comparison of the same computation. The no-APC arm also
reproduces the baseline section above to within 0.3%, which is the reason to
trust the pair: the measurement is repeatable, not a single sample.

Four things that were not obvious before proving it.

**Per-segment cost goes down, not up.** 92.3 s per segment without
autoprecompiles, 87.9 s with — 4.7% cheaper. The expectation was the opposite:
an autoprecompiled segment carries a wider AIR, so some of the segment
reduction should be paid back per segment. It is not, which is why the measured
1.54x on core proving beats the 1.47x the segment ratio predicts. Segment count
is therefore a slightly *conservative* predictor here, not an optimistic one.

**Recursion gains less than core does** (1.27x against 1.54x). Fewer segments
means a smaller recursion tree, but the tree's depth moves in steps, so its cost
is not linear in segment count the way core proving is. Since recursion is only
~10% of the total, this barely dents the end-to-end figure.

**The speedup is free in memory.** 48.3 GiB against 48.5 GiB, so the host still
fits the same two concurrent provers. This is a throughput gain outright, not
latency traded for host density. Both arms also sat at ~8 of 16 cores (815% and
847% CPU), so the sequential-segment bottleneck is untouched — the saving is
less work, not better parallelism, which the CPU-seconds row confirms.

**Setup is not where the cost went.** Keygen is unchanged despite 16 injected
circuits, and the APC pipeline itself — generate, select, setup — took 22 s off a
warm `--artifacts-dir` against a 4,296 s prove. Autoprecompiles are close to
pure profit on a block this size.

The return diminishes fast, though: 8 APCs already reach 45 segments and 16 only
buys two more, so the interesting range to sweep is below 8, not above 16.

### 22200003 is the corpus's weakest case

Segment counts across the whole corpus, at 16 APCs. These are cheap to collect —
metered execution, minutes rather than hours — and now known to *understate* the
speedup, since per-segment cost falls too:

| block | instructions | none | 16 APCs | fewer by |
|---|---|---|---|---|
| 22200003 | 454 M | 63 | 43 | 1.47x |
| 22200005 | 877 M | 114 | 70 | 1.63x |
| 22200001 | 1,069 M | 135 | 85 | 1.59x |
| 22200004 | 1,534 M | 201 | 122 | 1.65x |
| 22200002 | 1,711 M | 219 | 129 | 1.70x |

**Autoprecompiles help more on bigger blocks, not less.** The measured 1.51x
end to end above is therefore the corpus floor rather than a typical figure —
22200003 is the smallest block and the weakest case in it. The likely reason is
that a longer block runs the same hot basic blocks more times, so a fixed set of
16 covers proportionally more of the work.

### One APC set works for every block

Selection is PGO-driven, so `--profile-input` is what the APC set is derived
from and `--input` is what gets proved. They are separate because the intended
shape is to profile once and then prove every block against the same set — which
matters more than a tuning knob, since the APC set is baked into the verifying
key and changing it is a parameter change for verifiers.

That shape costs almost nothing. Profiling all four other blocks on 22200003
instead of on themselves gives 70 / 87 / 124 / 129 segments against the 70 / 85 /
122 / 129 above — two blocks identical, two worse by two segments, under 2.4% at
worst. Correctness was never at risk (autoprecompiles are semantics-preserving,
and all five blocks committed their expected post-state root under both sets);
what is new is that the *benefit* transfers too.

`--artifacts-dir` caches the generate/select/setup stages keyed on their own
arguments, which is what makes an `--autoprecompiles` sweep cheap — the generate
stage is shared across selections, and a re-profile only invalidates from select
onward.

### `-fno-jump-tables`

The guest is built with this on OpenVM only. GCC emits a switch jump table as
one rodata word per case holding `case_target - table_base`, which on RISC-V is
an `R_RISCV_ADD32`/`R_RISCV_SUB32` relocation pair; powdr's ELF reader accepts
only `R_RISCV_32` in data sections and panics on anything else. A Rust guest
never produces label-difference pairs, so upstream has not needed to handle
them — this guest produced 395.

It costs almost nothing here: 453,986,359 instructions against 454,072,708
with jump tables, a 0.019% *decrease*, and the same 63 segments. So the
baseline above stays comparable and did not need re-measuring.

## Constraints inherited from OpenVM

- Input framing: the witness must be exactly one `StdIn::write_bytes` vector
  on the host; `read_input` exposes only the first record (idempotent).
- Public values are 4-byte words, zero-defaulted. `num_public_values` is the
  size of that address space **in bytes** and must be 8 × a power of two
  (`CHUNK` = `DIGEST_SIZE` = 8). It defaults to 32, which fits the witness
  guest's 32-byte post-state root and a *passing* precompile run's 20-byte
  summary, but not that guest's worst case of 244 B (16-byte PR01 header +
  4-byte count + 32 × 7 bytes of failure log); diagnosing more than one failed
  vector needs 256. This cannot be set in `openvm.toml`: `SdkVmConfig` defaults
  the whole `system` field, but `SystemConfig` declares no per-field serde
  defaults, so naming the table obliges you to spell out
  `max_constraint_degree` and every address space of `memory_config`. The host
  driver calls `SystemConfig::with_public_values(256)` instead, which is why
  `cargo openvm run` and `script/` disagree on the width of the committed
  output for the same guest.
- `zkvm_halt` collapses status to 0/1 (the `terminate` custom instruction
  takes the exit code as an immediate).

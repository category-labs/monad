# Airbender spike

The Monad guest (C++, rv32im) on ZKsync Airbender's transpiler VM, pinned to
the Ethproofs "Airbender v3" stack: zksync-airbender `bd0d515` and
airbender-platform `68fc060` (matter-labs/ethereum-prover
`.github/stack-revisions.env`).

- `../runtime.c`, `../start.S`, `../link.x` — the bare-metal rv32 runtime: entry,
  witness input over the non-determinism CSR, word-wise mem*, output registers.
- `../keccak_delegation.h` — Keccak-f through the 361-call keccak_f1600
  delegation.
- `../accel/` — every zkvm_* accelerator over airbender-crypto, a no_std
  staticlib.
- `../runner/` — `cargo airbender run`/`flamegraph` on airbender-host's
  `run_with_source`, with a host that answers the guest's queries (below).

## Layout and prerequisites

The Cargo paths and the scripts assume one work directory, `MONAD_ZKVM_WORK`
(by default the directory two above this checkout):

```
$MONAD_ZKVM_WORK/airbender/<this checkout>
$MONAD_ZKVM_WORK/airbender/stack/{zksync-airbender,airbender-platform}  # the pins above
$MONAD_ZKVM_WORK/airbender/build-rv32/      # the guest library's CMake build (link.sh's GUESTLIB)
$MONAD_ZKVM_WORK/airbender/out/             # ELFs, inputs, test outputs
$MONAD_ZKVM_WORK/run/w/rpc_<block>.witness  # witnesses (the ZisK guest's tooling)
```

- airbender-platform with `airbender-crypto-glv4.patch` applied (the GLV4
  ecrecover check, `secp256k1/recover_glv4.rs`).
- xPack riscv-none-elf-gcc 15.2.0 (`TC_DIR`, default
  `~/.local/xPacks/xpack-riscv-none-elf-gcc-15.2.0-1`), Boost
  (`CMAKE_PREFIX_PATH`), Rust `nightly-2026-08-09`.
- `FATAL_HOOK`: a header force-included into the guest that defines
  `BOOST_OUTCOME_SYSTEM_ERROR2_FATAL` as a trap (default
  `$MONAD_ZKVM_WORK/fatal_hook.h`).

## Build

- `build.sh <out_dir> [MONAD_ETH_OSAKA]` — configures and builds the rv32im
  guest library, links it with stub accelerators, and reports ROM use and any
  instruction Airbender cannot prove (signed MULH/DIV/REM, atomics). The
  optional revision builds a single-fork guest.
- accelerators: in `../accel`,
  `cargo +nightly-2026-08-09 build --release --target riscv32im-unknown-none-elf`.
- `link.sh [objects...]` — runtime + guest library (`GUESTLIB`) + accelerators
  (`RUSTLIB`) + libgcc into `out/guest.elf` (`OUT`). `stubs.c`: weak stand-ins
  that abort, for test ELFs without accelerators.
- runner: in `../runner`, `CARGO_TARGET_DIR=<airbender-platform>/target cargo
  build --release`.

## Inputs

The guest reads its own input layout, not the ZisK guest's:
`mk_ab_input.py <block>...` rebuilds the witness blob from
`run/w/rpc_<block>.witness` with filler bytes (Tag::PAD) and framed branches
(Tag::BRANCH_FRAMED, SLOT marks) so that copies move whole words, and the codes
8-aligned in place with at least 33 zero bytes around each (`--plain`
reproduces the ZisK blob byte for byte). `mk_ab_min.py` makes the minimal
variant (the parent header and only the EIP-2935 slots the block touches); it
needs the ZisK study's `minw` tooling.

## Running

`ab_run.py <elf> <block> [--flamegraph out.svg]` runs one block in the runner
(`ABIN=1` for the Airbender input, `STOCK=1` for plain `cargo airbender run`)
and prints the expected block hash beside the output registers.

The guest asks the host through the non-determinism CSR: a tag, the operands'
addresses, then the answer's words. Every answer is checked in the guest.

| tag | query | check |
|---|---|---|
| `0x4d445601` | u / v (udivrem, DIV/MOD/SDIV/SMOD) | q·v fits, u - q·v no borrow, remainder below v |
| `0x4d445602` | 512-bit / 256-bit (mulmod, addmod) | as above, on both halves |
| `0x4d445610`..`13` | secp256k1 divide, sqrt (+ non-residue flag), invert, scalar invert | one multiplication each |
| `0x4d445614` | ecrecover key Q and short (k0, k1, m0, m1) | the relation, Q on the curve, one 8-stream MSM |
| `0x4d445620` | bn254 base-field divide | one multiplication |

Runner options: `--transcript t.hex` records every word read, an input with
which the stock `cargo airbender run`/`prove` replays the run;
`--corrupt <n>:inc|dec|flip|zero|flag[:<query>]` and
`--corrupt-recover <n>:negq|k0|swap|scale|negall|nokey` answer wrongly, and
the guest must halt (the true variants `scale`, `negall`, `nokey` must not).

## Tests

- `int128_test.cpp` (with `int128_test_halt.cpp`), `div_edge_test.cpp` — the
  no-`__int128` arithmetic against `unsigned __int128`, on the host (build
  line in the file).
- `oracle_div_test.sh` — udivrem, sdivrem, mulmod and addmod with host
  quotients against the software Knuth division, in the VM.
- `keccak_align_test.sh` — the sponge at every offset in a word (0-7) and
  lengths 0-700 against an aligned copy.
- `ecrecover_hint_test.sh` — the accel crate's `ecrecover-selftest`: hinted
  against default hooks on random and edge inputs.
- `ab_pt.py`, `ab_pt_all.sh <elf>` — the go-ethereum precompile golden vectors
  (zkvm/test/precompile_tests) in the VM, per precompile. Build the ELF with
  `RT_CFLAGS=-DMONAD_ZKVM_AIRBENDER_PRECOMPILE_TESTS` and stubs compiled with
  `-DSTUB_FAIL`.

## Invariants

The optimizations rest on these; keep them when changing the guest:

- Fresh memory reads zero (Airbender's RAM argument fixes every address's first
  value at 0) and the allocators never hand memory out twice: the EVM memory
  pool and the trie offset map are not cleared, the lazy JUMPDEST bitmap and
  chunk ends start empty, and the trie walk's PAD/SLOT marks start clear.
- Every taken jump tests the gas (termination with deferred gas tests), and no
  untested opcode reads the witness (BLOCKHASH is tested).
- `is_jumpdest16` without a bound test needs zero bytes after every code.
- The input buffer is rewritten in place by `frame_branch`: a commitment to the
  raw witness must be taken before the walk. `encode_current`'s span over a
  patched frame is read-only.
- Delegation circuits reject operands in ROM: read-only data is copied to RAM
  at start, and anything handed to a delegation must live in RAM.

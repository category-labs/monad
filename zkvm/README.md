# monad zkVM guest

Executes monad witnesses inside a zero-knowledge VM: the guest ingests a
reth-format execution witness, rebuilds the partial state trie, runs the block
it carries, and commits the block hash -- and on the L2 arm the message anchor
and the block number with it.
The C++ guest library is shared across backends. On ZisK a Rust guest crate
owns the entrypoint and the input/output ABI (via ziskos); on SP1 the
entrypoint (`program/main.c`) and the IO/accelerator ABI come from `libzkevm.a`,
leaving only the host-side driver in Rust.

## Layout

```
zkvm/
├── core/                 # bare-metal libc / libstdc++ shims and ABI headers
│   └── zkvm_halt.h
├── category/             # mirror tree shadowing host headers (BEFORE include path)
├── guest/                # C++ library called from every backend
│   ├── execute_witness.cpp # monad_zkvm_execute_witness: witness in, values out
│   ├── execute_block.cpp   # sequential block execution
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
value, both from
[`zkvm_io.h`](../third_party/zkevm-standards/standards/io-interface/zkvm_io.h).
On ZisK the guest is a Rust crate and those symbols are provided by `ziskos`;
on SP1 there is no Rust guest — the entry is `program/main.c`, and
`read_input` / `write_output` (plus `_start`, the allocator, and the `zkvm_*`
accelerators) come from `libzkevm.a`, built from the SP1 zkEVM SDK source at
build time.

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
- [ZisK](https://github.com/0xPolygonHermez/zisk) ≥ v1.3.1-alpha
  (`ziskup` from <https://github.com/0xPolygonHermez/zisk>) — installs
  `cargo-zisk`, `ziskemu`.
- [SP1](https://docs.succinct.xyz/) ≥ v6.2.x (`sp1up` from
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

The official profile requires ZisK 1.3.1-alpha, GCC 15.2.0 and the baseline
codegen flags. The profile also requires the ZisK JUMPDEST precompile to occur
in the linked ELF. It embeds the commit and build identity in the ELF, then
audits the result and writes `<elf>.build.json` with the ELF hash. Keep that
manifest with published benchmark artifacts.

DMA lowering is disabled in this initial profile. Build-dependent optimisations
must extend the feature list and audit in the same commit; source-only changes
are already identified by the commit and ELF hash. Use direct `cargo-zisk build`
for diagnostic A/B builds, which do not produce an audited manifest.

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

**Ethereum** — one value:

| Offset | Size | Value |
|--------|------|-------|
| 0 | 32 | block hash, over the header with the COMPUTED state root sealed in |

The block hash is sufficient on its own: the computed root is sealed into the
header before it is hashed, so pinning the hash against the canonical chain at
that height pins the state root, the parent, and every other header field in
one comparison. Publishing the roots beside it would add nothing a verifier
could not already derive.

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
xxd -s 0  -l 32 /tmp/zkvm-output.bin   # block hash

# L2
xxd -s 0  -l 64 /tmp/zkvm-output.bin   # parent block hash || block hash
xxd -s 64 -l 40 /tmp/zkvm-output.bin   # anchor || block number
```

A diagnostic build appends the `MONAD_ZKVM_KECCAK_SITES` tail after these, so
their offsets never move. That tail is 152 bytes, which with the Ethereum
arm's 32 comes to 184 of ZisK's 256-byte committed output. `MONAD_ZKVM_L2` and `MONAD_ZKVM_KECCAK_SITES` remain a
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

That builds a guest to check, not one to measure. A dev build leaves five of
the six levers the official profile forces switched off, and the official
profile refuses L2, so a guest to benchmark sets them itself --
`MONAD_ZKVM_OFFICIAL_PROFILE=OFF;MONAD_ZKVM_ZISK_DMA=ON;MONAD_ZKVM_KECCAKF_MEMO=ON;MONAD_ZKVM_WIDE_MEMORY_SIZE=ON;MONAD_ZKVM_VARCODE_CACHE=ON;MONAD_ZKVM_NO_DIRTY_ACCOUNTS=ON;MONAD_ZKVM_NO_MERGE_CONSTRAINTS=ON`
ahead of the nine values -- with `RISCV_TOOLCHAIN_DIR` and
`CC_/CXX_riscv64ima_zisk_zkvm_elf` pointing at the DMA-patched GCC 15.2.0
that `ZISK_DMA` needs. Build each configuration in its own worktree:
`cargo-zisk` writes to `target/elf` whatever `CARGO_TARGET_DIR` says, and the
CMake cache there keeps options a later build does not mention.

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
the tag; in front of it `decode_block_l2` and `execute_witness.cpp` name no
cipher at all.
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
about 7x, since the ECDH's work is precompiled and the sponge's is not. On the
generated corpus the sponge is 1.5x the ECDH in steps; see
[Where the L2's share goes](#where-the-l2s-share-goes).

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
the block-hash output, which is the cheaper check to run first: it exercises
the generator and the trie without the cipher in the way.

### The benchmark corpus, and what it costs

The three scenarios above prove the generator works; they say nothing about
what a block costs, because twenty accounts and two blocks cannot. `--preset`
generates a corpus at scale instead: a genesis of `--accounts` holders, then
`--blocks` blocks that each aim to touch `--distinct` of them.

```sh
# The design document's two inverse cases. Wholesale is hundreds of
# institutions moving large amounts with an anchor every block; payouts is one
# payer fanning out over a million holders.
./build/zkvm/guest/monad-zkvm-corpus-gen --out /tmp/corpus-payouts \
    --preset payouts --accounts 1000000 --blocks 200 --distinct 500 \
    --sk <64 hex> --salt <64 hex>

# The dispersion sweep: one corpus per point, each in its own subdirectory.
./build/zkvm/guest/monad-zkvm-corpus-gen --out /tmp/sweep \
    --preset payouts --accounts 1000000 --blocks 4 \
    --shape uniform --sweep 50,200,500,2000,5000

# The same two cases as the document describes them, over wrapped ERC-20
# tokens: payment-versus-payment between banks, and a payroll platform with
# an earn vault and three exits. See "The document's flows" below.
./build/zkvm/guest/monad-zkvm-corpus-gen --out /tmp/wholesale-cbdc \
    --preset wholesale-cbdc --blocks 200 --sk <64 hex> --salt <64 hex>
./build/zkvm/guest/monad-zkvm-corpus-gen --out /tmp/worker-payouts \
    --preset worker-payouts --accounts 1000000 --blocks 200 --distinct 500 \
    --sk <64 hex> --salt <64 hex>
```

**Genesis does not go through a `State`.** `State::set_storage` probes two
linear-scan containers per call and `FlatStorage::find` is a scan in a host
build -- the open-addressed index above it is `#ifdef MONAD_ZKVM_ZISK`, so only
the guest gets it. That is quadratic in the slots already on an account, and a
million of them measured at 64 minutes. `GenesisSink`
(`zkvm/test/corpus/genesis_bulk.hpp`) builds the `StateDeltas` directly, the
way `load_genesis_state` does: **11 seconds for a million accounts.** Two tests
hold it honest -- the fast route gives the same state root as the `State` route,
and chunking does not change it.

`manifest.csv` records the regressors beside each witness:
`intended_distinct`, `acct_leaves`, `storage_leaves`, `branches`, `exts`,
`digests`, `blob_bytes`, `code_bytes`. They come from `witness_stats`, which
tiles the node blob with the guest's own `checked_end` and aborts if the tiling
is not exact -- a counter that had the grammar wrong would otherwise return
plausible, wrong numbers.

#### The two corpora

Both presets at two hundred blocks, generated and checked end to end. The
figures are the L2 arm's; the plaintext arm's witnesses are 4-5 % smaller and
otherwise the same shape.

| | `wholesale` | `payouts` |
|---|---:|---:|
| accounts | 500 | 1,000,000 |
| blocks | 201 (15,537,395-15,537,595) | 201 |
| transactions per block | 21 | 500 |
| witness, median | 78 KB | 859 KB |
| witness, min-max | 23-132 KB | 798-916 KB |
| leaves touched, median | 42 | 553 |
| digests per leaf | 5.8 | 29.7 |
| gas, median | 0.50 M | 11.45 M |
| corpus size | 16 MB | 172 MB |

Every witness in both is accepted by the guest under `ziskemu` (below). The
chain holds: `post_root[n] == pre_root[n+1]` and
`block_hash[n] == parent_hash[n+1]` across all 201, the numbers are contiguous,
all 201 post-state roots are distinct -- the state moves every block rather than
being re-proved -- and 200 of the 201 L2 blocks carry a non-zero anchor, which
the guest republishes exactly. The first block of every corpus deploys the
spoke, one transaction whatever the preset, and is left out of every figure
below.

**Wholesale is about six times cheaper per block than payouts, and eighteen
times in the part of the cost that depends on the block** -- the design
document's two inverse cases showing up in the measurement: wholesale is the
cheap end, and payouts is what sizing has to be done against.

Note that the depth law below was fitted at a million accounts, and wholesale's
5.8 digests per leaf sits well outside its range -- 500 accounts is under two
levels of trie. Do not read the fit as covering it.

#### The document's flows

The two presets above move native balances between EOAs, so a holder is an
account leaf and a transaction is a transfer. That is the cleaner experiment on
the account trie -- the depth law below was fitted on it -- but it is not what
the design document describes. `wholesale-cbdc` and `worker-payouts` follow the
document's own flows, over three contracts in `zkvm/test/corpus/contracts/`:

- **`WrappedToken`**, one per natively wrapped L1 token: the setup's "ERC-20 L2
  smart contracts for the wrapped tokens". Eligibility is enforced in the
  token, as the payout case requires, because "a transferable balance can be
  moved by its holder to destinations the platform does not control": a
  balance moves only between holders the token's admin has admitted. The flag
  is the top bit of the balance slot, the way USDC v2.2 packs its blacklist
  state, so checking it reads no slot a transfer would not read anyway -- a
  separate registry, in the style of ERC-3643, would add at least a slot per
  party per transfer. Leaving the L2 burns, and sends the L1 bridge a message
  through the spoke. There is no mint: the spoke records L1 anchors, but the
  operator posts them and nothing the proof publishes ties them to the hub, so
  a mint against one would be money the operator creates. Every balance exists
  at genesis.
- **`PvpSettlement`**, because "the two interbank legs are conditioned on one
  another and settle together or not at all". The debtor's bank proposes a
  payment, which stores only the hash of its terms; the intermediary -- paid by
  the first leg, paying the second, supplying the conversion -- settles both
  legs in one transaction, and either leg failing reverts both. The document's
  own version spans two L2s, with a lock on each and a coordinator on the L1.
  On one L2 a transaction is already atomic, and that is what this measures.
- **`EarnVault`**, the payout case's yield venue, "gated by closed-loop
  allowlisting ... so that only verified contractors can route funds into it",
  with withdrawal at any time. The return is not modelled: it changes the
  numbers in a slot, not which slots a block touches.

All three are seeded at genesis together with their storage rather than
deployed -- none has a constructor or an immutable -- and the spoke is deployed
in the first block exactly as in the native presets, so one configured guest
takes every corpus. The generator refuses a preset block in which any
transaction reverted: a reverted transaction still makes a valid block that
round-trips every root, and only its receipt says the block did less than the
workload claims. `WrappedToken.OnlyAdmittedHoldersMoveBalances` and
`PvpSettlement.BothLegsOrNeither` hold the two properties the document asks
for, eligibility and both legs or neither, on the checked-in bytecode.

| | `wholesale-cbdc` | `worker-payouts` |
|---|---|---|
| participants | 500 banks: 50 intermediaries holding both currencies, 225 in each | 1,000,000 contractors, 4,096 of whom send; 1,000 businesses; the platform |
| a block | settles the last block's 10 payments and proposes 10; one bank redeems reserves to the L1 | admits 10 contractors; pays 400 in 10 batches of 40, each funded by a business; 25 deposits into the vault and 25 withdrawals; 50 exits, by card, by redemption and to the L1 |
| transactions | 21 | 130 |
| gas, median | 1.25 M | 9.60 M |
| witness, median (min-max) | 112 KB (25-165) | 919 KB (860-981) |
| account / storage leaves touched | 25 / 75 | 115 / 616 |
| digests per leaf | 6.6 | 25.4 |
| corpus size | 22 MB | 176 MB |

A contractor who only receives has a balance slot and no account: nothing it
does creates one. So the million are in one storage trie, and the account trie
holds only the few thousand who send -- the storage-trie variant the native
presets leave out. Both corpora chain like the native ones, all 201 post-state
roots of each are distinct, and every L2 block after the first carries a
non-zero anchor.

#### What the dispersion is worth

Measured on this generator, 1,000,000 accounts, four blocks per point, L2 arm.
`N` is the accounts in the trie, `K` the leaves a block touched.

| distinct | leaves | digests | digests/leaf | witness | bytes/leaf | gas |
|---:|---:|---:|---:|---:|---:|---:|
| 50 | 58 | 2,394 | 41.5 | 113 KB | 1,964 | 1.2 M |
| 200 | 222 | 7,747 | 34.8 | 370 KB | 1,661 | 4.6 M |
| 500 | 552 | 16,430 | 29.8 | 806 KB | 1,462 | 11.4 M |
| 2,000 | 2,190 | 48,938 | 22.4 | 2,579 KB | 1,179 | 45.7 M |
| 5,000 | 5,440 | 96,674 | 17.8 | 5,477 KB | 1,007 | 114.3 M |

Three things fall out of the witness, and the first is why this corpus exists
at all.

**The access distribution does not matter; the distinct count does.** A leaf
touched twice in one block is free -- it is already in the witness -- so a
distribution can only reach the cost through the number of distinct leaves it
produces. Run with all three shapes at these five points (plaintext arm),
uniform, Zipf and hot-set agree to within **0.2-1.6 %** in witness bytes and
0.3-1.1 % in digests, with identical transaction counts, against a 2.3x swing
in digests-per-leaf across the points themselves. Frozen as
`WorkloadDispersion.TheShapeDoesNotChangeTheCostAtEqualDistinct`.

**The depth law is measurable.** `digests/leaf = 14.5 x log16(N/K) - 9.5`,
**R2 0.998** on the L2 arm, and `14.0 x log16(N/K) - 8.6` on the plaintext arm:
fourteen digests for each level a path diverges from its neighbours, less about
nine for the top levels where every path is shared. The naive prediction was
fifteen per level with no offset. Mainnet cannot establish this -- the same fit
over 504 mainnet witnesses gives **R2 0.065**, because mainnet mixes storage
tries of wildly different sizes and confounds dispersion with the shape of the
state. A flat million-account trie separates them.

**The witness is sublinear in dispersion; the cost is not.**
`witness_bytes = 4225 x distinct^0.843`, **R2 0.9999** (`4291 x distinct^0.830`
in plaintext) -- doubling the distinct accounts costs **1.79x the bytes, not
2x**, because the extra paths land under prefixes the earlier ones already paid
for. But bytes are not what these blocks spend most on: measured, the variable
cost goes as `distinct^0.96`, because each distinct account here is a
transaction, and a transaction costs more than its share of the witness.

#### What a block costs

Measured under `ziskemu` 1.2.0-alpha, on every workload block of the four
corpora and the sweep, both arms, each run first checked against the manifest. COST is
ZisK's own cost model (`ziskemu -X --stats`), taken through `zkvm-bench`'s
`compare.run_zisk` so that a figure here and one in a `compare` report come
from one parser.

```sh
# Verify every witness against its manifest, then take steps and COST.
export ZKVM_BENCH=<zkvm-bench checkout>
zkvm/test/corpus/bench.py --arm l2 --elf <L2 ELF> --emu ~/.zisk/bin/ziskemu \
    --corpus /tmp/wholesale /tmp/payouts /tmp/sweep --out l2.csv
zkvm/test/corpus/bench.py --arm plain --elf <plaintext ELF> --emu ~/.zisk/bin/ziskemu \
    --corpus /tmp/wholesale-plain /tmp/payouts-plain /tmp/sweep-plain --out plain.csv

# The document's flows in CSVs of their own: bench-report.py fits whatever it
# is given, and the per-transaction fit below is the native presets'.
zkvm/test/corpus/bench.py --arm l2 --elf <L2 ELF> --emu ~/.zisk/bin/ziskemu \
    --corpus /tmp/wholesale-cbdc /tmp/worker-payouts --out l2-tokens.csv

# A zkvm-bench generation reads as it is: <n>.witness against <n>.blockhash.
zkvm/test/corpus/bench.py --arm plain --elf <plaintext ELF> --emu ~/.zisk/bin/ziskemu \
    --corpus $ZKVM_BENCH/guests/monad/gen/r10zisk-rtp-25815000-25815199-cb7b6b1ae/witnesses \
    --out mainnet.csv

zkvm/test/corpus/bench-report.py --l2 l2.csv --plain plain.csv --mainnet mainnet.csv
```

**The ELFs are built the way the benchmark builds its own**, and it matters: a
bare `cargo-zisk build --release` leaves five of the six levers the official
profile forces switched off, and measured 15 % more steps on a payouts block.
The plaintext ELF is the official profile; the L2 one cannot be (the guest
CMake refuses `MONAD_ZKVM_L2` there), so it is a dev build carrying the same six
levers -- `ZISK_DMA`, `KECCAKF_MEMO`, `WIDE_MEMORY_SIZE`, `VARCODE_CACHE`,
`NO_DIRTY_ACCOUNTS`, `NO_MERGE_CONSTRAINTS` -- with the DMA-patched GCC 15.2.0
that `ZISK_DMA` needs. A plaintext dev build with those levers gives the
official ELF's steps and COST exactly, on all 207 blocks compared, which is
what licenses reading the L2 ELF as the official guest plus the L2.

| | `wholesale` | `payouts` | `wholesale-cbdc` | `worker-payouts` |
|---|---:|---:|---:|---:|
| steps, L2 | 0.72 M | 12.97 M | 1.62 M | 12.52 M |
| COST, L2 | 0.413 G | 2.510 G | 0.534 G | 2.284 G |
| of which fixed | 0.287 G | 0.287 G | 0.287 G | 0.287 G |
| COST, plaintext | 0.403 G | 2.286 G | 0.521 G | 2.210 G |
| share of a median mainnet block | 4 % | 26 % | 6 % | 24 % |

**A fixed 287,309,824 of it is the same on every block**: `Base`, ZisK's ROM
and lookup tables (137 x 2^21), which the cost model charges once per run
whatever the run proves. It is 70 % of a wholesale block. A guest that proved
several blocks in one run -- this one proves one -- would pay it once, and on
wholesale two blocks per run would save more than making the block itself
free.

**The rest follows the transactions first.** Over the 420 workload blocks of
the L2 arm,

    COST - base = 3.08 M x txs + 791 x witness_bytes + 0.5 M        R2 0.99999

and the plaintext arm gives 2.66 M per transaction and 811 per byte. The
per-byte term is the trie's and is the same on both arms; the L2 is 0.42 M more
per transaction, +16 %. A payouts block spends 1.54 G on its 500 transactions
and 0.68 G on its 859 KB of witness.

**So prover cost is proportional to gas only above the floor.** On the payouts
sweep `COST - base = 174 x gas`, R2 0.9995: for one transaction mix, the part
of the cost that depends on the block is linear in gas even though the witness
is not. What makes COST per gas fall from 455 at 50 transfers to 175 at 5,000
is the fixed part, and the slope belongs to the mix -- outside the floor,
wholesale spends 253 per gas and payouts 194.

**The document's flows cost what their gas says, not what their transaction
count says.** The per-transaction law above was fitted where a transaction is a
transfer. On the token presets a transaction is a contract call -- for payroll,
forty transfers -- and the law misses the part of the cost above the floor by
38 % on `wholesale-cbdc` and 44 % on `worker-payouts`. Gas and witness bytes
carry all four mixes: over their 800 workload blocks on the L2 arm,

    COST - base = 144 x gas + 673 x witness_bytes - 3.2 M        R2 0.99998

within 0.4 % on every block of both payout presets, and a median of -4 % and
+2 % on the two wholesale ones, whose blocks are small enough for the constant
to show. Outside the floor the token presets spend 197 and 208 per gas, inside
the native range.

Settling payment versus payment doubles a wholesale block above the floor,
0.247 G against 0.126 G: about forty banks either way, but reached through two
tokens' storage and a settlement contract rather than as account leaves.
Payroll goes the other way. `worker-payouts` touches as many contractors as
`payouts` touches holders and costs 9 % less, 2.284 G against 2.510 G, because
batching pays four hundred of them in ten transactions: 130 signatures to
recover instead of 500 take secp256k1 from 0.22 G to 0.06 G, more than the
mapping slots and the million-slot storage trie add in Keccak, 0.58 G to
0.62 G.

**Mainnet, on the same ELF.** The 200 canonical blocks 25,815,000-25,815,199
(`zkvm-bench`'s `r10zisk-rtp` witnesses), every block hash reproduced: median
**9.67 G** COST (p10 5.84, p90 14.58), 63.4 M steps, 6.61 MB of witness,
1,432 COST per witness byte above the floor. A payouts block spends 2,586 per
byte, nearly twice as much: a transaction-dense L2 block is not a small mainnet
block, and the mainnet law below does not carry over to it -- the transaction
count is what it misses.

#### Where the L2's share goes

Paired block for block against the plaintext arm, which executes the same
transfers from the same seed:

| | steps | COST | COST - base |
|---|---:|---:|---:|
| `wholesale` | 1.09x | 1.02x | 1.08x |
| `payouts` | 1.12x | 1.10x | 1.11x |
| sweep, 50 to 5,000 transfers | 1.11-1.13x | 1.04-1.14x | 1.10-1.14x |
| `wholesale-cbdc` | 1.06x | 1.02x | 1.05x |
| `worker-payouts` | 1.04x | 1.03x | 1.04x |

What the L2 adds is paid per transaction -- a leaf to decrypt, its sponges, a
signature payload -- so it weighs less on the token presets, which reach the
same participants through fewer, heavier transactions.

Of the extra COST on a payouts block, 41 % is main-machine steps, 37 %
precompiles (Poseidon2 10 %, secp256k1 16 %, Keccak 4 %) and 16 % memory. By
function, on one 500-transaction block (`hotspots.py`, 12.81 M steps against
11.38 M):

- the software sponge around the Poseidon2 precompile, **0.96 M steps**:
  `L2Sponge::absorb` 0.51 M, the constructor 0.19 M, `squeeze` 0.16 M, byte
  packing 0.09 M;
- the ECDH, mostly the GLV scalar multiplication, 0.66 M;
- leaf decryption and the L2 block decode, 0.45 M;
- less about 0.6 M the L2 does not do: gas pricing (`gas_price`, `checked_mul`,
  the fee credits) and the plaintext decode.

What keeps the sponge at that: it checks its declared I/O pattern once per call
rather than once per element, absorbs and squeezes a rate block at a time, and
writes the first rate block without the modular addition -- until the first
permutation the rate is the zero it was built with, so adding into it is the
element itself. An absorbed element is then about sixteen instructions: the
load, the canonicity check, the Goldilocks addition and the store. The tag
block is copied whole rather than byte by byte, and it is hashed once rather
than once a sponge: SAFE's tag is a function of the domain, the merged I/O
pattern, the label and the context and of nothing else, and over one block the
context is fixed and a leaf's patterns differ from the last leaf's only by the
message length -- so the cipher context carries an `L2SpongeTags`, and a
block's leaves open their sponges on tags already computed. The cache is bound
to the context and label it last saw and empties itself when either differs,
so a tag is only ever served for the inputs it was computed from. None of this
changes what the sponge computes: `L2Sponge.KnownAnswers` and
`L2Cipher.KnownAnswerLeaves` pin its outputs, `L2Sponge.TagCacheIsTransparent`
holds the cached and uncached sponges equal, and every leaf of the corpora
above decrypts under it.

Each transaction's signing payload is built from the plaintext it was decoded
from, which `decode_block_l2` keeps for the block, rather than re-encoded field
by field -- the same bytes, as `DecodeBlockL2.EncodingsAreWhatEachTransactionWasDecodedFrom`
checks for legacy, EIP-155 and typed transactions.

The sponge is 1.5x the ECDH here, and most of what is left is the absorption
itself, at the sixteen instructions an element above. What the constructor
still costs, about 125 steps a sponge, is merging the pattern, checking the
cache's binding, finding the tag and zeroing the state.

#### What mainnet said, on `r8`

Over 504 mainnet witnesses joined to their measured cost on the `r8` guest
(the corpus and per-block figures in `zkvm-bench`):

| | fit |
|---|---|
| `blob_bytes = 40.0 x digests` | R2 0.9996 -- the blob **is** its digests, 82 % of its bytes |
| `COST = 2891 x witness_bytes` | R2 0.942; 2,371 -> 2,734 per byte from the 1st to the 10th decile |
| `keccak = 0.0093 x bytes^1.02` | R2 0.987 -- 12.4-13.0 keccak calls per KB, stable over a 40x range |
| `COST = 7.54e6 x touched_leaves` | R2 0.897 |
| `COST ~ leaves + code_bytes` | delta-R2 **0.000** -- code adds nothing once the leaf count is known |

The structural fits are properties of the witness and still hold. The slope is
not a constant of the guest: it was `r8` under the emulator and runtime of its
time, and this ELF spends 1,432 per byte on mainnet above the floor, about half. On
mainnet, witness bytes are the cost to within about 8 %; on the L2 corpus they
are the smaller of two terms.

#### What still has to be measured elsewhere

**Proving time.** Everything above executes under the emulator; COST is ZisK's
model of prover work, not a wall-clock. `zkvm-bench` proves on its GPU boxes,
and two things stand between these blocks and that path. Its root gate
(`profiling/series/root-ref.sh`) compares the first 32 bytes of the output
against a block hash or a state root, and on the L2 arm those bytes are the
parent hash, so the four values need a reference kind of their own. And
`cli/build-monad` builds the official profile only, which refuses L2.

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
| an "ancestor" sits at the block's own height | the parent-is-last check, `headers.empty()` |
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

That step has been taken, under `ziskemu` 1.2.0-alpha -- the runtime
`Cargo.lock` pins -- on the ELFs [the cost section](#what-a-block-costs)
measures: the official plaintext profile, and the L2 arm as a dev build carrying
the same six levers and the nine deployment values the tests use. Every witness
the scenarios and the four presets generate passes, on both arms: the guest
publishes exactly what the manifest recorded, the block hash on the plaintext
arm and the four values on the L2 one, including the 821 L2 blocks whose anchor
is non-zero.

| | plaintext | L2 |
|---|---:|---:|
| scenarios (transfers, evm, spoke) | 6 / 6 | 6 / 6 |
| `wholesale`, 500 accounts | 201 / 201 | 201 / 201 |
| `payouts`, 1,000,000 accounts | 201 / 201 | 201 / 201 |
| the dispersion sweep, 50 to 5,000 distinct | 25 / 25 | 25 / 25 |
| `wholesale-cbdc`, 500 banks | 201 / 201 | 201 / 201 |
| `worker-payouts`, 1,000,000 contractors | 201 / 201 | 201 / 201 |

What the L2 adds to each block is in
[Where the L2's share goes](#where-the-l2s-share-goes).

The plaintext ELF also reproduces the canonical mainnet block hash of all 200
blocks 25,815,000-25,815,199 from `zkvm-bench`'s `r10zisk-rtp` witnesses, 0.3 M
to 127.1 M steps. Witnesses from before the blob grammar moved `DIGEST` to `0xa0`
abort in the reader, which is expected: `ziskemu` exits 0 and leaves the output
zero, so a harness has to judge the bytes, never the exit status.

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

The `--input` path is read as raw bytes and handed over verbatim with
`SP1Stdin::write_slice` — no length prefix, and **not** `write_vec`, which
prepends framing that libzkevm's `read_input` (`read_vec_raw`) does not strip
and which would therefore corrupt the RLP. The ZisK framing above is the
emulator's own convention and has no counterpart here.

## Iterating on the C++ guest in isolation

The C++ guest library can be built independently of either Rust crate, for
fast iteration on `execute_witness.cpp` / `execute_block.cpp`:

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

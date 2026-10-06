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

**L2** — eight values, and **no state root**:

| Offset | Size | Value |
|--------|------|-------|
| 0 | 8 | domain chain id, big-endian u64 |
| 8 | 8 | domain block number, big-endian u64 |
| 16 | 32 | pre-state commitment |
| 48 | 32 | post-state commitment |
| 80 | 32 | message anchor |
| 112 | 32 | sequencing anchor |
| 144 | 33 | viewing public key, SEC1 compressed |
| 177 | 32 | salt commitment |

The middle three are the statement: **from this state, over these inputs, to
that state.** The pre-state commitment is blinded with the PARENT's number, so
it is byte for byte what that block's own run published as its final state --
the hub chains by one equality against the commitment it already holds, and
needs no derivation of its own. Nothing inside the circuit establishes that
link: the pre-state root is checked against an ancestor header the prover also
supplied, which is internal consistency and not a tie to what the hub accepted.

Around them is what a validator would sign and nothing else. The proof stands in for a
quorum of them, so what it publishes is that signature's arguments —
`stateTransitionDigest(domainChainId, domainBlockNumber, newStateRoot,
domainAnchor)` — plus the two things the digest does not reach: the input set,
and the keys this run was bound to.

**No block hash and no parent hash.** They were published to chain a block to
its parent, and this chain does not chain that way. A domain block has no header
of its own — the execution client runs its transactions against the **L1**
header and stores a two-field record, `{state_root, number}` — and the hub
orders transitions with its own `stateNonce` and a strictly increasing block
number. The number here is the L1 block's, and the sequence is sparse: an L1
block that sequences nothing for a domain produces no domain block at all.

**The state root is published blinded.** A root is a commitment, and a
commitment to a guessable value confirms guesses. On this chain the state IS
guessable from public data: the participants are registered on the L1, deposits
are public L1 transfers, and the ciphertexts were sequenced through the L1 in
the clear. Hashing is no defence — nothing is being inverted. So what goes out
is `H(salt ‖ state_root)`, the salt derived as
`H("monad-l2/state-salt/v2" ‖ salt_secret ‖ chainId ‖ number)` with the chain's
own hash. The number is there because a constant blinder would leave two blocks
of identical state publishing the same value, which on a low-volume chain says
which blocks did nothing; the chain id because nothing enforces that two domains
hold distinct secrets.

It costs the L1 nothing, and that is why it is possible at all: `DomainHub`
writes `newStateRoot` into `_commitments`, reads it back through
`readCommitment`, and never opens it — not by a merkle proof, not by the bridge,
which works off the recorded anchors. What does reopen it is the execution
client, which compares a finalized update against the root it committed, so that
comparison has to move to the commitment. **That change is not in this
repository**, and until it lands a real deployment would halt on the first
finalized update.

`salt_secret` is witness field [7] and is checked against the compiled
`MONAD_ZKVM_L2_SALT_COMMITMENT`, which needs saying because the reason is not
soundness. An unbound blinder costs nothing there — every proof still verifies.
What it costs is the confidentiality it exists for: a producer supplying zeros
publishes a predictable commitment and nothing anywhere says so.

**The sequencing anchor binds the inputs.** Without it the tuple pins the result
of a computation and not what it ran on; a validator quorum covers that socially
and a single proof does not. It is taken with the chain's hash — `keccak256` in
a keccak chain, which the EVM computes for 30 gas a word; Poseidon2 in a
Poseidon2 chain, which a hub checking it pays for in Solidity — over the leaves
the block carried, rejected ones included. See
[`sequencing_anchor.hpp`](../category/execution/ethereum/sequencing_anchor.hpp)
and [DECISIONS.md](DECISIONS.md).

**The two keys are published, not left implicit in the ELF**, so that rotating
either does not change the verification key. The hub is meant to check them
against what it has registered for the domain; `registerDomain` has no field for
either today, which is the same contract change a proof mode needs.

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

1. **Chain and height** — the published chain id is this domain's, and the
   published block number is above the last it committed.
2. **The pre-state it accepted** — the published pre-state commitment equals
   the commitment the hub last committed for this domain. One equality, because
   the guest blinds it with the parent's number and so republishes exactly what
   that block's proof published as its final state.
3. **The inputs it authorised** — the sequencing anchor, compared against a
   digest of the ciphertexts the hub actually sequenced for this domain at this
   height. The guest publishes its half; where the hub's half comes from is an
   open protocol question, recorded in [DECISIONS.md](DECISIONS.md).
4. **The operator** — the signature this proof replaces, over
   `stateTransitionDigest(chainId, blockNumber, newStateRoot, domainAnchor)`,
   with the state commitment standing in for `newStateRoot`. And the two keys
   at the end of the output against the ones registered for this domain.

So the gap is not in the output format; it is that none of the four checks
above exists. The L2's soundness is conditional on an L1 side this branch does
not contain, and on the operator actually handing over the header rather than
only the tuple.

```sh
# Ethereum
xxd -s 0  -l 32 /tmp/zkvm-output.bin   # block hash

# L2
xxd -s 0   -l 16 /tmp/zkvm-output.bin  # chain id || block number
xxd -s 16  -l 64 /tmp/zkvm-output.bin  # pre-state || post-state commitment
xxd -s 80  -l 64 /tmp/zkvm-output.bin  # message anchor || sequencing anchor
xxd -s 144 -l 65 /tmp/zkvm-output.bin  # viewing public key || salt commitment
```

A diagnostic build appends the `MONAD_ZKVM_KECCAK_SITES` tail after these, so
their offsets never move. That tail is 152 bytes, which with the Ethereum
arm's 32 comes to 184 of ZisK's 256-byte committed output. `MONAD_ZKVM_L2` and `MONAD_ZKVM_KECCAK_SITES` remain a
configure-time error together: the L2's eight values are 209 bytes, so the two
would overrun the buffer outright.

## The L2 arm

`MONAD_ZKVM_L2` builds a guest for the L2: transactions arrive encrypted, an
end-of-block anchor of the messages emitted is published, and gas is metered
but not priced. It is a mode and not an optimisation — the witness grows two
fields, the operator secret and the blinder's, the chain changes, and the
consensus rules with it — so a witness built for one setting is rejected
outright by the other.

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
MONAD_ZKVM_L2_REVISION=MONAD_ETH_PARIS;\
MONAD_ZKVM_L2_SPOKE=0x<40 hex>;\
MONAD_ZKVM_L2_PENDING_SLOT=<n>;\
MONAD_ZKVM_L2_OPERATOR_PK_X=0x<64 hex>;\
MONAD_ZKVM_L2_OPERATOR_PK_ODD=<0|1>;\
MONAD_ZKVM_L2_SALT_COMMITMENT=0x<64 hex>" \
    cargo-zisk build --release
```

The operator key is compiled in, so the order is: pick a secret, run
`monad-zkvm-corpus-gen --pubkey <secret>` for the two `OPERATOR_PK` values,
configure with those, and hand the generator the same secret with `--sk`. The
generator checks the pair at startup and refuses to produce a corpus nothing
can decrypt.

`MONAD_ZKVM_L2_SPOKE` comes from the same tool: `--spoke-address` prints the
fixed predeploy address the corpus seeds the spoke at. Fixed and not
CREATE-derived, because the access check asks the spoke before every call and so
it has to exist from genesis, before anything could have deployed it. And `--salt-commitment <secret>`
prints `MONAD_ZKVM_L2_SALT_COMMITMENT` for a blinder secret, which the
generator then wants back as `--salt`.

**The chain's hash is Poseidon2 unless configured otherwise**
(`MONAD_ZKVM_L2_HASH`, `poseidon2` by default, `keccak` for Ethereum's). It is a
property of the chain like the values above, and it decides the hashes the
chain defines for itself: a block's hash -- what a parent hash names, what
BLOCKHASH returns and what the guest publishes --, the state blinder and its
commitment, and the logs bloom
([`chain_hash.hpp`](../category/execution/ethereum/core/chain_hash.hpp),
[`l2_config.cpp`](guest/l2_config.cpp)). It is also the default of the trie and
signature hashes below, so a build that names none of the three is the chain
with everything it defines on ZisK's Poseidon2 precompile. Two of the values
above follow it, which is why the tool prints them in a tree configured like
the chain: `--salt-commitment` hashes the secret with the chain's hash, and
`--spoke-address` derives the deployer's address with the signature hash. What
the EVM, a contract or the L1 hub computes stays keccak256 whatever it says: the
KECCAK256 opcode, code hashes, CREATE and CREATE2 addresses, transaction hashes
and the namespace anchor.

That builds a guest to check, not one to measure. A dev build leaves five of
the six levers the official profile forces switched off, and the official
profile refuses L2, so a guest to benchmark sets them itself --
`MONAD_ZKVM_OFFICIAL_PROFILE=OFF;MONAD_ZKVM_ZISK_DMA=ON;MONAD_ZKVM_KECCAKF_MEMO=ON;MONAD_ZKVM_WIDE_MEMORY_SIZE=ON;MONAD_ZKVM_VARCODE_CACHE=ON;MONAD_ZKVM_NO_DIRTY_ACCOUNTS=ON;MONAD_ZKVM_NO_MERGE_CONSTRAINTS=ON`
ahead of the seven values -- with `RISCV_TOOLCHAIN_DIR` and
`CC_/CXX_riscv64ima_zisk_zkvm_elf` pointing at the DMA-patched GCC 15.2.0
that `ZISK_DMA` needs. Build each configuration in its own worktree:
`cargo-zisk` writes to `target/elf` whatever `CARGO_TARGET_DIR` says, and the
guest's CMake tree, `target/guest-build`, is shared by every cargo target dir
and keeps options a later build does not mention.

**An L2 build analyses JUMPDESTs in software** (`MONAD_ZKVM_JUMPDEST_SOFTWARE`,
on by default there, refused by the official profile). ZisK proves at least
one whole instance of every state machine a run uses, however little the run
asks of it, and a block of 1 to 250 L2 transactions plans the same 18
instances -- the JUMPDEST precompile's among them, for the code of the few
contracts the L2 runs. In software the scan is about 9,600 steps a block, 1 %
of a 50-transaction block, in a Main instance such a block leaves mostly empty,
and the plan drops to 17 instances. Whether that shortens the proof is what
`zkvm-bench`'s `cluster/tests/l2-latency` times, block for block, against
`MONAD_ZKVM_JUMPDEST_SOFTWARE=OFF` -- which builds the guest of before the
lever byte for byte.

**Keccak-f can run in software too** (`MONAD_ZKVM_KECCAKF_SOFTWARE`, off by
default, with `MONAD_ZKVM_KECCAKF_MEMO=OFF`, refused by the official profile).
The Keccakf instance -- 14,462 permutations in 2^20 rows of 643 columns -- is
about a fifth of the plan of a block of 1 to 250 L2 transactions, which runs
from a hundred to nine thousand permutations. In software a permutation is
4,138 steps and about 2,400 Binary operations: a small block's Main and Binary
instances absorb them, a larger block's overflow. Measured under ZisK
1.3.1-alpha on the latency corpora, the instance areas taken from the proving
key's starkinfo (2^nBitsExt x columns, plus the compressor), the plan of a
block with the lever against the default build's is 0.79x for the transfer
blocks of up to 25 transactions, 0.85x at 50 and on the 21-transaction token
preset, 1.20x at 100, 1.62x at 250 and 2.41x on the 130-transaction
worker-payouts preset. Whether the proof follows the area is what
`l2-latency` times as a fourth arm, on the blocks of up to 250 transactions.

**The tries are built on Poseidon2** (`MONAD_ZKVM_L2_TRIE_HASH`, the chain's
hash unless set; `keccak` builds them as Ethereum does). The hash is a property
of the chain, so the host tree that generates its corpora and the guest that
proves them are configured alike; a guest of the other kind recomputes a
pre-state root no header holds, and halts.
Every trie the chain commits to -- the state and storage tries, and the ordered
tries behind the transactions, receipts and withdrawals roots -- then hashes its
nodes and keys with `monad_poseidon2_256`, through
[`category/core/trie_hash.hpp`](../category/core/trie_hash.hpp): ZisK's
Poseidon2 precompile in the guest, the same permutation in software on the
host. What Ethereum, a wallet or the L1 computes stays keccak: the KECCAK256
opcode, code hashes, contract addresses, transaction hashes and signatures, the
logs bloom, the block hash and the namespace anchor.

Measured under ZisK 1.3.1-alpha on the latency corpora regenerated from the same
seeds, the trie takes 86 to 95 % of a transfer block's Keccak-f permutations
away from ten transactions up, for about 1.75 Poseidon2 calls each and 2 % more
steps. What that does to the plan's area depends on the keccak that is left, and
so on the block:

| block | Poseidon2 trie | Poseidon2 trie, Keccak-f in software |
|---|---:|---:|
| 1 to 100 transfers | 1.00x | 0.79x |
| 250 | 1.03x | 0.82x |
| 500 | 1.05x | 0.91x |
| 1,000 | 0.96x | 0.93x |
| 2,000 | 0.85x | 0.94x |
| 5,000 | 0.81x | 1.02x |
| worker-payouts, 130 | 0.87x | 1.03x |

On the precompile, the keccak left -- about 1.5 permutations a transfer -- still
costs a whole Keccakf instance, so a small block gains nothing, and from 250
transactions the Poseidon instances the trie adds cost more than it saves; the
gain comes past 1,000, where the Keccakf instances it removes outnumber them.
With the remainder in software (`MONAD_ZKVM_KECCAKF_SOFTWARE`) the instance goes:
0.79x up to 100 transfers, where the keccak trie in software already overflows
Main and Binary. A contract-heavy block keeps more keccak -- the EVM's, the
bloom's -- and is better off on the precompile. `l2-latency` times both as two
more arms.

**The signatures are bound with Poseidon2 too**
(`MONAD_ZKVM_L2_SIGNATURE_HASH`, the chain's hash unless set). The curve stays
secp256k1 and the signature ECDSA -- its recovery already runs on ZisK's curve
precompiles, beside the encryption's ECDH. What changes is the two hashes keccak
supplies: the digest a transaction's or an authorization's signature signs, and
the hash that turns the public key it recovers into an address, both
`monad_poseidon2_256` over a label of their own (`monad-l2/tx-sig/v1`,
`monad-l2/address/v1`), through
[`signature_hash.hpp`](../category/execution/ethereum/core/signature_hash.hpp).
A stock wallet cannot sign for such a chain, since it signs keccak digests. The
address hash applies wherever the chain turns a key into an address -- a
sender, an authority, the ECRECOVER precompile -- so a key's address here is not
its Ethereum one, and the spoke, CREATE-derived from its deployer's address,
moves with it: `corpus-gen --spoke-address` in a tree configured this way prints
the chain's (`0x056bfe3f1ca91a3ac44b15ac68bc450b29faa04e` for the default seed).
Withdrawals name their L1 recipient, so bridging does not depend on the two
addresses agreeing.

Measured on corpora regenerated from the same seeds with both the tries and the
signatures on Poseidon2, every witness of which passes on both guests: the
keccak left falls from about 1.5 permutations a transfer to 0.3 -- the EVM's,
the anchor's and the bloom's, and per block the code hashes, the block hash and
the salt -- for two more Poseidon2 calls a transaction. With that remainder in
software, the plan's area against the keccak chain's:

| block | Poseidon2 trie, Keccak-f in software | and Poseidon2 signatures |
|---|---:|---:|
| 1 to 100 transfers | 0.79x | 0.79x |
| 250 | 0.82x | 0.82x |
| 500 | 0.91x | 0.88x |
| 1,000 | 0.93x | 0.87x |
| 2,000 | 0.94x | 0.81x |
| 5,000 | 1.02x | 0.78x |
| worker-payouts, 130 | 1.03x | 1.03x |

Up to 250 transactions keccak has nothing more to give: the plan is the 16
instances such a block needs whatever it hashes with. Past that, the signatures
were most of what was left, and without them the remainder fits in software at
every size, so one configuration is the cheapest across the whole sweep. A
contract-heavy block keeps the EVM's keccak and is still better off on the
precompile. `l2-latency` times it as one more arm.

The chain's own hashes (`MONAD_ZKVM_L2_HASH`, above) take the bloom's, the
block hash's and the salt's off Keccak-f as well: about fourteen permutations a
block, and one for the address and each topic of every log it emits. Measured
on corpora generated from the same seeds by a tree that names no hash, every
witness of which passes on the x86 and ZisK guests, with the remainder in
software: 4 to 25 % fewer steps than with the tries and signatures alone across
the sweep, 22 % on wholesale-cbdc and 33 % on worker-payouts, whose token
transfers fill blooms. Not enough to drop an instance: the plan is the same at
every size of the sweep, and worker-payouts' area falls to 0.98x the keccak
chain's. What keccak keeps is the EVM's, the anchor's and the code hashes'.

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
the tag; in front of it `decode_domain_body` and `execute_witness.cpp` name no
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
[Where the encryption's share goes](#where-the-encryptions-share-goes).

**`plaintext` is the suite the others are measured against, and never a
deployment.** [`l2_plaintext_suite.hpp`](guest/l2_plaintext_suite.hpp) takes a
leaf to be the transaction it carries and binds no secret; in every other rule
the guest is the L2 -- the chain id, the constant revision, unpriced gas, the
blinded commitments and the anchor. An ELF built with it and the same seven values
therefore runs the same chain as an encrypting one, and the difference between
the two runs is what the encryption costs, which a comparison with the mainnet
guest cannot isolate: its chain prices gas, publishes another output and
follows a fork schedule. With it the transactions the L1 sequences are
readable by anyone who reads the L1.

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

**The corpus is the L2's own chain.** In an L2 build its genesis is block 0
and holds what the design creates with the L2: the `NamespaceSpoke`, seeded at
the compiled `MONAD_ZKVM_L2_SPOKE` from its runtime code with its two
immutables written in where solc says the constructor writes them --
`CorpusScenarios.TheGenesisSpokeIsTheDeployedSpoke` holds that byte for byte
against a CREATE -- and, for the token presets, the wrapped tokens and their
holders. Nothing about a block number decides its rules: the guest fixes the
revision at compile time, `MONAD_ZKVM_L2_REVISION` as the type the block is
executed with rather than a value looked up per block, and it has to be
`MONAD_ETH_PARIS` -- the one revision with no withdrawals, no `requests_hash`
and no blob fields, which is exactly the shape this chain accepts. A build
without `MONAD_ZKVM_L2` generates a chain for the mainnet guest instead, whose
schedule picks the revision from the number, so that chain starts at the Paris
block, 15,537,394, with a timestamp below Shanghai's.

Three scenarios: EOA transfers with a contract that fills storage slots and
zeroes one; CREATE, logs, REVERT, SELFDESTRUCT and the legacy/2930/1559
transaction types; and the real `NamespaceSpoke`, vendored from
`eerkaijun/monad-namespaces` at `e6012d8cebf4` and deployed by CREATE, sending
namespace messages so the anchor has logs to harvest and a pending array to
clear.

```sh
# Configure an L2 host tree with the seven deployment values, then:
cmake --build build --target monad-zkvm-corpus-gen monad-zkvm-x86-test-runner
./build/zkvm/guest/monad-zkvm-corpus-gen --out /tmp/corpus \
    --sk <64 hex> --salt <64 hex>

# Each witness makes the guest republish what the manifest records: the
# number, both state commitments, the message anchor and the sequencing anchor.
./build/zkvm/guest/monad-zkvm-x86-test-runner \
    --input /tmp/corpus/spoke-00000002.witness --output /tmp/out.bin
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

Configuring the L2 tree with `MONAD_ZKVM_L2_CIPHER=plaintext` gives the same
chain with its transactions in the clear: the control the cost sections
measure the encryption against (see [Swapping the
encryption](#swapping-the-encryption)). Building with `MONAD_ZKVM_L2=OFF`
gives a corpus for the mainnet guest and its block-hash output, which is the
cheaper check of the generator and the trie.

### The benchmark corpus, and what it costs

The three scenarios above prove the generator works; they say nothing about
what a block costs, because twenty accounts and two blocks cannot. `--preset`
generates a corpus at scale instead: a genesis of `--accounts` holders, then
`--blocks` blocks that each aim to touch `--distinct` of them.

**A witness carries the ancestor headers its block reads.** The guest needs
the parent -- the pre-state root is checked against it -- and the hash of each
block `BLOCKHASH` reads, which it serves from the run of headers it is given
and refuses to serve from outside it. So in an L2 build the generator ships
the run back to the oldest block the block reads, and the parent alone when it
reads none (`--ancestors reached`); `--ancestors all` ships every header the
block hash buffer holds, up to 256, as a mainnet witness does. A header is 544
bytes and 0.345 M COST, so a block that reads no hash -- no block of these
presets does -- is 139 KB smaller and 88 M cheaper with the first. The first
`--warmup` blocks, 256 by default, run the same workload and are not emitted,
so every emitted block has the history a chain in its steady state has: a
block that reads a hash finds it, and an `--ancestors all` witness carries all
256 -- measured from genesis instead, a 200-block corpus understates a
wholesale block by 13 %.

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
# tokens: payment-versus-payment between banks in five currencies, and a
# payroll platform with an earn vault and three exits. See "The document's
# flows" below; --currencies 2 is the document's example, one pair.
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

Both presets at two hundred blocks after the warm-up, generated and checked
end to end. The figures are the L2 arm's; the control's witnesses -- the same
chain with the plaintext suite -- are smaller by what encryption adds to each
transaction, 102 bytes a transfer, and otherwise the same shape.

| | `wholesale` | `payouts` |
|---|---:|---:|
| accounts | 500 | 1,000,000 |
| blocks | 200 (257-456, after 256 of warm-up) | 200 |
| transactions per block | 21 | 500 |
| witness, median | 23 KB | 805 KB |
| witness, min-max | 21-24 KB | 793-815 KB |
| witness with `--ancestors all`, median | 162 KB | 944 KB |
| leaves touched, median | 42 | 553 |
| digests per leaf | 5.8 | 29.7 |
| gas, median | 0.50 M | 11.45 M |
| corpus size | 4.6 MB | 161 MB |

Every witness in both is accepted by the guest under `ziskemu` (below). The
chain holds: `post_root[n] == pre_root[n+1]` and
`block_hash[n] == parent_hash[n+1]` across all 200, the numbers are contiguous,
all 200 post-state roots are distinct -- the state moves every block rather than
being re-proved -- and every block carries a non-zero anchor, which the guest
republishes exactly.

**Wholesale is about five times cheaper per block than payouts, and eleven
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
deployed -- none has a constructor or an immutable -- and so is the spoke, as
in the native presets, so one configured guest takes every corpus. The
generator refuses a preset block in which any transaction reverted: a reverted
transaction still makes a valid block that round-trips every root, and only
its receipt says the block did less than the workload claims.
`WrappedToken.OnlyAdmittedHoldersMoveBalances` and
`PvpSettlement.BothLegsOrNeither` hold the two properties the document asks
for, eligibility and both legs or neither, on the checked-in bytecode.

| | `wholesale-cbdc` | `worker-payouts` |
|---|---|---|
| participants | 500 banks over five currencies: 50 intermediaries holding all five, 90 in each | 1,000,000 contractors, 4,096 of whom send; 1,000 businesses; the platform |
| a block | settles the last block's 10 payments and proposes 10; one bank redeems reserves to the L1, each currency in turn | admits 10 contractors; pays 400 in 10 batches of 40, each funded by a business; 25 deposits into the vault and 25 withdrawals; 50 exits, by card, by redemption and to the L1 |
| transactions | 21 | 130 |
| gas, median | 1.25 M | 9.60 M |
| witness, median (min-max) | 58 KB (54-62) | 865 KB (845-877) |
| witness with `--ancestors all`, median | 197 KB | 1,004 KB |
| account / storage leaves touched | 28 / 75 | 115 / 616 |
| digests per leaf | 6.8 | 25.4 |
| corpus size | 12 MB | 173 MB |

A contractor who only receives has a balance slot and no account: nothing it
does creates one. So the million are in one storage trie, and the account trie
holds only the few thousand who send -- the storage-trie variant the native
presets leave out. Both corpora chain like the native ones, all 200 post-state
roots of each are distinct, and every block carries a non-zero anchor.

**Five currencies, because the platforms are that size.** The document's
example is one payment between two currencies, not the size of the platform --
it names CLS's eighteen as the reach today's settlement has -- and the
multi-currency central bank projects settle four to seven: mBridge five, Agorá
seven. `--currencies` sets the count. Each currency is a wrapped token of its
own, held by its own banks and by every intermediary. A payment's pair is drawn
with weight 1/((a+1)(b+1)), so the first currency is on one side of 68 % of the
payments and three corridors carry 58 % of them, the way a hub currency does,
and each pair's payments run both ways. Five cost almost nothing more than two:
block for block, `--currencies 2` has a 2.0 KB smaller witness and costs 1.6 M
less -- 0.6 % of what a block costs above the floor with every ancestor, 0.9 %
without them. Three more token
contracts' accounts in each block, against storage tries a little smaller:
what a wholesale block costs is its payments, not how many currencies they are
in.

#### What the dispersion is worth

Measured on this generator, 1,000,000 accounts, four blocks per point after
the warm-up, L2 arm. `N` is the accounts in the trie, `K` the leaves a block
touched; the blob is the witness's node field, the part dispersion moves.

| distinct | leaves | digests | digests/leaf | witness | blob bytes/leaf | gas |
|---:|---:|---:|---:|---:|---:|---:|
| 50 | 58 | 2,405 | 41.5 | 113 KB | 1,693 | 1.2 M |
| 200 | 223 | 7,847 | 35.2 | 373 KB | 1,462 | 4.6 M |
| 500 | 552 | 16,550 | 30.0 | 810 KB | 1,265 | 11.4 M |
| 2,000 | 2,192 | 49,484 | 22.6 | 2,616 KB | 990 | 45.7 M |
| 5,000 | 5,447 | 97,164 | 17.8 | 5,526 KB | 811 | 114.3 M |

Three things fall out of the witness, and the first is why this corpus exists
at all.

**The access distribution does not matter; the distinct count does.** A leaf
touched twice in one block is free -- it is already in the witness -- so a
distribution can only reach the cost through the number of distinct leaves it
produces. Run with all three shapes at these five points, on a corpus for the
mainnet guest, uniform, Zipf and hot-set agree to within **0.2-1.6 %** in
witness bytes and 0.3-1.1 % in digests, with identical transaction counts,
against a 2.3x swing in digests-per-leaf across the points themselves. Frozen as
`WorkloadDispersion.TheShapeDoesNotChangeTheCostAtEqualDistinct`.

**The depth law is measurable.** `digests/leaf = 14.6 x log16(N/K) - 9.5`,
**R2 0.999**, the same on both arms because the cipher does not reach the blob:
fourteen digests for each level a path diverges from its neighbours, less about
nine for the top levels where every path is shared. The naive prediction was
fifteen per level with no offset. Mainnet cannot establish this -- the same fit
over 504 mainnet witnesses gives **R2 0.065**, because mainnet mixes storage
tries of wildly different sizes and confounds dispersion with the shape of the
state. A flat million-account trie separates them.

**The blob is sublinear in dispersion; the cost is not.**
`blob_bytes = 3996 x distinct^0.827`, **R2 0.9996**, on both arms -- doubling
the distinct accounts costs **1.77x the bytes, not 2x**, because the extra
paths land under prefixes the earlier ones already paid for. The witness adds
the transactions to it, and with `--ancestors all` a constant 139 KB of
ancestors. But bytes are not what these blocks spend most on: measured, the
variable cost goes as `distinct^0.95` once the 88 M of ancestor headers is set
aside, R2 0.99999 (`distinct^0.88` with them), because each distinct account
here is a transaction, and a transaction costs more than its share of the
witness.

#### What a block costs

Measured under `ziskemu` 1.3.1-alpha, which is what this tree pins, on every
workload block of the corpora above and the sweep -- 820 of them, which is what
the commands above produce -- on the L2 ELF and on the control, each run first
checked against the manifest. COST is ZisK's own cost model (`ziskemu -X
--stats`), taken through `zkvm-bench`'s `compare.run_zisk` so that a figure here
and one in a `compare` report come from one parser.

**Only the last row survives a change of anything.** The absolutes are a
snapshot of one commit on one emulator. The figures before these were taken on
ZisK 1.2.0-alpha at 71dcc0957, with the JUMPDEST precompile an L2 build now
leaves out, and with every ancestor header in the witness -- which the witness no
longer carries at all, it carries hashes. Five things moved between that table
and this one, so no pair of lines across them compares one thing.

The ratio does survive: both arms are the same commit, the same emulator and the
same seeds, so what one costs over the other is the encryption and nothing else.
It was 1.030x, 1.158x, 1.030x and 1.051x on the old base and is 1.036x, 1.164x,
1.035x and 1.053x here. That it barely moved across a change of emulator, of
base, of the JUMPDEST lever, of the ancestor format and of an access check on
every EVM call is the one thing these numbers say with confidence.

The share-of-a-mainnet-block row is gone rather than carried over: it is a ratio
against a mainnet arm that has not been re-taken on this emulator, and keeping a
number whose denominator moved would be worse than having none.

**The control is the same chain without the encryption.** Both ELFs are L2
builds of the same seven values; the control is configured with
`MONAD_ZKVM_L2_CIPHER=plaintext`, and so is the host tree that generates its
corpora from the same seeds. Block for block the two arms execute the same
transactions on the same state -- the pre- and post-state roots, the anchors
and the node blobs are identical across all 1,020 pairs -- so what one costs
over the other is the encryption and nothing else.

```sh
# Verify every witness against its manifest, then take steps and COST. Both
# ELFs publish the L2's eight values, so both are the l2 arm.
export ZKVM_BENCH=<zkvm-bench checkout>
zkvm/test/corpus/bench.py --arm l2 --elf <L2 ELF> --emu <ziskemu> \
    --corpus /tmp/l2/wholesale /tmp/l2/payouts /tmp/l2/sweep \
    /tmp/l2/wholesale-cbdc /tmp/l2/worker-payouts --out l2.csv
zkvm/test/corpus/bench.py --arm l2 --elf <control ELF> --emu <ziskemu> \
    --corpus /tmp/control/wholesale /tmp/control/payouts /tmp/control/sweep \
    /tmp/control/wholesale-cbdc /tmp/control/worker-payouts --out control.csv

# A zkvm-bench generation reads as it is: <n>.witness against <n>.blockhash.
zkvm/test/corpus/bench.py --arm plain --elf <mainnet ELF> --emu <ziskemu> \
    --corpus $ZKVM_BENCH/guests/monad/gen/r10zisk-rtp-25815000-25815199-cb7b6b1ae/witnesses \
    --out mainnet.csv

zkvm/test/corpus/bench-report.py --l2 l2.csv --plain control.csv --mainnet mainnet.csv
```

**The ELFs are built the way the benchmark builds its own**, and it matters: a
bare `cargo-zisk build --release` leaves five of the six levers the official
profile forces switched off, and measured 25 % more steps on a payouts block
and 9 % more COST. The official profile refuses `MONAD_ZKVM_L2`, so both L2
ELFs are dev builds carrying the same six levers -- `ZISK_DMA`, `KECCAKF_MEMO`,
`WIDE_MEMORY_SIZE`, `VARCODE_CACHE`, `NO_DIRTY_ACCOUNTS`,
`NO_MERGE_CONSTRAINTS` -- with the DMA-patched GCC 15.2.0 that `ZISK_DMA`
needs, and the mainnet ELF is the same dev build without `MONAD_ZKVM_L2`. That
one gives the official ELF's steps and COST exactly, on all 207 blocks
compared, which is what licenses reading the L2 ELFs as the official guest plus
the L2. All three were compiled with ZisK 1.2.0-alpha's own toolchain and run
under its `ziskemu`. Which release built an ELF matters even where no version
string shows it: installing a release relinks the `zisk` rustup toolchain, and
1.3.1's emits other code than 1.2's under the same `rustc` version.

| | `wholesale` | `payouts` | `wholesale-cbdc` | `worker-payouts` |
|---|---:|---:|---:|---:|
| steps, L2 | 0.45 M | 9.82 M | 1.13 M | 9.07 M |
| COST, L2 | 0.363 G | 2.053 G | 0.462 G | 1.867 G |
| of which fixed | 0.288 G | 0.288 G | 0.287 G | 0.287 G |
| COST, without encryption | 0.350 G | 1.764 G | 0.447 G | 1.774 G |
| what the encryption costs | 1.036x | 1.164x | 1.035x | 1.053x |

**A fixed 287,309,824 of it is the same on every block**: `Base`, ZisK's ROM
and lookup tables (137 x 2^21), which the cost model charges once per run
whatever the run proves. It is 64 % of a wholesale block, and 79 % of one
without its ancestors. A guest that proved several blocks in one run -- this
one proves one -- would pay it once, and on wholesale two blocks per run would
save more than making the block itself free.

**The ancestor headers are another 88 M on every block, and the guest does not
need most of them.** It accepts any contiguous run of headers that ends at the
parent and aborts on a `BLOCKHASH` outside it, so a witness need only carry
the run back to the oldest block the transactions actually read, and the
parent alone when they read none. None of these blocks reads one -- no
contract in the corpus calls `blockhash` -- and cut to the parent, ten blocks
of each preset, one in twenty, still publish the values their manifests
record, at 87-88 M less COST and 430 K fewer steps: 20 % of a wholesale block,
54 % of what it costs above the floor, and 4 % of a payouts block. So in an L2
build the generator ships only that run by default, `--ancestors reached`, and
`--ancestors all` keeps the shape this section was measured on. The laws below
carry over: at their 661 COST a byte, the 139 KB the ancestors take are 92 M,
against the 88 M they measure.

**The rest follows the transactions first.** Over the 420 blocks of the
transfer presets on the L2 arm,

    COST - base = 2.43 M x txs + 661 x witness_bytes + 4.2 M        R2 0.999999

and the control gives 1.93 M per transaction and 651 per byte. The per-byte
term is the trie's and is the same on both arms; the encryption is 0.50 M more
per transaction, +26 %. A payouts block spends 1.21 G on its 500 transactions
and 0.62 G on its 944 KB of witness.

**So prover cost is proportional to gas only above the floor.** On the payouts
sweep `COST - base = 138 x gas`, R2 0.9993 -- re-taken on 1.3.1-alpha at this
commit, against 140 and R2 0.9988 before, which is the law holding across every
change listed above. For one transaction mix, the part of the cost that depends
on the block is linear in gas even though the witness is not. What makes COST
per gas fall from 413 at 50 transfers to 139 at 5,000 is the fixed part, and the slope belongs to the mix -- outside the floor,
wholesale spends 328 per gas, over half of it on its ancestors, and payouts
161.

**The document's flows cost what their gas says, not what their transaction
count says.** The per-transaction law above was fitted where a transaction is a
transfer. On the token presets a transaction is a contract call -- for payroll,
forty transfers -- and the law misses the part of the cost above the floor by
30 % on `wholesale-cbdc` and 42 % on `worker-payouts`. Gas and witness bytes
carry every mix: over all 1,020 workload blocks of the L2 arm,

    COST - base = 104.9 x gas + 687 x witness_bytes - 1.7 M        R2 0.999994

within 1.0 % on every block of the five corpora, and 2.7 % at worst, on the
sweep's 50-transfer blocks. Outside the floor the token presets spend 212 and
177 per gas, inside the native range. The law describes this guest and not the
mixes: on the control, the same two terms miss by up to 9 %.

Settling payment versus payment costs a wholesale block 63 % more above the
floor, 0.265 G against 0.162 G: about forty banks either way, but reached
through tokens' storage and a settlement contract rather than as account
leaves. Payroll goes the other way. `worker-payouts` touches as many
contractors as `payouts` touches holders and costs 7 % less, 1.986 G against
2.130 G, because batching pays four hundred of them in ten transactions: 130
signatures to recover instead of 500 take secp256k1 from 0.19 G to 0.05 G,
more than the mapping slots and the million-slot storage trie add in Keccak,
0.59 G to 0.64 G.

**Mainnet, on the mainnet guest built the same way.** The 200 canonical blocks
25,815,000-25,815,199 (`zkvm-bench`'s `r10zisk-rtp` witnesses), every block
hash reproduced: median **8.13 G** COST (p10 4.94, p90 12.20), 47.9 M steps,
6.61 MB of witness, 1,195 COST per witness byte above the floor. A payouts
block spends 1,953 per byte, 1.6 times as much: a transaction-dense L2 block
is not a small mainnet block, and the mainnet law below does not carry over to
it -- the transaction count is what it misses.

#### Where the encryption's share goes

Paired block for block against the control, which executes the same
transactions on the same state:

| | steps | COST | COST - base |
|---|---:|---:|---:|
| `wholesale` | 1.12x | 1.03x | 1.08x |
| `payouts` | 1.27x | 1.16x | 1.19x |
| sweep, 50 to 5,000 transfers | 1.17-1.30x | 1.05-1.22x | 1.11-1.22x |
| `wholesale-cbdc` | 1.08x | 1.03x | 1.06x |
| `worker-payouts` | 1.08x | 1.05x | 1.06x |

The encryption is paid per transaction -- a leaf to decrypt, its ECDH and its
sponges: 0.58-0.60 M COST and 102 bytes of witness a transfer, 0.75-0.76 M and
140-142 bytes a token call, whose plaintext is longer. So it weighs less on
the token presets, which reach the same participants through fewer, heavier
transactions.

Of the extra COST on a payouts block, 47 % is main-machine steps, 32 %
precompiles (Poseidon2 8 %, secp256k1 12 %, Keccak 7 %) and 14 % memory. By
function, on one 500-transaction block (`hotspots.py`, 9.58 M steps against
7.56 M):

- the software sponge around the Poseidon2 precompile, **0.96 M steps**:
  `L2Sponge::absorb` 0.51 M, the constructor 0.19 M, `squeeze` 0.16 M, byte
  packing 0.09 M;
- the ECDH, mostly the GLV scalar multiplication, 0.66 M;
- leaf decryption, 0.33 M;
- Keccak and allocation, 0.06 M. The L2 block decode costs the same on both
  arms, so nothing else separates them.

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
from, which `decode_domain_body` keeps for the block, rather than re-encoded field
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
time, and this ELF spends 1,195 per byte on mainnet above the floor, two-fifths of it. On
mainnet, witness bytes are the cost to within about 8 %; on the L2 corpus they
are the smaller of two terms.

#### What still has to be measured elsewhere

**Proving time.** Everything above executes under the emulator; COST is ZisK's
model of prover work, not a wall-clock. `zkvm-bench` proves on its GPU boxes,
and two things stand between these blocks and that path. Its root gate
(`profiling/series/root-ref.sh`) compares the first 32 bytes of the output
against a block hash or a state root, and on the L2 arm those bytes are the
chain id and the block number, so this output needs a reference kind of its
own. And
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
| the run stops short of a block whose hash `BLOCKHASH` reads | the read itself, `WitnessBlockHashBuffer::get` |

They drive the real runner as a subprocess, because a bad witness is signalled
by aborting -- the thing under test is a process exit -- and they match on the
assertion text, not just a non-zero status, so a test cannot pass for the wrong
reason.

Two details that decide whether these test anything. The run starts from a
four-block chain and drops an ancestor from the MIDDLE: dropping the oldest
would just make a shorter, valid run and prove nothing -- for a block that
reads no hash. One that does is the other case, and the one that makes
`--ancestors reached` sound: a block reading the hash three back, witnessed
with exactly that run, is accepted, and the same run without its oldest header
is refused by the read itself. And the first test
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

That step has been taken on the ELFs [the cost section](#what-a-block-costs)
measures, under `ziskemu` 1.2.0-alpha: the L2 ELF and the control, dev builds
carrying the same six levers and the deployment values the tests use.
Every witness the scenarios and the five corpora generate passes, on both arms:
the guest republishes exactly what the manifest recorded -- the block number,
both state commitments, the message anchor and the sequencing anchor, each
derived twice, once by the generator and once by the guest --
including the 1,021 blocks of each arm whose anchor is non-zero. The figures in
this table predate the output change; what they measured is unaffected by it.

| | L2 | without encryption |
|---|---:|---:|
| scenarios (transfers, evm, spoke) | 6 / 6 | 6 / 6 |
| `wholesale`, 500 accounts | 200 / 200 | 200 / 200 |
| `payouts`, 1,000,000 accounts | 200 / 200 | 200 / 200 |
| the dispersion sweep, 50 to 5,000 distinct | 20 / 20 | 20 / 20 |
| `wholesale-cbdc`, 500 banks in five currencies | 200 / 200 | 200 / 200 |
| `wholesale-cbdc --currencies 2` | 200 / 200 | 200 / 200 |
| `worker-payouts`, 1,000,000 contractors | 200 / 200 | 200 / 200 |

It has been taken again on this tree, with the same levers and values built
by 1.3.1-alpha's toolchain and run under its `ziskemu`: every one of those
witnesses passes on the L2 ELF and on the control, and the mainnet ELF
reproduces the 200 block hashes below. The corpora are this tree's own: its
generator reproduces every one of them byte for byte with `--ancestors all`,
and by default emits the same witnesses cut to the parent, every one of which
passes on both arms too.

What the encryption adds to each block is in
[Where the encryption's share goes](#where-the-encryptions-share-goes).

The mainnet ELF reproduces the canonical mainnet block hash of all 200
blocks 25,815,000-25,815,199 from `zkvm-bench`'s `r10zisk-rtp` witnesses, 0.2 M
to 95.1 M steps. Witnesses from before the blob grammar moved `DIGEST` to `0xa0`
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

# The Monad guest: what it does, and what is left

This branch takes the zkVM guest from `EvmTraits` to `MonadTraits`, and adds a
domain arm on top of it. The domain arm has been run: six witnesses, natively
and under ZisK, each publishing what an independent host run computed. The L1
arm builds and links and has not been run. Everything below separates what was
established by building, reading or running from what was not.

The companion documents are [DECISIONS.md](DECISIONS.md), for choices the
specification does not make, and [CONFORMANCE.md](CONFORMANCE.md), for
behaviour the client and the contracts already determine. This one is neither:
it is a list of work.

---

## What the branch does

**The trait family.** `EthereumMainnet` becomes `MonadMainnet`, the revision
comes from `get_monad_revision`, and both dispatches became
`SWITCH_MONAD_TRAITS`. All twelve Monad revisions are instantiated and the
block's timestamp picks one. `execute_block_zkvm` is `requires(is_monad_trait_v)`.

Everything that follows from the family follows with it: Monad pricing, the
reserve balance, cold-access costs, code-size limits. The client refuses the
other pairing at compile time -- its gasless path carries
`static_assert(!gasless || is_monad_trait_v<traits>)` -- so this was never
optional.

**The ancestor sets.** `ChainContext<MonadTraits>` carries five members, and
two are the sender and authority sets of the *parent* and *grandparent* blocks.
`can_sender_dip_into_reserve` reads them to refuse a dip. A proof of one block
cannot derive them.

The witness already had the two fields and the guest ignored them. It now
decodes them and publishes their commitment as a second public value, sorted
before hashing because a `segmented_set` iterates in insertion order and the
verifier builds its set from its own chain. Passing empty sets instead would
let a sender dip where the chain refuses, and the proof would attest a state
the node would not reach.

This is load-bearing under speculative execution, which is what the rule exists
for: at the time the node executes block N, N-1 and N-2 are proposals. The
commitment pins which branch the proof was built on, so a proof of a block that
was later reorged away is rejected rather than believed.

**The staking contract**, with BLAKE3, libsecp256k1 and blst behind it. See the
commit for what each is for and what the bare-metal target forced.

---

## What is not established

**The guest has never run.** No witness, no steps, no COST. "It builds" is the
whole of the claim. Every number below that is not a file size is unmeasured.

**No Monad witness exists.** The corpus builds Ethereum witnesses. The guest now
reads two fields the corpus does not populate, so the first thing any of this
needs is a witness generator that fills them.

**Which header the witness carries.** A Monad consensus header separates
`execution_inputs` from `delayed_execution_results`. The guest must be handed
the inputs and must compare against the parent's *result*. The code does check
the pre-state root against the parent header, but whether the witness supplies
the right one of the two was not checked.

---

## What is left

### 1. Run the L1 arm

The domain arm runs. The L1 arm does not, for want of a corpus: the generator
builds Monad blocks only under `MONAD_ZKVM_L2`, and it leaves both ancestor
sender sets empty -- which is right for a domain, whose blocks are not pending
blocks of the chain that carries them, and wrong for an L1 block, where the
node fills them from its block cache. Until an L1 corpus exists, the reserve
rule that reads those sets is unexercised on the arm that needs it.

### 2. `read_valset.cpp`

Dropped, and not for want of a library: it reads the validator set straight
from the trie through `trie_db`, which is a node's operation. A guest holds a
witness. Making it available means writing it against the guest's `Db`, not
linking this one.

### 3. System transactions

`execute_system_transaction.cpp` is dropped from the guest, but
`monad/dispatch_transaction.cpp` dispatches them in the block path. A block
carrying one is executed differently by the node and by this guest. Nothing
currently refuses such a block, which makes this the sharpest open item on the
list: the divergence is silent.

### 4. MIP-8, and what targeting MONAD_TEN means

`db/storage_page.cpp` and `db/page_commit_builder.cpp` are dropped. MONAD_TEN
makes MIP-8 page-encoded storage active, which changes the storage trie's
encoding. Instantiating the twelve revisions does not make MONAD_TEN faithful;
it makes it compile. Either those sources come in, or the guest should refuse
the revisions that need them.

### 5. Monad's own block validation

The guest validates with `static_validate_block_with_parent`, the
Ethereum-shaped check. `static_validate_monad_body` exists and is not called,
and `MonadConsensusBlockHeader` is not touched at all. What the guest does not
check, it assumes.

### 6. The cost of a BLS pairing

`blst_core_verify_pk_in_g1` is a pairing. It is the most expensive thing a
proof can be asked to do, and it is why the tree shadowed the BLS precompiles
rather than running them. A block that registers a validator now has a cost
nobody has measured. If it is prohibitive, the answer is probably a precompile,
not a faster pairing.

### 7. BLAKE3 through ZisK's precompile

ZisK has BLAKE2b, BLAKE2s and BLAKE3f precompiles, in 1.2 as in 1.3.1 -- what
1.3.1 adds is a carry-bit soundness fix, not the precompiles themselves. The
guest currently compiles BLAKE3's portable C.

Whether that rides the precompile is unverified and should not be assumed:
`libziskclib.a` exposes `_zisk_keccakf` as a C entry point and nothing for
BLAKE, so the trigger is likely pattern recognition in the transpiler, against
the Rust crate rather than this C. Counting the steps on a block that derives a
validator address settles it.

### 8. The ELF, and the twelve revisions

| | bytes |
|---|---|
| Ethereum guest (`plain`) | 6,211,576 |
| Monad guest | 24,220,744 |

Of which the staking path is 979,168 -- 4.2 %. The rest is the twelve
revisions. Instantiating only the revisions actually proved is the obvious
lever, and for a domain, which runs one, it is a large one.

### 9. Orphaned proofs

Running on proposals, as intended, means a proof can be built on a branch that
loses. The ancestor commitment makes that detectable rather than silent, but
nothing decides what happens to the proof: who pays for the work, and whether
the prover retries on the canonical chain. That is a deployment question this
tree does not answer.

---

## For the L2

Most of the above does not reach a domain, and that is worth stating plainly so
it is not re-derived later:

- the reserve balance **applies**, and the client applies it too: its domain
  path is instantiated with `EXPLICIT_MONAD_TRAITS` and its reserve context is
  gated on the trait family, not on `gasless`;
- but a domain has **no ancestors**. The node builds its domain ChainContext
  with both sets empty, so the guest does the same, and nothing about them is
  published;
- the staking prelude returns before constructing anything, because the staking
  contract is not deployed on a domain, and the precompile is refused outright
  rather than left unreachable by argument.

Two constraints the domain arm discovered, which bind any guest that tracks the
reserve:

- **`MONAD_ZKVM_L2_REVISION` must be MONAD_FOUR or later.** Below it
  `ReserveBalance::init_from_tx` turns its own tracking off, so the client
  would apply reserve rules the guest would not. Pinning a domain to
  MONAD_ZERO..THREE to keep that machinery inert is therefore not an option,
  whatever a Cancun base would have saved.
- **`MONAD_ZKVM_NO_DIRTY_ACCOUNTS` cannot be used.** `State::push` asserts that
  tracking is off when that lever drops the per-frame dirty account sets, and
  `dipped_into_reserve` has nothing to walk without them. An ELF carrying both
  halts at its first call frame; `cmake/l2.cmake` refuses the combination. The
  lever is worth 1.9 % of emulator steps, measured on the arm that can take
  both values.

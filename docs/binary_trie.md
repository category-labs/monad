# Binary trie state commitment

This document describes the binary-trie state commitment selected by
`state_machine_kind::lbt_binary`. The code lives in `category/mpt/lbt/` (the
commitment and its engine integration) and in
`category/execution/monad/db/lbt_machine.*` (the State table layout).

The commitment replaces the State table's Merkle-Patricia root with the root
of a binary trie over key bits, in the style of EIP-7864. The storage engine is
unchanged: it still stores 16-way nodes, and each node computes the slice of the
binary trie that its key bits span. Only the hashing changes.

## What is committed

The State table is a set of 256-bit keys, each with a value. Storage is not a
separate set: each account's storage trie folds into that account's leaf (see
State layout). The commitment is the root of the binary trie over the key bits,
most significant bit first, with two rules that keep it compact:

- A leaf rises to its shortest unique prefix. A subtree that holds a single
  key is that key's leaf, however deep the key's bits go.
- An internal node with a single child is hashed against a zero sibling. When
  two subtrees share bits below their parent, each shared bit costs one merge
  with a zero on the side the bit does not take.

The empty trie's root is 32 zero bytes. Unlike EIP-7864, there are no stem
nodes grouping 256 values: every account and every storage page is its own
leaf, keyed by its existing keccak hash.

`TrieDb::state_root()` does not return that zero root for an empty State
table. As for every table, when the table holds no data it returns
`NULL_ROOT`, the keccak hash of the RLP empty string.

## Hashes

All hashing is BLAKE3. Each binary node is one BLAKE3 compression of a single
64-byte block, and its 32-byte commitment is the resulting chaining value: 8
words, stored little-endian.

- **Internal node.** The block is `left ‖ right`, compressed from the
  standard BLAKE3 IV with block length 64, counter 0 and flags
  `CHUNK_START | CHUNK_END`. A missing child is 32 zero bytes.
- **Leaf.** The block is `key ‖ value`, compressed from the leaf IV with block
  length 64 and flags `CHUNK_START | CHUNK_END`.
  - The key is the leaf's full key, packed two nibbles per byte (high nibble
    first) and zero-padded to 32 bytes.
  - The counter is the key's nibble count, which is 64 for every state leaf.
  - The value is a 32-byte digest. Accounts and pages each have their own
    (see State layout).
- **Value hash.** `value_hash` is BLAKE3's keyed mode
  (`blake3_hasher_init_keyed`, 32-byte output) under the value key.
- **Domains.** The leaf IV and the value key each come from a single
  compression from the standard IV:
  - The block is a 32-byte domain string followed by 32 zero bytes.
  - The block length is 64, the counter is 0, and the only flag is
    `DERIVE_KEY_MATERIAL`.
  - The domain strings are `monad_lbt_leaf_domain___________` and
    `monad_lbt_value_domain__________`.
  - The leaf IV is the resulting chaining value, and the value key is the
    same 8 words as 32 little-endian bytes.

  This is not BLAKE3's public `derive_key` function, which would give
  different bytes.
- **Node type.** A parent must know which of its children are leaves: a lone
  leaf rises unchanged, while a lone internal node is merged with a zero
  sibling. The type is not part of any hash. The engine records it beside
  each child's hash: every node's `child_value_mask` has a bit per child,
  set when the child has a value, which in the State table means a leaf.
  `lbt::Commitment` pairs a hash with that type.

## How a 16-way node commits its slice

A branch node's children sit at 4-bit indices. `lbt::branch_commit` reduces
them through the 4 binary levels those bits span, deepest bit first. At each
level, two children that differ only in that bit are merged. A lone leaf rises
unchanged. A lone internal node keeps the side its bit selects and is merged
with a zero sibling on the other side.

A branch node with a non-empty path is reached through path bits that no other
key shares. `lbt::commit_path` adds one merge with a zero sibling per path bit,
starting from the deepest bit of the last nibble. A leaf at the end of a
compressed path needs no such merges, because it rises.

The result does not depend on how the engine groups bits into nodes. The test
`LbtBranchCommit.grouping_does_not_change_the_commitment` checks that an 8-bit
branch equals a 4-bit branch over 4-bit branches.

## Full-key binding

A leaf commits its full 64-nibble key, not just the suffix below its parent.
Because of this, a leaf that the engine lifts over a coalesced path keeps its
commitment, and the commitment cannot depend on where the engine happened to
split the key.

A node stores only its path below its parent, so the machine records the key
it walks:

- Both LBT machines write every nibble they descend into an `lbt::KeyPath`.
  This covers `down(unsigned char)` and `down(NibblesView)`, since the engine
  descends whole node paths through the latter.
- `get_compute()` binds the recorded key, measured from the start of the
  current account or storage key, to the compute just before the engine
  hashes.
- For a leaf with path `p` hashed while the recorded prefix is `prefix`, the
  key is `prefix[0, 64 − |p|) ‖ p`. This holds at any depth at or below the
  leaf's start, because state keys are exactly 64 nibbles. A release assert
  checks that the recorded prefix agrees with the path where they overlap.

## State layout

- **Accounts.** An account is a leaf keyed by `keccak256(address)`. Its value
  is `value_hash(db ‖ storage root)`, where `db` is the account's DB encoding
  (`encode_account_db`: the RLP of address, incarnation, nonce, balance and
  code hash, the code hash omitted for empty code). An account without storage
  hashes `db` alone. The account node keeps its storage root in its own data.

  This leaf is incomplete. It commits the address and the incarnation, which
  MPT does not, so two pools holding the same state can disagree when they
  store different account bytes; the binary-checkpoint loader writes a zero
  address, for example. The account/storage split replaces this leaf.
- **Storage.** Storage is page-encoded (MIP-8). Each page is a leaf keyed by
  `keccak256(page key)`, and its value is `page_commit(page)`. An account's
  storage root is the binary-trie root over its pages.
- **Roots.** The State table's root node keeps the table's commitment in its
  own data, and `TrieDb::state_root()` reads it from there. Keys exclude the Db
  prefix, so the same state gives the same root under a proposal prefix and
  under the finalized prefix.
- **Other tables.** Only the State table uses this commitment. Receipts,
  transactions, code and the other tables keep their MPT commitments.

The kind's persisted value is 2. A pool stamped with a kind this build does
not know aborts on open, through the registry on a read-write open and through
`is_page_encoded_kind()` on a read-only one.

`is_page_encoded_kind()` reports `lbt_binary` as page-encoded, so `TrieDb`,
`TrieRODb`, the snapshot loader and the snapshot dumper read and write pages
for it. `monad-mpt --state-machine lbt_binary` stamps the kind on a pool, and
`register_lbt_state_machines()` lets a pool stamped with it be reopened.

## Node format

`child_value_mask` sits in the node header next to `mask`. With alignment the
header grows from 16 to 24 bytes for every node, MPT nodes included; the
spare bytes are explicit and zeroed, because the header is written to disk as
is. The pool magic is `MONAD009`, so this build refuses pools written by
earlier ones instead of misreading them. There is no upgrade path yet.

## Pinned roots

Every `PIN_*` constant in the tests was produced by this implementation. The
model in `category/mpt/lbt/tools/lbt_model.py`, written from this document with
its own BLAKE3 compression, reproduces the primitive, branch and path pins and
the oracle roots whose inputs it can replay. The other pins are tied in their
tests to the reference trie or to state roots rebuilt from the raw leaves. The
inputs of three pins (two branch commitments and the random-batches oracle
root) are drawn through `std::ranges::shuffle`, so a standard library other
than libstdc++ changes those inputs, not the commitment.

The commitment differs from the prototype it was benchmarked as only in where
the node type lives: the prototype stole the top bit of each hash for it.

End to end, loading the mainnet snapshot of block 90047827 into an
`lbt_binary` pool gives state root
`0xd82327e452791dc3e53ba68b114ebf2d88aad6368ef3bfc29d59cb75f01cb367`.

## Open questions

- **Empty-state root.** The binary trie's empty root is zero, but
  `TrieDb::state_root()` reports `NULL_ROOT` for an empty State table.
  Integration has to pick the value the block header carries.
- **Node header.** `child_value_mask` costs 8 bytes in every node header,
  including MPT nodes. The planned node-format revision can pack it, and needs
  to define the upgrade path from `MONAD008` pools.
- **Hash function.** BLAKE3 was chosen for speed, and the MIP-8 page
  commitment already uses it. A proof system may favour a different hash. The
  trie's hashing is confined to `commit.cpp`, and `page_commit` has its own.
- **Key recording.** Recording the key costs time on the update path, because
  every descent writes into `KeyPath`.
- **Concurrent updates.** The machines share process-wide computes, as
  `MachineBase` does, and an LBT compute also holds a view of one machine's
  key. Two pools updated at once from one process would race.

## Remaining work

- **Execution and RPC integration.** Choose the revision that selects
  `lbt_binary` and put its root in the block header. Register the kind in
  `cmd/monad`, the runloop (`runloop_interface_monad.cpp`) and the statesync
  client; none registers it yet, so each aborts on an `lbt_binary` pool. Serve
  proofs through `eth_getProof`, and carry the kind through statesync.
- **Account/storage split.** Commit accounts and storage as separate tries,
  and define the account leaf that replaces the provisional one above.
- **Migration.** Move an existing MPT database to `lbt_binary`.
- **Witness generation.** Produce and verify per-block witnesses over this
  commitment.

# Monad DB: Two‑Layer Architecture & Client Patterns

This document collects the key takeaways from our recent deep‑dive into the `monad::Db` façade, its underlying MPT engine, its concrete implementations, and how the various sub‑systems (execution, consensus, RPC, StateSync) drive and read it.

---

## 1. Two‑Layer DB Architecture

Monad’s state persistence is implemented in two layers:

| Layer                            | Namespace       | Responsibilities                                                                              |
| :--------------------------------| :---------------| :---------------------------------------------------------------------------------------------|
| **Raw MPT engine**               | `monad::mpt::Db`| Low‑level Merkle‑Patricia‑Trie store (async I/O, lock‑free ring buffer for historic versions). |
| **High‑level blockchain façade**  | `monad::Db`     | Blockchain execution API: read/write account/storage/code, commit/finalize blocks, roots.     |

The high‑level façade (in `libs/execution/src/monad/db`) delegates all the heavy lifting to the raw MPT engine (`libs/db/src/monad/mpt`), avoiding duplication and focusing on blockchain semantics.

---

## 2. Raw MPT Interface: `monad::mpt::Db`

Located in **`libs/db/src/monad/mpt/db.hpp`**, the `mpt::Db` abstraction provides:

- **RODb**: read‑only trie (for RPC & StateSync clients).  
- **Db**: read‑write trie (for execution & consensus), with on‑disk or in‑memory backends and async I/O.

Core operations include:

- `get(prefix, version)`, `get_data(prefix, version)` → fetch leaf or root‑offset  
- `upsert(UpdateList, version)` → apply state/code/transaction updates, write new root  
- `copy_trie(src_ver, src_pref, dst_ver, dst_pref)` → snapshot‑copy proposal→finalized  
- `update_finalized_block(version)`, `update_verified_block(version)`, `update_voted_metadata(version, round)` → metadata ring  
- `get_latest_*` → read current ring watermarks  
- versioned traversals (`traverse`) for RPC/state‑sync dumps

---

## 3. High‑Level Façade: `monad::Db`

In **`libs/execution/src/monad/db/db.hpp`**, `monad::Db` defines the execution engine’s view of state:

```cpp
struct Db {
  // ── Read queries ──────────────────────────────────────
  virtual std::optional<Account>         read_account(Address) = 0;
  virtual bytes32_t                      read_storage(Address, Incarnation, bytes32_t const&) = 0;
  virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const&) = 0;

  // ── Root queries ──────────────────────────────────────
  virtual BlockHeader    read_eth_header()    = 0;
  virtual bytes32_t      state_root()        = 0;
  virtual bytes32_t      receipts_root()     = 0;
  virtual bytes32_t      transactions_root() = 0;
  virtual std::optional<bytes32_t> withdrawals_root() = 0;

  // ── Wrap consensus callbacks ──────────────────────────
  virtual void set_block_and_round(uint64_t, std::optional<uint64_t> = std::nullopt) = 0;
  virtual void finalize(uint64_t, uint64_t)                                       = 0;
  virtual void update_verified_block(uint64_t)                                     = 0;
  virtual void update_voted_metadata(uint64_t, uint64_t)                           = 0;

  // ── Apply an executed block ─────────────────────────
  virtual void commit(StateDeltas const&, Code const&, MonadConsensusBlockHeader const&,
                      std::vector<Receipt> const& = {}, std::vector<std::vector<CallFrame>> const& = {},
                      std::vector<Address> const& = {}, std::vector<Transaction> const& = {},
                      std::vector<BlockHeader> const& = {},
                      std::optional<std::vector<Withdrawal>> const& = std::nullopt) = 0;
};
```

### Implementations

| Class       | File(s)                           | Role                                        |
| :---------- | :-------------------------------- | :-------------------------------------------|
| **TrieDb**  | `trie_db.hpp/cpp`                 | RW trie delegator → `mpt::Db` (execution)     |
| **TrieRODb**| `trie_rodb.hpp/cpp`               | RO trie delegator → `mpt::Db` (RPC, StateSync) |
| **DbCache** | `db_cache.hpp/cpp`                | In‑process LRU cache wrapper (RPC + local)   |
| **StateSync server context** | `statesync_server_context.hpp/cpp` | `monad::Db` wrapper that instruments commit/finalize to capture deletions for StateSync server |

### How TrieDb encodes EVM tables into the raw MPT

`TrieDb` uses a fixed one‑byte “nibble” per EVM table, concatenated onto the proposal/finalized prefix, so that all state, storage, code, receipts, transactions, headers, ommers, etc., live in disjoint subtries.  The nibble constants and prefix definitions live in `util.hpp`:

```cpp
// libs/execution/src/monad/db/util.hpp:L86-L97
inline constexpr unsigned char STATE_NIBBLE       = 0;
inline constexpr unsigned char CODE_NIBBLE        = 1;
inline constexpr unsigned char RECEIPT_NIBBLE     = 2;
inline constexpr unsigned char TRANSACTION_NIBBLE = 3;
inline constexpr unsigned char BLOCKHEADER_NIBBLE = 4;
inline constexpr unsigned char WITHDRAWAL_NIBBLE  = 5;
inline constexpr unsigned char OMMER_NIBBLE       = 6;
inline constexpr unsigned char TX_HASH_NIBBLE     = 7;
inline constexpr unsigned char BLOCK_HASH_NIBBLE  = 8;
inline constexpr unsigned char CALL_FRAME_NIBBLE  = 9;
inline constexpr unsigned char BFT_BLOCK_NIBBLE   = 10;
```【F:libs/execution/src/monad/db/util.hpp†L86-L97】

```cpp
// libs/execution/src/monad/db/util.hpp:L114-L117
inline constexpr unsigned char PROPOSAL_NIBBLE = 0;
inline constexpr unsigned char FINALIZED_NIBBLE = 1;
inline mpt::Nibbles const proposal_nibbles  = mpt::concat(PROPOSAL_NIBBLE);
inline mpt::Nibbles const finalized_nibbles = mpt::concat(FINALIZED_NIBBLE);
```【F:libs/execution/src/monad/db/util.hpp†L114-L117】

On `commit()`, `TrieDb` switches its **prefix** to `proposal_prefix(round)` (using the round number) and then writes every EVM table under that proposal prefix plus its table nibble and key bytes.  Upon `finalize()`, the entire proposal subtrie is copied into the immutable `finalized_nibbles` subtrie so that snapshot remains frozen.

---

## 4. Clients & Access Patterns

| Client                | Calls                             | Mutates? | Reads Prefix          | Writes Prefix           |
| :---------------------| :---------------------------------| :------- | :---------------------| :-----------------------|
| Execution RunLoop     | commit, finalize, update_*        | ✓        | proposal/finalized     | proposal → finalized    |
| Consensus WAL Replay  | (→ runloop)                       | ✓        | proposal              | proposal                |
| StateSync Server      | RO queries + instrumentation      | ⚠ only instrumentation | finalized_nibbles      | N/A                     |
| StateSync Client      | commit/finalize (ingest data), verify roots | ✓        | client‐side RO prefix | ingested upserts/deletions |
| RPC Server            | read_* + traverse queries         | ✗        | any (proposal/finalized) | N/A                    |
| CLI (`monad_cli`)     | read_* + traverse + metadata      | ✗        | any                   | N/A                     |

---

## 5. `monad::Db` Method Summaries

Below is a concise English summary of each method’s arguments, effects, and pre/post conditions:

| Method & Signature                                             | Arguments                          | What it does & Conditions                                                                                  |
| -------------------------------------------------------------- | --------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| `read_account(Address addr)`                                   | `addr`: account key             | **Reads** the account at `addr` in the current (block,round). Returns `None` if no account.                 |
| `read_storage(Address a, Incarnation i, bytes32_t key)`        | `a`, storage slot `key`, `i`      | **Reads** 32‑byte storage value at that slot/version. Defaults to zero if unset.                          |
| `read_code(bytes32_t hash)`                                    | `hash`: code key                 | **Reads** code analysis pointer for that account/class if present.                                         |
| `read_eth_header()`                                            | (none)                            | **Reads** the RLP‑decoded block header at current version.                                                  |
| `state_root(), receipts_root(), transactions_root(), withdrawals_root()` | (none)                   | **Reads** the MPT root for accounts/receipts/txs/withdrawals under current prefix/version.                  |
| `set_block_and_round(uint64_t block, optional<uint64_t> rnd)`  | `block`: version; `rnd`: round   | **Switches** read prefix+version. If `rnd` given → proposal_prefix(rnd); else → finalized prefix.         |
| `commit(StateDeltas&, Code&, Header&, …)`                       | EVM post‐state and block inputs   | **Writes** a new proposal snapshot for block `Header.number`. **Precondition:** execution succeeded.     |
| `finalize(uint64_t block, uint64_t rnd)`                       | `block`, `rnd`                   | **Freezes** the proposal snapshot → finalized prefix. Updates `latest_finalized_block_id`.                  |
| `update_verified_block(uint64_t block)`                        | `block`: verified block           | **Marks** the highest delayed‐execution block applied.                                                      |
| `update_voted_metadata(uint64_t block, uint64_t rnd)`          | `block`: voted block, `rnd`: voted round | **Stores** only the *highest‐round* QC. On next vote, if `rnd` > existing, overwrite `(block,rnd)`.          |

---
## 6. Clarifications & Common Points of Confusion

**Q: Why does the StateSync server context cache deletions?**  
A: The MPT traversal used to stream upserts only visits live (non‐deleted) leaves. To faithfully reproduce on the client that a slot or account was removed, the server must record which keys were zeroed out or accounts deleted during each block’s commit/finalize.  `statesync_server_context` instruments `commit()` and `finalize()` to build a bounded ring buffer of deletions and then iterates over them to emit explicit delete messages alongside the upsert stream.

**Q: Why not record all changed keys/accounts instead of just deletions?**  
A: Recording every changed key duplicates the work of the MPT traversal, which already streams all existing leaves as upserts. Only removed keys would otherwise vanish silently, so only deletions must be captured explicitly to guide the client’s trie GC.

**Q: How do finalize vs update_verified_block vs update_voted_metadata differ?**  
- `finalize(block,round)`: copies the proposal prefix snapshot into the immutable finalized prefix and bumps the finalized‐block watermark (no further writes ever touch that block).  
- `update_verified_block(block)`: marks which deferred‐execution block headers were validated/applied—this watermark may lag finalized blocks if there are no delayed headers.  
- `update_voted_metadata(block,round)`: logs the highest‐round QC vote the node has cast for a given block (overwriting any previous lower‐round vote), for crash recovery and RPC inspection.

**Q: Why record a vote (update_voted_metadata) on a block before it’s finalized?**  
A: Voting (producing a QC) is part of the PROPOSE phase, not finalization.  The node records its latest QC immediately after proposing, so that on restart it can recover its locked certificate and preserve consensus safety.

**Q: Does update_voted_metadata keep history of all votes?**  
A: No. The implementation only stores a single `(block,round)` pair—always the highest‐round seen so far. Older or duplicate rounds are ignored.

**Q: Must the block number passed to update_voted_metadata or update_verified_block match the current activeBlock?**  
A: Not necessarily.  These two methods record independent consensus metadata: one for QC votes and one for delayed‐execution verification.  They do not modify the active read/write snapshot (that is left to `set_block_and_round` and `finalize`).

**Q: How are `delayed_execution_results` populated?**  
A: The consensus layer (outside this repo) packs any deferred‐execution headers into `consensus_header.delayed_execution_results`.  MonAD only decodes them and validates them via `validate_delayed_execution_results(...)` against the local trie snapshot; the vector is not modified by the execution layer.

**Q: Does each block’s header contain the root after executing that block or N‑2?**  
A: Every block N’s header has its own post‑execution state root.  `block_state.commit(…)` writes the header (including `state_root = state_root()`) under version N, and only then can `finalize(N,…)` succeed.  There is no two‐block lag, and you cannot finalize a block you haven’t executed.

---
**Q: How do RODb and RWDb coordinate across separate processes?**  
A: As noted in the `mpt::Db` interface comment, `find`/`get`/`get_data` return non‑owning cursors that become invalid when the trie root is reloaded—either by an RWDb upsert, an RODb switch, or an RWDb in another process.

```cpp
// libs/db/src/monad/mpt/db.hpp:L87-L96
// The find, get, and get_data API calls return non-owning references.
// The result lifetime ends when a subsequent operation reloads the trie
// root. This can happen due to an RWDb upsert, an RODb reading a different
// version, or an RODb reading the same version that has been updated by an
// RWDb in another process.
```

Under the hood, both RODb and RWDb multiplex on the same on‑disk metadata region via `mmap(..., MAP_SHARED)`.  The ring‑buffer of root/verified/voted versions is stored in these in‑file metadata pages and updated atomically by RWDb; any process mapping the same file sees the new metadata immediately in memory.

```cpp
// libs/db/src/monad/mpt/update_aux.cpp:L563-L572
// Map the two mirror copies of the metadata region via mmap(..., MAP_SHARED)
db_metadata_[0].main = (detail::db_metadata *)mmap(
    nullptr, map_size, prot, MAP_SHARED, fd, offset0);
db_metadata_[1].main = (detail::db_metadata *)mmap(
    nullptr, map_size, prot, MAP_SHARED, fd, offset1);
```

Only the metadata pages (versions/ring buffers) are shared cross‑process.  The actual trie node chunks are loaded into each process’s own memory (via `mmap` or async read) and pinned locally by `OwningNodeCursor` (`shared_ptr<Node>`).  No per‑chunk pin flags are written back to the shared metadata region—only the ring‐buffer pages are memory‐mapped MAP_SHARED, so processes coordinate only on version metadata.  If a version is evicted by one process, readers holding `OwningNodeCursor`s for that version still keep their nodes alive in their own heap.
---
*Last updated:* __DATE__
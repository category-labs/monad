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

*Last updated:* __DATE__
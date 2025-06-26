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

**Q: If you reset to the finalized state and then re‑commit the same (block,round), should the state deltas be computed as s₂ vs s₁ or s₂ vs s₀?**  
A: They must always be diff(s₂ vs s₀).  Before each commit you call `set_block_and_round(finalized_block,nullopt)` to reset the working prefix back to the finalized sub‑trie (state s₀), so `TrieDb::commit`’s guard sees a “new” (block,round) and invokes `copy_trie` to snapshot s₀ again (shallowly, only the root chunk is written).  Then `upsert(state_deltas,version)` applies the entire s₂−s₀ diff and `write_new_root_node(...,version)` simply overwrites that version’s root‐offset in place, yielding exactly s₂ under the proposal prefix and discarding any prior s₁.  
【F:monad/dbsummary2.md†L237-L241】【F:monad/dbsummary2.md†L253-L274】【F:monad/libs/execution/src/monad/db/trie_db.cpp†L484-L489】【F:monad/libs/execution/src/monad/db/trie_db.cpp†L187-L197】【F:monad/libs/db/src/monad/mpt/trie.cpp†L1935-L1946】

**Q: db.commit(…) takes a `MonadConsensusBlockHeader`. Which fields of it does commit actually use?**  
A: Internally, `TrieDb::commit` only *inspects* two parts of the header for prefix/version switching:
  1. `consensus_header.round` → to select `proposal_prefix(round)`;
  2. `consensus_header.execution_inputs.number` → to bump the MPT version (block number).
These drive the `if(consensus_header.round!=round_number_||header.number!=block_number_)` guard.【F:monad/libs/execution/src/monad/db/trie_db.cpp†L161-L169】


Additionally, commit *persists*:
  - The full `consensus_header` (RLP‑encoded under `BFT_BLOCK_NIBBLE`) so all its votes/signatures/delayed results are stored.【F:monad/libs/execution/src/monad/db/trie_db.cpp†L365-L370】
  - The `execution_inputs` block‑header fields (`number`, `timestamp`, etc) are used to build the canonical `BLOCKHEADER_NIBBLE` leaf via `rlp::encode_block_header` (together with computed roots/blooms).【F:monad/libs/execution/src/monad/db/trie_db.cpp†L412-L431】

**Q: In `set_block_and_round`, can the `round_number` argument be `std::nullopt` if the block has been finalized by calling `finalize()`?**  
A: Yes. Passing `std::nullopt` for `round_number` selects the finalized sub‑trie prefix.  The implementation in `TrieDb` is:

```cpp
// libs/execution/src/monad/db/trie_db.cpp:L484-L489
void TrieDb::set_block_and_round(
    uint64_t block_number,
    std::optional<uint64_t> round_number)
{
    if (!db_.is_on_disk()) {
        MONAD_ASSERT(block_number_ == 0);
        MONAD_ASSERT(round_number_ == std::nullopt);
        return;
    }
    prefix_ = round_number.has_value()
                ? proposal_prefix(round_number.value())
                : finalized_nibbles;
    MONAD_ASSERT(db_.find(prefix_, block_number).has_value());
    block_number_ = block_number;
    round_number_ = round_number;
}
```
【F:monad/libs/execution/src/monad/db/trie_db.cpp†L484-L489】

---
## 7. Genesis: Initial State Setup

The genesis block (block 0) is loaded from a JSON file via `read_genesis(…)` in `genesis.hpp`, which parses both the block header and the initial account allocations, then commits and finalizes block 0:

```cpp
// libs/execution/src/monad/execution/genesis.hpp:L132-L146
inline BlockHeader read_genesis(std::filesystem::path const& genesis_file, Db& db) {
    std::ifstream ifile(genesis_file);
    auto const genesis_json = nlohmann::json::parse(ifile);

    StateDeltas state_deltas;
    read_genesis_state(genesis_json, state_deltas);

    MonadConsensusBlockHeader consensus_header{};
    consensus_header.execution_inputs = read_genesis_blockheader(genesis_json);

    db.commit(state_deltas, Code{}, consensus_header);
    db.finalize(0, 0);
    return db.read_eth_header();
}
```

Here, `read_genesis_state` populates `state_deltas` with the `alloc` balances:

```cpp
// libs/execution/src/monad/execution/genesis.hpp:L108-L130
inline void read_genesis_state(nlohmann::json const& genesis_json, StateDeltas& state_deltas) {
    for (auto const& info : genesis_json["alloc"].items()) {
        Address addr{};
        auto const bs = evmc::from_hex("0x" + info.key());
        std::copy_n(bs->begin(), bs->length(), addr.bytes);

        Account acct{};
        acct.balance = intx::from_string<uint256_t>(
            info.value()["wei_balance"].get<std::string>());
        acct.nonce = 0;

        state_deltas.emplace(addr, StateDelta{.account={std::nullopt, acct}});
    }
}
```
【F:monad/libs/execution/src/monad/execution/genesis.hpp†L108-L130】

`TrieDb`’s initial constructor and commit snapshot‑guard automatically handle block 0/round 0:

```cpp
// libs/execution/src/monad/db/trie_db.cpp:L83-L89
TrieDb::TrieDb(mpt::Db& db)
  : db_{db}
  , block_number_{db.get_latest_finalized_block_id()==INVALID_BLOCK_ID?0:db.get_latest_finalized_block_id()}
  , round_number_{std::nullopt}
  , prefix_{finalized_nibbles}
{}

// libs/execution/src/monad/db/trie_db.cpp:L161-L169
if (db_.is_on_disk() &&
    (consensus_header.round != round_number_ ||
     header.number             != block_number_))
{
    // first commit for (0,0): no copy_trie since no prior state
    round_number_ = consensus_header.round;
    block_number_ = header.number;
    prefix_       = proposal_prefix(round_number_);
}
```
【F:monad/libs/execution/src/monad/db/trie_db.cpp†L83-L89】【F:monad/libs/execution/src/monad/db/trie_db.cpp†L161-L169】

Finally, finalizing block 0 shallow‑copies the proposal sub‑trie into the immutable finalized prefix:

```cpp
// libs/execution/src/monad/db/trie_db.cpp:L491-L502
db_.copy_trie(0, proposal_prefix(0), 0, finalized_nibbles, true);
db_.update_finalized_block(0);
```
【F:monad/libs/execution/src/monad/db/trie_db.cpp†L491-L502】

After this sequence, the database’s finalized prefix at version 0 contains the genesis state.

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

Only the metadata pages (versions/ring buffers) are shared cross‑process.  The actual trie node chunks are loaded into each process’s own memory (via `mmap` or async read) and pinned locally by `OwningNodeCursor` (`shared_ptr<Node>`).  No per‑chunk pin flags are written back to the shared metadata region—only the ring‑buffer pages are memory‑mapped MAP_SHARED, so processes coordinate only on version metadata.  If a version is evicted by one process, readers holding `OwningNodeCursor`s for that version still keep their nodes alive in their own heap.

**Q: Doesn’t commit() issue an upsert and reload the trie root—won’t that invalidate existing cursors?**  
A: That comment in the `mpt::Db` interface applies _only_ if you call `find`/`get` on the _same_ mpt::Db instance that then `upsert`s.  In Monad we never mix reads and writes on one instance.  Instead, the execution runloop uses a separate RWOnDisk instance and RPC/CLI use a read‑only RODb instance.  Since RODb never calls upsert, its cursors stay valid even while the writer evicts old versions.

**Q: What if after checking version validity in the ring buffer, the reader is descheduled and another process evicts that version before the disk read completes?**  
A: The MPT I/O path double-checks validity at both ends.
```cpp
// libs/db/src/monad/mpt/find_notify_fiber.cpp:L274-L280
if (!aux.version_is_valid_ondisk(version)) {
    promise.set_value({start, find_result::version_no_longer_exist});
    return;
}
```
That check prevents starting a read for a version already evicted.

```cpp
// libs/db/src/monad/mpt/read_node_blocking.cpp:L22-L24, L54-L57
Node::UniquePtr read_node_blocking(aux, node_offset, version) {
    if (!aux.version_is_valid_ondisk(version)) {
        return {};
    }
    // perform pread(...) into buffer, then:
    return aux.version_is_valid_ondisk(version)
               ? deserialize_node_from_buffer(buffer + buffer_off,
                                             bytes_read - buffer_off)
               : Node::UniquePtr{};
}
```
If eviction occurs mid-read, the post-read check stops stale buffers from returning.

**Q: Does JSON‑RPC eth_call only read finalized state?**  
A: No. The eth_call RPC endpoint accepts both a `block_number` and a `round` argument, then does:
```cpp
// libs/rpc/src/monad/rpc/eth_call.cpp:L90-L94
tdb.set_block_and_round(
    block_number,
    round == mpt::INVALID_ROUND_NUM ? std::nullopt
                                    : std::make_optional(round));
```
If you pass a valid `round`, it reads the *proposal* subtrie (in‑flight state); if you pass `INVALID_ROUND_NUM` (or omit the round), it reads the *finalized* subtrie.

> **Note:** An eth_call handler typically makes several MPT reads (`read_account`, `read_storage`, etc.) to assemble its result, but all of these operate on the same `TrieRODb` instance **and** the same prefix/version set by the single `set_block_and_round` call above.  Since `TrieRODb` never issues upserts or reloads its root, every sub‑read sees a consistent snapshot—even if a concurrent commit occurs in another process.  

**Q: Where and when does the execution layer advance the block number (i.e. the MPT version)?**  
A: In `TrieDb::commit`, at the very start of the method, before assembling any updates.  That bump to `block_number_`/`round_number_` is then used to stamp all ensuing updates, and finally `db_.upsert(..., block_number_, ...)` writes them out:
```cpp
// libs/execution/src/monad/db/trie_db.cpp:L187-L197
if (db_.is_on_disk() && (consensus_header.round != round_number_ ||
                         header.number     != block_number_)) {
    auto const dest_prefix = proposal_prefix(consensus_header.round);
    if (db_.get_latest_block_id() != INVALID_BLOCK_ID) {
        db_.copy_trie(
            block_number_, prefix_, header.number, dest_prefix, false);
    }
    round_number_ = consensus_header.round;
    block_number_ = header.number;
    prefix_       = dest_prefix;
}
```
【F:libs/execution/src/monad/db/trie_db.cpp†L187-L197】

**Q: What exactly does `finalize()` do?  Does it re‑write all leaf (account/storage) values?**  
A: No.  `TrieDb::finalize` simply invokes `copy_trie` to clone the proposal subtrie under `proposal_prefix(round)` into the `finalized_nibbles` prefix—then writes only the new root node and updates the finalized‐block watermark:
```cpp
// libs/execution/src/monad/db/trie_db.cpp:L483-L497
void TrieDb::finalize(uint64_t const block_number, uint64_t const round_number)
{
    if (db_.is_on_disk()) {
        auto const src_prefix = proposal_prefix(round_number);
        MONAD_ASSERT(db_.find(src_prefix, block_number).has_value());
        db_.copy_trie(
            block_number, src_prefix,
            block_number, finalized_nibbles,
            true  // block until root is persisted
        );
        db_.update_finalized_block(block_number);
    }
}
```
【F:libs/execution/src/monad/db/trie_db.cpp†L483-L497】

This performs a deep, in‑memory clone of the subtrie but **does not** eagerly re‑encode all leaf nodes.  Only the new root chunk is written to disk; all child chunks remain shared and are lazy‑loaded.

**Q: Why does commit take a nested `vector<vector<CallFrame>>`? Is this just debugging? Can RPC read it?**  
A: The outer `vector` is per‑transaction and the inner `vector<CallFrame>` is the sequence of EVM call‑trace frames for that transaction.  During commit, `TrieDb` RLP‑encodes and stores these frames under the `CALL_FRAME_NIBBLE` subtrie so tools can fetch post‑execution traces:
```cpp
// libs/execution/src/monad/db/trie_db.cpp:L297-L305
std::span<CallFrame const> frames{call_frames[i]};
byte_string_view view = bytes_alloc_.emplace_back(rlp::encode_call_frames(frames));
// chunk and upsert under CALL_FRAME_NIBBLE …
```
【F:libs/execution/src/monad/db/trie_db.cpp†L297-L305】

The `encode_call_frames`/`decode_call_frames` helpers live in:
```cpp
// libs/execution/src/monad/execution/trace/rlp/call_frame_rlp.hpp:L15-L20
byte_string encode_call_frames(std::span<CallFrame const>);
Result<std::vector<CallFrame>> decode_call_frames(byte_string_view &);
```
【F:libs/execution/src/monad/execution/trace/rlp/call_frame_rlp.hpp†L15-L20】

This feature drives CLI and debug‑trace tooling (e.g. eventual RPC `debug_traceBlockByNumber`‑style endpoints).  There is no consensus requirement on call frames, and today no built‑in JSON‑RPC method reads them—you’d need to traverse the `CALL_FRAME_NIBBLE` subtree and decode manually.
---
*Last updated:* __DATE__
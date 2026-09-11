// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/db_cache.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/vm/vm.hpp>

#include <nlohmann/json_fwd.hpp>

#include <deque>
#include <istream>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

#if KVDB_PROTO
struct KvShadow; // KV-DB prototype shadow reader (defined in trie_db.cpp)

// KV-DB prototype (RPC read side): a standalone read-only opener over the
// flat-page KV device with hazard-pointer block protection for cross-process
// reclamation safety. Defined in trie_db.cpp; the RPC FFI
// (rust/crates/monad-triedb/src/ffi.cpp) drives it through these shims.
struct KvReader;
// Open read-only. `kvhdr_path` is the .kvhdr sidecar; the device is $KVDB_DEVICE.
// Exec must already be up (attaches its /kvdb_hazards + meta). nullptr on failure.
KvReader *kv_reader_open(char const *kvhdr_path);
void kv_reader_close(KvReader *);
// Pin `block` for a request (HP1 block-map walk -> HP2 on the block root -> drop
// HP1). Returns an opaque handle (>= 0) whose HP2 holds the block root, or -1 if
// the block is not retained (pruned / never existed).
// id = the 32-byte proposal id, or nullptr for the finalized block at `block`.
int64_t kv_reader_protect_block(
    KvReader *, uint64_t block, unsigned char const *id);
void kv_reader_end_protect(KvReader *, int64_t handle);

// State, under a handle's pinned block root. Balance is written as 32B
// big-endian so the caller never depends on the C++ uint256 layout; code_hash is
// the raw 32B (== keccak256("") when the account has no code). False = absent.
bool kv_reader_account(
    KvReader *, int64_t handle, unsigned char const *addr,
    unsigned char *out_balance_be, unsigned char *out_code_hash,
    uint64_t *out_nonce);
// Slot value; writes 32 zero bytes when absent (KV stores no zero slots).
void kv_reader_storage(
    KvReader *, int64_t handle, unsigned char const *addr,
    unsigned char const *key, unsigned char *out32);

// Code by hash. Needs no handle: the code tree is grow-only, never reclaimed.
bool kv_reader_code(
    KvReader *, unsigned char const *code_hash, unsigned char const **out,
    uint64_t *out_len);
// Per-block blobs off the pinned block root. `category` is a kv BlobCat:
// 0 receipts, 1 transactions, 2 header, 3 call frames, 4 ommers, 5 withdrawals,
// 6 tx-hash list. Whole-blob categories use kv_reader_block_blob; the per-tx
// table categories (receipts / transactions / call frames) index one tx with
// kv_reader_tx_blob. False = that category is absent for this block.
bool kv_reader_block_blob(
    KvReader *, int64_t handle, uint32_t category, unsigned char const **out,
    uint64_t *out_len);
bool kv_reader_tx_blob(
    KvReader *, int64_t handle, uint32_t category, uint32_t tx_index,
    unsigned char const **out, uint64_t *out_len);
// Is a blob category present for this block at all?
bool kv_reader_blob_present(KvReader *, int64_t handle, uint32_t category);
// Entry count of a per-tx table category (how many txs it covers); -1 if the
// category is absent or is not a per-tx table.
int64_t kv_reader_table_count(KvReader *, int64_t handle, uint32_t category);
// Release a buffer returned by the code / blob reads (new[]/delete[], the same
// convention as triedb_read / triedb_finalize). nullptr is a no-op.
void kv_reader_free(unsigned char const *);

// Global hash indexes; resolution-only and pre-pin, so they take no handle and
// walk under a transient hazard internally.
bool kv_reader_resolve_tx_hash(
    KvReader *, unsigned char const *hash, uint64_t *out_block,
    uint32_t *out_tx_index);
bool kv_reader_resolve_block_hash(
    KvReader *, unsigned char const *hash, uint64_t *out_number);

// Block-tag cursors from KV's metadata: 0 = finalized tip, 1 = oldest retained,
// 2 = latest proposed, 3 = latest voted. Proposed/voted are KV_BLOCK_NONE
// (UINT64_MAX) until consensus first stamps them.
uint64_t kv_reader_cursor(KvReader *, int which);
// One consistent snapshot of all four tag cursors, with the ids of the proposed
// and voted heads. False if no stable (block, id) pair could be read.
bool kv_reader_tags(
    KvReader *, uint64_t *finalized, uint64_t *earliest, uint64_t *proposed,
    unsigned char *proposed_id, uint64_t *voted, unsigned char *voted_id);
// How many times the tag bracket had to re-read (the id changed under it).
uint64_t kv_reader_tag_retries(KvReader *);
#endif

class TrieDb final : public ::monad::Db
{
    ::monad::mpt::Db &db_;
    uint64_t block_number_;
    // bytes32_t{} represent finalized
    bytes32_t proposal_block_id_;
    ::monad::mpt::Nibbles prefix_;
    ::monad::mpt::Node::SharedPtr curr_root_;
    // DbCache default constructor initializes two massive mempools.
    // We only want to pay that price when the cache is enabled, hence
    // the need for unique_ptr.
    std::unique_ptr<DbCache> cache_;
    // True iff this trie reads / writes page-encoded storage (MIP-8).
    // Set at construction; immutable. Exposed via is_page_encoded().
    bool const page_encoded_;

#if KVDB_PROTO
    // KV-DB prototype (read-side): a bulk-built KV image loaded from the
    // KVDB_IMAGE env var. read_account/read_storage shadow-compare against it
    // and count mismatches (see dtor for the report). nullptr if env unset.
    std::unique_ptr<KvShadow> kv_;
#endif

public:
    explicit TrieDb(mpt::Db &, bool enable_multiblock_cache = false);
    ~TrieDb();

    bool is_page_encoded() const override
    {
        return page_encoded_;
    }

    void reset_root(::monad::mpt::Node::SharedPtr root, uint64_t block_number);
    ::monad::mpt::Node::SharedPtr const &get_root() const;

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;
    virtual storage_page_t read_storage_page(
        Address const &, Incarnation, bytes32_t const &page_key) override;
    virtual vm::SharedIntercode read_code(bytes32_t const &) override;
    virtual void set_block_and_prefix(
        uint64_t block_number,
        bytes32_t const &block_id = bytes32_t{}) override;

    virtual void commit(
        bytes32_t const &block_id, CommitBuilder &builder,
        BlockHeader const &header, StateDeltas const &state_deltas,
        Code const &code,
        std::function<void(BlockHeader &)> populate_header_fn) override;

    virtual void
    finalize(uint64_t block_number, bytes32_t const &block_id) override;
    virtual void update_verified_block(uint64_t block_number) override;
    virtual void update_voted_metadata(
        uint64_t block_number, bytes32_t const &block_id) override;
    virtual void update_proposed_metadata(
        uint64_t block_number, bytes32_t const &block_id) override;

    virtual BlockHeader read_eth_header() override;
    virtual bytes32_t state_root() override;
    virtual bytes32_t receipts_root() override;
    virtual bytes32_t transactions_root() override;
    virtual std::optional<bytes32_t> withdrawals_root() override;
    virtual std::string print_stats() override;
    virtual uint64_t get_block_number() const override;

    nlohmann::json to_json(size_t concurrency_limit = 4096);
    uint64_t get_history_length() const;

private:
    /// STATS
    std::atomic<uint64_t> n_account_no_value_{0};
    std::atomic<uint64_t> n_account_value_{0};
    std::atomic<uint64_t> n_storage_no_value_{0};
    std::atomic<uint64_t> n_storage_value_{0};

    void stats_account_no_value()
    {
        n_account_no_value_.fetch_add(1, std::memory_order_release);
    }

    void stats_account_value()
    {
        n_account_value_.fetch_add(1, std::memory_order_release);
    }

    void stats_storage_no_value()
    {
        n_storage_no_value_.fetch_add(1, std::memory_order_release);
    }

    void stats_storage_value()
    {
        n_storage_value_.fetch_add(1, std::memory_order_release);
    }

    bytes32_t merkle_root(mpt::Nibbles const &);

#if KVDB_PROTO
    // Blocking KV reads via the io_uring path (post to io thread, wait).
    std::optional<Account> kv_read_account(Address const &);
    bytes32_t kv_read_storage(Address const &, bytes32_t const &key);
    vm::SharedIntercode kv_read_code(bytes32_t const &code_hash);
    // Testing-only: compare a KV read to the triedb result (mismatch counters).
    void kv_shadow_account(Address const &, std::optional<Account> const &);
    void kv_shadow_code(bytes32_t const &code_hash, vm::SharedIntercode const &);
    void kv_shadow_storage(
        Address const &, bytes32_t const &key, bytes32_t const &value);
    // True when KV is the read source (perf); false = triedb serves + shadow.
    bool kv_serves() const;
    // Multiversion (kvdb_base): historical reads at an explicit ring root, and
    // in-process validation of the ring against triedb at a past version.
    std::optional<Account> kv_read_account_at(Address const &, uint64_t root);
    bytes32_t
    kv_read_storage_at(Address const &, bytes32_t const &key, uint64_t root);
    std::optional<Account> td_read_account_at(
        ::monad::mpt::Node::SharedPtr const &root, uint64_t version,
        Address const &, ::monad::mpt::Nibbles const &top);
    bytes32_t td_read_storage_at(
        ::monad::mpt::Node::SharedPtr const &root, uint64_t version,
        Address const &, bytes32_t const &key, ::monad::mpt::Nibbles const &top);
    void kv_mv_validate(
        uint64_t block, bytes32_t const &block_id,
        std::vector<std::pair<Address, std::optional<bytes32_t>>> const
            &sample);
    // RPC read-side validation (env KVDB_RDTEST=1): drive a KvReader over the
    // live store exactly as the RPC process will -- pin the finalized tip, read
    // state / code / blobs / hash indexes -- and compare against triedb at that
    // version. Opens the reader lazily on first use; see kv_rd_ below.
    // Also pins the block just committed as an undecided proposal, by its id,
    // and compares it against triedb's proposal subtrie -- the only place a
    // live undecided block exists to pin.
    // Validation (env KVDB_TAGTEST=<seconds>): race a reader's tag bracket
    // against a writer thread publishing self-describing (block, id) pairs.
    void tagtest(uint64_t secs);
    // Validation (env KVDB_PGTEST=<pages>): read slots from storage pages whose
    // values are stored out of line, through the RPC reader, vs triedb.
    void pgtest(size_t want);
    void kv_reader_validate(
        uint64_t block, bytes32_t const &block_id,
        std::vector<std::pair<Address, std::optional<bytes32_t>>> const
            &sample);
    KvReader *kv_rd_{nullptr}; // KVDB_RDTEST reader; nullptr when off/unopened
    bool kv_rd_off_{false}; // true once opening has failed (don't retry)
    bool kv_rd_check_{false}; // env KVDB_RDTEST=1 enables the reader checks
    // The finalized tip observed on the first check: the bulk-built base image
    // block, which predates per-block blob writing (kvbuild seeds no blob roots).
    // Blob / index checks apply only to blocks this run committed, i.e. above it.
    uint64_t kv_rd_base_block_{0};
    // KVDB_RDHOLD=<k>: pin the OLDEST retained block and hold that handle for k
    // commits, so exec's prune reaches a root a reader's hazard names. Reads
    // through the held handle must keep returning the values captured at pin
    // time -- the snapshot must neither change nor be freed under us.
    struct KvHoldEntry
    {
        Address addr;
        bytes32_t slot;
        bool has_slot;
        bool got;
        unsigned char acct[72]; // balance32 | code_hash32 | nonce8
        bytes32_t val;
    };
    int64_t kv_hold_h_{-1}; // held handle, -1 = none
    uint64_t kv_hold_block_{0};
    uint64_t kv_hold_left_{0}; // commits remaining before release
    uint64_t kv_hold_n_{0}; // env KVDB_RDHOLD: commits to hold the pin (0 = off)
    std::vector<KvHoldEntry> kv_hold_;
    void kv_reader_hold_step(
        std::vector<std::pair<Address, std::optional<bytes32_t>>> const
            &sample);
#endif
};

MONAD_NAMESPACE_END

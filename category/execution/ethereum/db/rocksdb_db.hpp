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

// Self-guarded: empty unless the RocksDB backend is enabled.
#ifdef MONAD_HAVE_ROCKSDB

    #include <category/core/bytes.hpp>
    #include <category/core/config.hpp>
    #include <category/execution/ethereum/core/block.hpp>
    #include <category/execution/ethereum/db/db.hpp>
    #include <category/statedb/trie_node_store.hpp>

    #include <cstdint>
    #include <filesystem>
    #include <functional>
    #include <memory>
    #include <optional>

namespace rocksdb
{
    class WriteBatch;
}

MONAD_NAMESPACE_BEGIN

class CommitBuilder;
struct RocksDbCommitTrace;

namespace statedb
{
    class KvStore;
}

/// A monad::Db backed by a RocksDB store (the four CFs of category/statedb).
///
/// Reads (account/storage/code) are direct CF_FLAT_STATE / CF_CODE lookups --
/// no trie traversal -- so they scale to any state size. commit() updates the
/// state trie incrementally on disk: it walks CF_TRIE_NODES to assemble a
/// branch-complete witness for the block's touched keys, replays the deltas
/// through PartialTrieDb (the canonical-RLP engine) to recompute the root, and
/// writes the changed flat values, changed trie nodes, and CF_META roots in a
/// single atomic RocksDB WriteBatch (synchronous WAL) per block.
///
/// The three block-local roots (receipts/transactions/withdrawals) are not
/// persistent state; they are recomputed each commit from the CommitBuilder via
/// an ephemeral in-memory trie, exactly as TrieDb derives them.
///
/// Scope (F9, "Option 1"): on-disk incremental trie validated by the parity
/// harness + a bounded replay. Linear replay only -- block_id/proposals and
/// historical-version reads are out of scope for the prototype.
class RocksDbDb final : public Db
{
    std::unique_ptr<statedb::KvStore> kv_;
    statedb::TrieNodeStore nodes_;
    uint64_t block_number_{0};
    BlockHeader last_header_{};

    // Roots produced by the most recent commit(); the populate_header_fn
    // callback reads these back through the getters below mid-commit.
    bytes32_t state_root_{};
    bytes32_t receipts_root_{};
    bytes32_t transactions_root_{};
    std::optional<bytes32_t> withdrawals_root_{};

public:
    RocksDbDb() = delete;
    explicit RocksDbDb(std::filesystem::path const &rocksdb_dir);
    ~RocksDbDb();

    std::optional<Account> read_account(Address const &) override;
    bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;
    vm::SharedIntercode read_code(bytes32_t const &) override;
    BlockHeader read_eth_header() override;

    bytes32_t state_root() override;
    bytes32_t receipts_root() override;
    bytes32_t transactions_root() override;
    std::optional<bytes32_t> withdrawals_root() override;

    void set_block_and_prefix(
        uint64_t block_number,
        bytes32_t const &block_id = bytes32_t{}) override;
    void finalize(uint64_t block_number, bytes32_t const &block_id) override;
    void update_verified_block(uint64_t block_number) override;
    void
    update_voted_metadata(uint64_t block_number, bytes32_t const &) override;
    void
    update_proposed_metadata(uint64_t block_number, bytes32_t const &) override;

    uint64_t get_block_number() const override;

    void commit(
        bytes32_t const &block_id, CommitBuilder &, BlockHeader const &,
        std::unique_ptr<StateDeltas>,
        std::function<void(BlockHeader &)>) override;

    // Offline seed path (the F8 loader). Fold a chunk of flat state + code into
    // the on-disk trie incrementally -- the trie is built up on RocksDB like a
    // MonadDB restore, so peak memory is one chunk, not the whole state.
    // Folding is order-independent (it is just MPT insertion), so the caller
    // can stream the snapshot shard by shard. Updates the running state root;
    // CF_META is written only by seed_finalize. sync=false per chunk for
    // throughput.
    void seed_chunk(std::unique_ptr<StateDeltas> deltas, Code const &code);

    // Finish seeding: gate the running state root against the snapshot's
    // ETH_HEADER stateRoot, then persist CF_META (state_root + finalized).
    void seed_finalize(uint64_t block, bytes32_t const &expected_state_root);

private:
    // Fold `deltas` into the on-disk trie + flat CFs, staged into `batch`, and
    // return the new state root. The shared core of commit() and seed_chunk():
    // assemble a branch-complete witness from CF_TRIE_NODES for the touched
    // keys, replay through PartialTrieDb, and write back the changed nodes +
    // flat values. Consumes `deltas`.
    bytes32_t apply_state_chunk(
        rocksdb::WriteBatch &batch, std::unique_ptr<StateDeltas> deltas,
        RocksDbCommitTrace *trace = nullptr);
};

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB

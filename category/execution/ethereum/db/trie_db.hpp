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

#include <nlohmann/json.hpp>

#include <array>
#include <atomic>
#include <deque>
#include <istream>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

// Per-block aggregate over how many trie nodes each state-trie lookup
// touched. Useful for understanding how the no-keccak key layout affects
// trie depth; the histogram is bounded by the maximum nibble path length.
struct StateLookupStats
{
    uint64_t count = 0;
    double mean = 0.0;
    unsigned p50 = 0;
    unsigned p99 = 0;
    unsigned max = 0;
};

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

public:
    explicit TrieDb(mpt::Db &, bool enable_multiblock_cache = false);
    ~TrieDb();

    void reset_root(::monad::mpt::Node::SharedPtr root, uint64_t block_number);
    ::monad::mpt::Node::SharedPtr const &get_root() const;

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;
    virtual vm::SharedIntercode read_code(bytes32_t const &) override;
    virtual void set_block_and_prefix(
        uint64_t block_number,
        bytes32_t const &block_id = bytes32_t{}) override;

    virtual void commit(
        bytes32_t const &block_id, CommitBuilder &builder,
        BlockHeader const &header, std::unique_ptr<StateDeltas> state_deltas,
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

    // Returns a per-block aggregate of trie-node-visit counts since the last
    // call, and resets the histogram. Thread-safe: called once per block from
    // the runloop while transactions are no longer mutating it.
    StateLookupStats drain_lookup_stats();

private:
    /// STATS
    std::atomic<uint64_t> n_account_no_value_{0};
    std::atomic<uint64_t> n_account_value_{0};
    std::atomic<uint64_t> n_storage_no_value_{0};
    std::atomic<uint64_t> n_storage_value_{0};

    static constexpr size_t LOOKUP_HISTOGRAM_BUCKETS = 256;
    std::array<std::atomic<uint64_t>, LOOKUP_HISTOGRAM_BUCKETS>
        lookup_histogram_{};

    void record_lookup(unsigned nodes_visited)
    {
        auto const bucket = std::min<size_t>(
            nodes_visited, LOOKUP_HISTOGRAM_BUCKETS - 1);
        lookup_histogram_[bucket].fetch_add(1, std::memory_order_relaxed);
    }

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
};

MONAD_NAMESPACE_END

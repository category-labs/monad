#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine.hpp>
#include <monad/vm/vm.hpp>

#include <nlohmann/json.hpp>

#include <deque>
#include <istream>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

class TrieDb final : public ::monad::Db
{
    ::monad::mpt::Db &db_;
    std::deque<mpt::Update> update_alloc_;
    std::deque<byte_string> bytes_alloc_;
    std::deque<hash256> hash_alloc_;
    uint64_t block_number_;
    // bytes32_t{} represent finalized
    bytes32_t proposal_block_id_;
    ::monad::mpt::Nibbles prefix_;

public:
    TrieDb(mpt::Db &);
    ~TrieDb();

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;
    virtual vm::SharedIntercode read_code(bytes32_t const &) override;
    virtual void set_block_and_prefix(
        uint64_t block_number,
        bytes32_t const &block_id = bytes32_t{}) override;
    virtual void commit(
        StateDeltas const &, Code const &, bytes32_t const &block_id,
        BlockHeader const &, std::vector<Receipt> const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Address> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const & = std::nullopt) override;
    virtual void
    finalize(uint64_t block_number, bytes32_t const &block_id) override;
    virtual void update_verified_block(uint64_t block_number) override;
    virtual void update_voted_metadata(
        uint64_t block_number, bytes32_t const &block_id) override;

    virtual BlockHeader read_eth_header() override;
    virtual bytes32_t state_root() override;
    virtual bytes32_t receipts_root() override;
    virtual bytes32_t transactions_root() override;
    virtual std::optional<bytes32_t> withdrawals_root() override;
    virtual std::string print_stats() override;

    nlohmann::json to_json(size_t concurrency_limit = 4096);
    size_t prefetch_current_root();
    uint64_t get_block_number() const;
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
};

MONAD_NAMESPACE_END

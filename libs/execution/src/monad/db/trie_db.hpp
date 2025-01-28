#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/state_machine.hpp>

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
    // read from finalized if it is nullopt
    std::optional<uint64_t> round_number_;
    ::monad::mpt::Nibbles prefix_;

public:
    TrieDb(mpt::Db &);
    ~TrieDb();

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;
    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) override;
    virtual void set_block_and_round(
        uint64_t block_number,
        std::optional<uint64_t> round_number = std::nullopt) override;
    virtual void commit(
        StateDeltas const &, Code const &, MonadConsensusBlockHeader const &,
        std::vector<Transaction> const & = {},
        std::vector<ExecutionResult> const & = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const & = std::nullopt) override;
    virtual void
    finalize(uint64_t block_number, uint64_t round_number) override;
    virtual void update_verified_block(uint64_t) override;

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
    std::atomic<uint64_t> n_storage_no_value_{0};
    std::atomic<uint64_t> n_storage_value_{0};

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

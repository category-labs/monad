#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/code_analysis.hpp>
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

MONAD_NAMESPACE_BEGIN

class TrieDb final : public ::monad::Db
{
    ::monad::mpt::Db &db_;
    std::deque<mpt::Update> update_alloc_;
    std::deque<byte_string> bytes_alloc_;
    std::deque<hash256> hash_alloc_;
    uint64_t block_number_;

public:
    TrieDb(mpt::Db &);
    ~TrieDb();

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;
    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) override;
    virtual void increment_block_number() override;
    virtual void commit(
        StateDeltas const &, Code const &, BlockHeader const &,
        std::vector<Receipt> const & = {},
        std::vector<Transaction> const & = {},
        std::optional<std::vector<Withdrawal>> const & = {
            std::nullopt}) override;
    virtual bytes32_t state_root() override;
    virtual bytes32_t receipts_root() override;
    virtual bytes32_t transactions_root() override;
    virtual std::optional<bytes32_t> withdrawals_root() override;
    virtual std::string print_stats() override;

    nlohmann::json to_json();
    size_t prefetch_current_root();
    uint64_t get_block_number() const;
    uint64_t get_history_length() const;

    // for testing only
    std::pair<bytes32_t, bytes32_t>
    read_storage_and_slot(Address const &, bytes32_t const &key);

    void set_block_number(uint64_t);

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

#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/state_machine.hpp>

#include <nlohmann/json.hpp>

#include <istream>
#include <list>
#include <memory>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

class TrieDb final : public ::monad::Db
{
    struct Machine;
    struct InMemoryMachine;
    struct OnDiskMachine;

    std::unique_ptr<Machine> machine_;
    ::monad::mpt::Db db_;
    std::list<mpt::Update> update_alloc_;
    std::list<byte_string> bytes_alloc_;
    std::list<hash256> hash_alloc_;
    uint64_t block_number_;

public:
    TrieDb(mpt::ReadOnlyOnDiskDbConfig const &);
    TrieDb(std::optional<mpt::OnDiskDbConfig> const &);
    // parse from binary
    TrieDb(
        std::optional<mpt::OnDiskDbConfig> const &, std::istream &accounts,
        std::istream &code, uint64_t init_block_number = 0,
        size_t buf_size = 1ul << 31);
    ~TrieDb();

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;
    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) override;
    virtual void increment_block_number() override;
    virtual void commit(
        StateDeltas const &, Code const &,
        std::vector<Receipt> const & = {}) override;
    virtual bytes32_t state_root() override;
    virtual bytes32_t receipts_root() override;
    virtual std::string print_stats() override;

    nlohmann::json to_json();
    size_t prefetch_current_root();
    uint64_t get_block_number() const;

    // for testing only
    std::pair<bytes32_t, bytes32_t>
    read_storage_and_slot(Address const &, bytes32_t const &key);

    // read-only operations
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
};

MONAD_NAMESPACE_END

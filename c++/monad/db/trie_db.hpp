#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
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

MONAD_NAMESPACE_BEGIN

class TrieDb final : public ::monad::DbRW
{
    struct Machine;
    struct InMemoryMachine;
    struct OnDiskMachine;

    std::unique_ptr<Machine> machine_;
    ::monad::mpt::Db db_;
    std::list<mpt::Update> update_alloc_;
    std::list<byte_string> bytes_alloc_;
    uint64_t curr_block_id_;
    bool is_on_disk_;

public:
    TrieDb(std::optional<mpt::OnDiskDbConfig> const &);
    // parse from binary
    TrieDb(
        std::optional<mpt::OnDiskDbConfig> const &, std::istream &accounts,
        std::istream &code, uint64_t init_block_number = 0,
        size_t buf_size = 1ul << 31);
    ~TrieDb();

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, bytes32_t const &key) override;
    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) override;
    virtual void increment_block_number() override;
    virtual void commit(
        StateDeltas const &, Code const &,
        std::vector<Receipt> const & = {}) override;
    virtual bytes32_t state_root() override;
    virtual bytes32_t receipts_root() override;
    virtual void create_and_prune_block_history(uint64_t) const override;

    nlohmann::json to_json();
    uint64_t current_block_number() const;
};

MONAD_NAMESPACE_END

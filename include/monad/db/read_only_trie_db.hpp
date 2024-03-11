#pragma once

#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/mpt/read_only_db.hpp>

#include <memory>
#include <optional>

MONAD_DB_NAMESPACE_BEGIN

class ReadOnlyTrieDb final : public ::monad::Db
{
private:
    ::monad::mpt::ReadOnlyDb ro_db_;
    uint64_t curr_block_id_;

public:
    ReadOnlyTrieDb(
        mpt::ReadOnlyOnDiskDbConfig const &ro_db, uint64_t const curr_block_id)
        : ro_db_{ro_db}
        , curr_block_id_{curr_block_id}
    {
    }

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, bytes32_t const &key) override;
    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) override;
    virtual bytes32_t state_root() override;

    virtual void create_and_prune_block_history(uint64_t) const override {}

    virtual void increment_block_number() override {}

    virtual void commit(StateDeltas const &, Code const &) override{};

    uint64_t current_block_number() const;
};

MONAD_DB_NAMESPACE_END

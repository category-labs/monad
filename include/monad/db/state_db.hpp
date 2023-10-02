#pragma once

#include <monad/config.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/state_deltas.hpp>

#include <absl/container/btree_map.h>

#include <cstdint>
#include <filesystem>
#include <memory>
#include <optional>
#include <vector>

namespace rocksdb
{
    class ColumnFamilyHandle;
    class DB;
    class WriteBatch;
}

MONAD_NAMESPACE_BEGIN

class StateDb final : public Db
{
    std::filesystem::path const path_;
    std::vector<rocksdb::ColumnFamilyHandle *> cfs_;
    std::unique_ptr<rocksdb::DB> const db_;
    std::unique_ptr<rocksdb::WriteBatch> const batch_;

public:
    StateDb(std::filesystem::path const &);
    ~StateDb();

    virtual std::optional<Account>
    read_account(address_t const &) const override;

    std::optional<Account>
    read_account_history(address_t const &, uint64_t block_number);

    virtual bytes32_t
    read_storage(address_t const &, bytes32_t const &location) const override;

    bytes32_t read_storage_history(
        address_t const &, bytes32_t const &location, uint64_t block_number);

    virtual byte_string read_code(bytes32_t const &) const override;

    using Accounts =
        typename absl::btree_map<address_t, std::optional<Account>>;

    void write_accounts(Accounts const &);

    using Storage = typename absl::btree_map<
        address_t,
        absl::btree_map<uint64_t, absl::btree_map<bytes32_t, bytes32_t>>>;

    void write_storage(Storage const &);

    using AccountChanges = absl::btree_map<address_t, byte_string>;
    using StorageChanges = absl::btree_map<
        address_t,
        absl::btree_map<uint64_t, absl::btree_map<bytes32_t, byte_string>>>;

    void
    write_account_history(absl::btree_map<uint64_t, AccountChanges> const &);

    void
    write_storage_history(absl::btree_map<uint64_t, StorageChanges> const &);

    void revert();
    void commit();

    void commit(state::StateChanges const &) override
    {
        // TODO
        MONAD_ASSERT(false);
    }

    void commit(StateDeltas const &, Code const &) override
    {
        // TODO
        MONAD_ASSERT(false);
    }

    void create_and_prune_block_history(uint64_t) const override
    {
        // TODO
        MONAD_ASSERT(false);
    }

    auto *db() const { return db_.get(); } // TODO remove
};

MONAD_NAMESPACE_END

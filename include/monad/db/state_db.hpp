#pragma once

#include <monad/config.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

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

class StateDb final
{
    std::filesystem::path const path_;
    std::vector<rocksdb::ColumnFamilyHandle *> cfs_;
    std::unique_ptr<rocksdb::DB> const db_;
    std::unique_ptr<rocksdb::WriteBatch> const batch_;

public:
    StateDb(std::filesystem::path const &);
    ~StateDb();

    std::optional<Account> read_account(address_t const &);

    std::optional<Account>
    read_account_history(address_t const &, uint64_t block_number);

    bytes32_t read_storage(
        address_t const &, uint64_t incarnation, bytes32_t const &location);

    bytes32_t read_storage_history(
        address_t const &, uint64_t incarnation, bytes32_t const &location,
        uint64_t block_number);

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

    auto *db() const { return db_.get(); } // TODO remove
};

MONAD_NAMESPACE_END

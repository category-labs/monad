#pragma once

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db_interface.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/rlp/encode_helpers.hpp>
#include <monad/trie/assert.h>

#include <fmt/chrono.h>
#include <fmt/format.h>
#include <rocksdb/db.h>

#include <filesystem>

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    constexpr auto
    make_basic_storage_key(address_t const &a, bytes32_t const &k)
    {
        byte_string_fixed<sizeof(address_t) + sizeof(bytes32_t)> key;
        std::copy_n(a.bytes, sizeof(address_t), key.data());
        std::copy_n(k.bytes, sizeof(bytes32_t), &key[sizeof(address_t)]);
        return key;
    }
}

// Database impl without trie root generating logic, backed by rocksdb
struct RocksDB
    : public DBInterface<RocksDB, monad::execution::BoostFiberExecution>
{
    using DBInterface<RocksDB, monad::execution::BoostFiberExecution>::updates;

    std::filesystem::path const name;
    rocksdb::Options options;
    std::vector<rocksdb::ColumnFamilyDescriptor> cfds;
    std::vector<rocksdb::ColumnFamilyHandle *> cfs;
    std::shared_ptr<rocksdb::DB> db;
    rocksdb::WriteBatch batch;

    RocksDB(std::filesystem::path name = std::filesystem::absolute("db"))
        : name(name)
        , options([]() {
            rocksdb::Options ret;
            ret.IncreaseParallelism(2);
            ret.OptimizeLevelStyleCompaction();
            ret.create_if_missing = true;
            ret.create_missing_column_families = true;
            return ret;
        }())
        , cfds([&]() -> decltype(cfds) {
            return {
                {rocksdb::kDefaultColumnFamilyName, {}},
                {"PlainAccounts", {}},
                {"PlainStorage", {}}};
        }())
        , cfs()
        , db([&]() {
            if (std::filesystem::exists(name)) {
                MONAD_ASSERT(std::filesystem::is_directory(name));
            }
            else {
                std::filesystem::create_directory(name);
            }

            rocksdb::DB *db = nullptr;

            rocksdb::Status const s = rocksdb::DB::Open(
                options,
                name / fmt::format("{}", std::chrono::system_clock::now()),
                cfds,
                &cfs,
                &db);

            MONAD_ROCKS_ASSERT(s);
            MONAD_ASSERT(cfds.size() == cfs.size());

            return db;
        }())
        , batch()
    {
    }

    ~RocksDB()
    {
        rocksdb::Status res;
        for (auto *const cf : cfs) {
            res = db->DestroyColumnFamilyHandle(cf);
            MONAD_ASSERT(res.ok());
        }

        res = db->Close();
        MONAD_ROCKS_ASSERT(res);
    }

    ////////////////////////////////////////////////////////////////////
    // Helper functions
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] constexpr auto *accounts_cf() { return cfs[1]; }
    [[nodiscard]] constexpr auto *storage_cf() { return cfs[2]; }

    void commit_db()
    {
        rocksdb::WriteOptions options;
        options.disableWAL = true;
        db->Write(options, &batch);
        batch.Clear();
    }

    ////////////////////////////////////////////////////////////////////
    // DBInterface implementations
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] bool contains(address_t const &a)
    {
        rocksdb::PinnableSlice value;
        auto const res =
            db->Get(rocksdb::ReadOptions{}, accounts_cf(), to_slice(a), &value);
        MONAD_ASSERT(res.ok() || res.IsNotFound());
        return res.ok();
    }

    [[nodiscard]] bool contains(address_t const &a, bytes32_t const &k)
    {
        auto const key = detail::make_basic_storage_key(a, k);
        rocksdb::PinnableSlice value;
        auto const res = db->Get(
            rocksdb::ReadOptions{}, storage_cf(), to_slice(key), &value);
        MONAD_ASSERT(res.ok() || res.IsNotFound());
        return res.ok();
    }

    [[nodiscard]] std::optional<Account> try_find(address_t const &a)
    {
        rocksdb::PinnableSlice value;
        auto const res =
            db->Get(rocksdb::ReadOptions{}, accounts_cf(), to_slice(a), &value);
        if (res.IsNotFound()) {
            return std::nullopt;
        }
        MONAD_ASSERT(res.ok());

        Account ret;
        bytes32_t _;
        auto const rest = rlp::decode_account(
            ret,
            _,
            {reinterpret_cast<byte_string_view::value_type const *>(
                 value.data()),
             value.size()});
        MONAD_ASSERT(rest.empty());
        return ret;
    }

    [[nodiscard]] std::optional<bytes32_t>
    try_find(address_t const &a, bytes32_t const &k)
    {
        auto const key = detail::make_basic_storage_key(a, k);
        rocksdb::PinnableSlice value;
        auto const res = db->Get(
            rocksdb::ReadOptions{}, storage_cf(), to_slice(key), &value);
        if (res.IsNotFound()) {
            return std::nullopt;
        }
        MONAD_ROCKS_ASSERT(res);
        MONAD_ASSERT(value.size() == sizeof(bytes32_t));
        bytes32_t result;
        std::copy_n(value.data(), sizeof(bytes32_t), result.bytes);
        return result;
    }

    void commit_storage_impl()
    {
        for (auto const &[a, updates] : updates.storage) {
            for (auto const &[k, v] : updates) {
                auto const key = detail::make_basic_storage_key(a, k);
                if (v != bytes32_t{}) {
                    auto const res =
                        batch.Put(storage_cf(), to_slice(key), to_slice(v));
                    MONAD_ROCKS_ASSERT(res);
                }
                else {
                    auto const res = batch.Delete(storage_cf(), to_slice(key));
                    MONAD_ROCKS_ASSERT(res);
                }
            }
        }
        commit_db();
    }

    void commit_accounts_impl()
    {
        for (auto const &[a, acct] : updates.accounts) {
            if (acct.has_value()) {
                // Note: no storage root calculations in this mode
                auto const res = batch.Put(
                    accounts_cf(),
                    to_slice(a),
                    to_slice(rlp::encode_account(acct.value(), NULL_ROOT)));
                MONAD_ROCKS_ASSERT(res);
            }
            else {
                auto const res = batch.Delete(accounts_cf(), to_slice(a));
                MONAD_ROCKS_ASSERT(res);
            }
        }
        commit_db();
    }
};

MONAD_DB_NAMESPACE_END

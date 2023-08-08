#pragma once

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/db/assert.h>
#include <monad/db/auto_detect_start_block_number.hpp>
#include <monad/db/config.hpp>
#include <monad/db/create_and_prune_block_history.hpp>
#include <monad/db/db_interface.hpp>
#include <monad/db/prepare_state.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/logging/monad_log.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/rlp/encode_helpers.hpp>

#include <fmt/chrono.h>
#include <fmt/format.h>
#include <rocksdb/db.h>

#include <filesystem>
#include <type_traits>

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

    // Database impl without trie root generating logic, backed by rocksdb
    template <typename TExecutor, Permission TPermission>
    struct RocksDB
        : public DBInterface<
              RocksDB<TExecutor, TPermission>, TExecutor, TPermission>
    {
        using this_t = RocksDB<TExecutor, TPermission>;

        std::filesystem::path const root;
        rocksdb::Options options;
        std::vector<rocksdb::ColumnFamilyDescriptor> cfds;
        std::vector<rocksdb::ColumnFamilyHandle *> cfs;
        std::shared_ptr<rocksdb::DB> db;

        // batch occupies no space if we are in read only
        struct Empty
        {
        };
        [[no_unique_address]] std::conditional_t<
            Writable<TPermission>, rocksdb::WriteBatch, Empty>
            batch;

        uint64_t const starting_block_number;

        using block_history_size_t =
            std::conditional_t<Writable<TPermission>, uint64_t, Empty>;
        [[no_unique_address]] block_history_size_t const block_history_size;

        decltype(monad::log::logger_t::get_logger()) logger =
            monad::log::logger_t::get_logger("rocks_db_logger");
        static_assert(std::is_pointer_v<decltype(logger)>);

        ////////////////////////////////////////////////////////////////////
        // Constructor & Destructor
        ////////////////////////////////////////////////////////////////////

        RocksDB(std::filesystem::path root, uint64_t block_history_size)
            requires Writable<TPermission>
            : RocksDB(
                  root, auto_detect_start_block_number(root),
                  block_history_size)
        {
        }

        RocksDB(
            std::filesystem::path root, uint64_t const starting_block_number)
            requires(!Writable<TPermission>)
            : RocksDB(root, starting_block_number, Empty{})
        {
        }

        RocksDB(
            std::filesystem::path root, uint64_t starting_block_number,
            block_history_size_t block_history_size)
            requires Readable<TPermission>
            : root(root)
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
                rocksdb::DB *db = nullptr;

                auto const path = [&]() {
                    if constexpr (Writable<TPermission>) {
                        return prepare_state<RocksDB, TExecutor, TPermission>(
                            root, starting_block_number);
                    }
                    else {
                        // in read only mode, starting_block_number needs to be
                        // greater than 0 such that we read a valid checkpoint
                        MONAD_ASSERT(starting_block_number);
                        return find_starting_checkpoint<this_t>(
                            root, starting_block_number);
                    }
                }();
                if (!path.has_value()) {
                    throw std::runtime_error(path.error());
                }

                auto const status = [&]() {
                    if constexpr (Writable<TPermission>) {
                        return rocksdb::DB::Open(
                            options, path.value(), cfds, &cfs, &db);
                    }
                    else {
                        return rocksdb::DB::OpenForReadOnly(
                            options, path.value(), cfds, &cfs, &db);
                    }
                }();

                MONAD_ROCKS_ASSERT(status);
                MONAD_ASSERT(cfds.size() == cfs.size());

                return db;
            }())
            , batch()
            , starting_block_number(starting_block_number)
            , block_history_size(block_history_size)
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

        ////////////////////////////////////////////////////////////////////
        // DBInterface implementations
        ////////////////////////////////////////////////////////////////////

        [[nodiscard]] bool contains_impl(address_t const &a)
            requires Readable<TPermission>
        {
            rocksdb::PinnableSlice value;
            auto const res = db->Get(
                rocksdb::ReadOptions{}, accounts_cf(), to_slice(a), &value);
            MONAD_ASSERT(res.ok() || res.IsNotFound());
            return res.ok();
        }

        [[nodiscard]] bool contains_impl(address_t const &a, bytes32_t const &k)
            requires Readable<TPermission>
        {
            auto const key = detail::make_basic_storage_key(a, k);
            rocksdb::PinnableSlice value;
            auto const res = db->Get(
                rocksdb::ReadOptions{}, storage_cf(), to_slice(key), &value);
            MONAD_ASSERT(res.ok() || res.IsNotFound());
            return res.ok();
        }

        [[nodiscard]] std::optional<Account> try_find_impl(address_t const &a)
            requires Readable<TPermission>
        {
            rocksdb::PinnableSlice value;
            auto const res = db->Get(
                rocksdb::ReadOptions{}, accounts_cf(), to_slice(a), &value);
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

        [[nodiscard]] bytes32_t
        try_find_impl(address_t const &a, bytes32_t const &k)
            requires Readable<TPermission>
        {
            auto const key = detail::make_basic_storage_key(a, k);
            rocksdb::PinnableSlice value;
            auto const res = db->Get(
                rocksdb::ReadOptions{}, storage_cf(), to_slice(key), &value);
            if (res.IsNotFound()) {
                return bytes32_t{};
            }
            MONAD_ROCKS_ASSERT(res);
            MONAD_ASSERT(value.size() == sizeof(bytes32_t));
            bytes32_t result;
            std::copy_n(value.data(), sizeof(bytes32_t), result.bytes);
            return result;
        }

        void commit(state::changeset auto const &obj)
            requires Writable<TPermission>
        {
            for (auto const &[a, updates] : obj.storage_changes) {
                for (auto const &[k, v] : updates) {
                    auto const key = detail::make_basic_storage_key(a, k);
                    if (v != bytes32_t{}) {
                        auto const res =
                            batch.Put(storage_cf(), to_slice(key), to_slice(v));
                        MONAD_ROCKS_ASSERT(res);
                    }
                    else {
                        auto const res =
                            batch.Delete(storage_cf(), to_slice(key));
                        MONAD_ROCKS_ASSERT(res);
                    }
                }
            }

            for (auto const &[a, acct] : obj.account_changes) {
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

            rocksdb::WriteOptions options;
            options.disableWAL = true;
            db->Write(options, &batch);
            batch.Clear();
        }

        void create_and_prune_block_history(uint64_t block_number) const
            requires Writable<TPermission>
        {
            auto const s = ::monad::db::create_and_prune_block_history(
                *this, block_number);
            if (!s.has_value()) {
                // this is not a critical error in production, we can continue
                // executing with the current database while someone
                // investigates
                MONAD_LOG_ERROR(
                    logger,
                    "Unable to save block_number {} for {} error={}",
                    block_number,
                    as_string<RocksDB>(),
                    s.error());
            }

            // kill in debug
            MONAD_DEBUG_ASSERT(s.has_value());
        }
    };
}

using RocksDB =
    detail::RocksDB<monad::execution::BoostFiberExecution, ReadWrite>;
using ReadOnlyRocksDB =
    detail::RocksDB<monad::execution::BoostFiberExecution, ReadOnly>;

MONAD_DB_NAMESPACE_END

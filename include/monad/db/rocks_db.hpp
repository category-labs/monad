#pragma once

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/assert.h>
#include <monad/db/auto_detect_start_block_number.hpp>
#include <monad/db/config.hpp>
#include <monad/db/create_and_prune_block_history.hpp>
#include <monad/db/db.hpp>
#include <monad/db/permission.hpp>
#include <monad/db/prepare_state.hpp>
#include <monad/db/rocks_db_helper.hpp>
#include <monad/db/util.hpp>
#include <monad/logging/monad_log.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/rlp/encode_helpers.hpp>

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

    [[nodiscard]] inline std::shared_ptr<rocksdb::DB> open_rocks_db(
        std::filesystem::path root, uint64_t starting_block_number,
        std::vector<rocksdb::ColumnFamilyHandle *> &cfs,
        std::variant<ReadOnly, Writable> permission)
    {
        rocksdb::Options options;
        options.IncreaseParallelism(2);
        options.OptimizeLevelStyleCompaction();
        options.create_if_missing = true;
        options.create_missing_column_families = true;

        std::vector<rocksdb::ColumnFamilyDescriptor> const cfds = {
            {rocksdb::kDefaultColumnFamilyName, {}},
            {"PlainAccounts", {}},
            {"PlainStorage", {}},
            {"Code", {}}};

        auto const path = [&]() {
            if (std::holds_alternative<ReadOnly>(permission)) {
                // in read only mode, starting_block_number needs to be
                // greater than 0 such that we read a valid checkpoint
                MONAD_ASSERT(starting_block_number);
                return find_starting_checkpoint<monad::db::RocksDB>(
                    root, starting_block_number);
            }
            else {
                return prepare_state<monad::db::RocksDB>(
                    root, starting_block_number);
            }
        }();
        if (!path.has_value()) {
            throw std::runtime_error(path.error());
        }

        rocksdb::DB *db = nullptr;

        auto const status = [&]() {
            if (std::holds_alternative<ReadOnly>(permission)) {
                return rocksdb::DB::OpenForReadOnly(
                    options, path.value(), cfds, &cfs, &db);
            }
            else {
                return rocksdb::DB::Open(
                    options, path.value(), cfds, &cfs, &db);
            }
        }();

        MONAD_ROCKS_ASSERT(status);
        MONAD_ASSERT(cfds.size() == cfs.size());

        return std::shared_ptr<rocksdb::DB>{db};
    }
}

// Database impl without trie root generating logic, backed by rocksdb
struct RocksDB : public Db
{
    std::filesystem::path const root;
    std::vector<rocksdb::ColumnFamilyHandle *> cfs;
    rocksdb::WriteBatch batch;
    uint64_t const starting_block_number;
    uint64_t const block_history_size;
    std::shared_ptr<rocksdb::DB> db;

    decltype(monad::log::logger_t::get_logger()) logger =
        monad::log::logger_t::get_logger("rocks_db_logger");
    static_assert(std::is_pointer_v<decltype(logger)>);

    ////////////////////////////////////////////////////////////////////
    // Constructor & Destructor
    ////////////////////////////////////////////////////////////////////

    RocksDB(
        ReadOnly, std::filesystem::path root,
        std::optional<uint64_t> opt_starting_block_number)
        : RocksDB(ReadOnly{}, root, opt_starting_block_number, 0)
    {
    }

    RocksDB(
        std::variant<ReadOnly, Writable> permission, std::filesystem::path root,
        std::optional<uint64_t> opt_starting_block_number,
        uint64_t block_history_size)
        : root(root)
        , starting_block_number(opt_starting_block_number.value_or(
              auto_detect_start_block_number(root)))
        , block_history_size(block_history_size)
        , db(detail::open_rocks_db(
              root, starting_block_number, cfs, permission))
    {
        MONAD_DEBUG_ASSERT(
            std::holds_alternative<Writable>(permission) ||
            block_history_size == 0);
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

    [[nodiscard]] constexpr auto *accounts_cf() const { return cfs[1]; }
    [[nodiscard]] constexpr auto *storage_cf() const { return cfs[2]; }
    [[nodiscard]] constexpr auto *code_cf() const { return cfs[3]; }

    ////////////////////////////////////////////////////////////////////
    // Db implementations
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] std::optional<Account>
    read_account(address_t const &a) const override
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

    [[nodiscard]] bytes32_t
    read_storage(address_t const &a, uint64_t, bytes32_t const &k) const override
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

    [[nodiscard]] byte_string read_code(bytes32_t const &b) const override
    {
        return detail::rocks_db_read_code(b, db, code_cf());
    }

    void commit(state::StateChanges const &obj) override
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
                    auto const res = batch.Delete(storage_cf(), to_slice(key));
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

        detail::rocks_db_commit_code_to_batch(batch, obj, code_cf());

        rocksdb::WriteOptions options;
        options.disableWAL = true;
        db->Write(options, &batch);
        batch.Clear();
    }

    void create_and_prune_block_history(uint64_t block_number) const override
    {
        auto const s = ::monad::db::create_and_prune_block_history(
            root, db, block_number, block_history_size);
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

MONAD_DB_NAMESPACE_END

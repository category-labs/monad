#pragma once

#include <monad/db/auto_detect_start_block_number.hpp>
#include <monad/db/config.hpp>
#include <monad/db/create_and_prune_block_history.hpp>
#include <monad/db/db.hpp>
#include <monad/db/permission.hpp>
#include <monad/db/prepare_state.hpp>
#include <monad/db/rocks_db_helper.hpp>
#include <monad/db/trie_db_process_changes.hpp>
#include <monad/db/trie_db_read_account.hpp>
#include <monad/db/trie_db_read_storage.hpp>
#include <monad/logging/formatter.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/rocks_cursor.hpp>
#include <monad/trie/rocks_writer.hpp>
#include <monad/trie/trie.hpp>

#include <quill/Quill.h>

#include <filesystem>
#include <string_view>

MONAD_DB_NAMESPACE_BEGIN

struct RocksTrieDB;

namespace detail
{
    [[nodiscard]] inline std::shared_ptr<rocksdb::DB> open_rocks_trie_db(
        std::filesystem::path root, uint64_t starting_block_number,
        trie::PathComparator &accounts_comparator,
        trie::PrefixPathComparator &storage_comparator,
        std::vector<rocksdb::ColumnFamilyHandle *> &cfs,
        std::variant<ReadOnly, Writable> permission)
    {
        rocksdb::Options options;
        options.IncreaseParallelism(2);
        options.OptimizeLevelStyleCompaction();
        options.create_if_missing = true;
        options.create_missing_column_families = true;

        rocksdb::ColumnFamilyOptions accounts_opts;
        rocksdb::ColumnFamilyOptions storage_opts;
        accounts_opts.comparator = &accounts_comparator;
        storage_opts.comparator = &storage_comparator;

        std::vector<rocksdb::ColumnFamilyDescriptor> const cfds = {
            {rocksdb::kDefaultColumnFamilyName, {}},
            {"AccountTrieLeaves", accounts_opts},
            {"AccountTrieAll", accounts_opts},
            {"StorageTrieLeaves", storage_opts},
            {"StorageTrieAll", storage_opts},
            {"Code", {}}};

        auto const path = [&]() {
            if (std::holds_alternative<ReadOnly>(permission)) {
                // in read only mode, starting_block_number needs to be
                // greater than 0 such that we read a valid checkpoint
                MONAD_ASSERT(starting_block_number);
                return find_starting_checkpoint<monad::db::RocksTrieDB>(
                    root, starting_block_number);
            }
            else {
                return prepare_state<monad::db::RocksTrieDB>(
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

// Database impl with trie root generating logic, backed by rocksdb
struct RocksTrieDB : public Db
{
    struct Trie
    {
        trie::RocksCursor leaves_cursor;
        trie::RocksCursor trie_cursor;
        trie::RocksWriter leaves_writer;
        trie::RocksWriter trie_writer;

        trie::Trie<trie::RocksCursor, trie::RocksWriter> trie;

        Trie(
            std::shared_ptr<rocksdb::DB> db, rocksdb::WriteBatch &batch,
            rocksdb::ColumnFamilyHandle *lc, rocksdb::ColumnFamilyHandle *tc)
            : leaves_cursor(db, lc)
            , trie_cursor(db, tc)
            , leaves_writer(trie::RocksWriter{.batch = batch, .cf = lc})
            , trie_writer(trie::RocksWriter{.batch = batch, .cf = tc})
            , trie(leaves_cursor, trie_cursor, leaves_writer, trie_writer)
        {
        }

        void reset_cursor()
        {
            leaves_cursor.reset();
            trie_cursor.reset();
        }

        [[nodiscard]] trie::RocksCursor make_leaf_cursor() const
        {
            return trie::RocksCursor{leaves_cursor.db_, leaves_cursor.cf_};
        }

        [[nodiscard]] trie::RocksCursor make_trie_cursor() const
        {
            return trie::RocksCursor{trie_cursor.db_, trie_cursor.cf_};
        }
    };

    std::filesystem::path const root;
    uint64_t const starting_block_number;
    trie::PathComparator accounts_comparator;
    trie::PrefixPathComparator storage_comparator;
    std::vector<rocksdb::ColumnFamilyHandle *> cfs;
    std::shared_ptr<rocksdb::DB> db;
    Trie accounts_trie;
    Trie storage_trie;
    uint64_t const block_history_size;
    rocksdb::WriteBatch batch;

    ////////////////////////////////////////////////////////////////////
    // Constructor & Destructor
    ////////////////////////////////////////////////////////////////////

    RocksTrieDB(
        ReadOnly, std::filesystem::path root,
        std::optional<uint64_t> opt_starting_block_number)
        : RocksTrieDB(ReadOnly{}, root, opt_starting_block_number, 0)
    {
    }

    RocksTrieDB(
        std::variant<ReadOnly, Writable> permission, std::filesystem::path root,
        std::optional<uint64_t> opt_starting_block_number,
        uint64_t block_history_size)
        : root(root)
        , starting_block_number(opt_starting_block_number.value_or(
              auto_detect_start_block_number(root)))
        , db(detail::open_rocks_trie_db(
              root, starting_block_number, accounts_comparator,
              storage_comparator, cfs, permission))
        , accounts_trie(db, batch, cfs[1], cfs[2])
        , storage_trie(db, batch, cfs[3], cfs[4])
        , block_history_size(block_history_size)
    {
        MONAD_DEBUG_ASSERT(
            std::holds_alternative<Writable>(permission) ||
            block_history_size == 0);
    }

    ~RocksTrieDB()
    {
        accounts_trie.reset_cursor();
        storage_trie.reset_cursor();

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

    [[nodiscard]] constexpr auto *code_cf() const { return cfs[5]; }

    ////////////////////////////////////////////////////////////////////
    // Db implementations
    ////////////////////////////////////////////////////////////////////

    static constexpr std::string_view db_type() noexcept
    {
        return "rockstriedb";
    }

    [[nodiscard]] std::optional<Account>
    read_account(address_t const &a) const override
    {
        return trie_db_read_account(
            a,
            accounts_trie.make_leaf_cursor(),
            accounts_trie.make_trie_cursor());
    }

    [[nodiscard]] bytes32_t
    read_storage(address_t const &a, bytes32_t const &key) const override
    {
        return trie_db_read_storage(
            a,
            key,
            storage_trie.make_leaf_cursor(),
            storage_trie.make_trie_cursor());
    }

    [[nodiscard]] byte_string read_code(bytes32_t const &ch) const override
    {
        return detail::rocks_db_read_code(ch, db, code_cf());
    }

    void
    commit(StateDeltas const &state_deltas, Code const &code_delta) override
    {
        detail::rocks_db_commit_code_to_batch(batch, code_delta, code_cf());

        trie_db_process_changes(state_deltas, accounts_trie, storage_trie);

        rocksdb::WriteOptions options;
        options.disableWAL = true;
        db->Write(options, &batch);
        batch.Clear();

        accounts_trie.reset_cursor();
        storage_trie.reset_cursor();
    }

    void create_and_prune_block_history(uint64_t block_number) const override
    {
        auto const s = ::monad::db::create_and_prune_block_history(
            root, db, block_number, block_history_size);
        if (!s.has_value()) {
            // this is not a critical error in production, we can continue
            // executing with the current database while someone
            // investigates
            LOG_ERROR(
                "Unable to save block_number {} for {} error={}",
                block_number,
                db_type(),
                s.error());
        }

        // kill in debug
        MONAD_DEBUG_ASSERT(s.has_value());
    }

    [[nodiscard]] bytes32_t state_root()
    {
        return accounts_trie.trie.root_hash();
    }

    [[nodiscard]] bytes32_t storage_root(address_t const &a)
    {
        storage_trie.trie.set_trie_prefix(a);
        return storage_trie.trie.root_hash();
    }
};

MONAD_DB_NAMESPACE_END

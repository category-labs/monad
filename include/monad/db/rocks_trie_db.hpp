#pragma once

#include <monad/db/config.hpp>
#include <monad/db/create_and_prune_block_history.hpp>
#include <monad/db/prepare_state.hpp>
#include <monad/db/trie_db_interface.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/rocks_cursor.hpp>
#include <monad/trie/rocks_writer.hpp>
#include <monad/trie/trie.hpp>

#include <fmt/chrono.h>
#include <fmt/format.h>

#include <filesystem>

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    // Database impl with trie root generating logic, backed by rocksdb
    template <typename TExecutor>
    struct RocksTrieDB
        : public TrieDBInterface<RocksTrieDB<TExecutor>, TExecutor>
    {
        using base_t = TrieDBInterface<RocksTrieDB<TExecutor>, TExecutor>;

        struct Trie
        {
            trie::RocksCursor leaves_cursor;
            trie::RocksCursor trie_cursor;
            trie::RocksWriter leaves_writer;
            trie::RocksWriter trie_writer;

            trie::Trie<trie::RocksCursor, trie::RocksWriter> trie;

            Trie(
                std::shared_ptr<rocksdb::DB> db,
                rocksdb::ColumnFamilyHandle *lc,
                rocksdb::ColumnFamilyHandle *tc)
                : leaves_cursor(db, lc)
                , trie_cursor(db, tc)
                , leaves_writer(trie::RocksWriter{
                      .db = db, .batch = rocksdb::WriteBatch{}, .cf = lc})
                , trie_writer(trie::RocksWriter{
                      .db = db, .batch = rocksdb::WriteBatch{}, .cf = tc})
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
        uint64_t const block_history_size;
        rocksdb::Options options;
        trie::PathComparator accounts_comparator;
        trie::PrefixPathComparator storage_comparator;
        std::vector<rocksdb::ColumnFamilyDescriptor> cfds;
        std::vector<rocksdb::ColumnFamilyHandle *> cfs;
        std::shared_ptr<rocksdb::DB> db;
        Trie accounts_trie;
        Trie storage_trie;

        RocksTrieDB(
            std::filesystem::path root, uint64_t block_number,
            uint64_t block_history_size)
            : root(root)
            , block_history_size(block_history_size)
            , options([]() {
                rocksdb::Options ret;
                ret.IncreaseParallelism(2);
                ret.OptimizeLevelStyleCompaction();
                ret.create_if_missing = true;
                ret.create_missing_column_families = true;
                return ret;
            }())
            , accounts_comparator()
            , storage_comparator()
            , cfds([&]() -> decltype(cfds) {
                rocksdb::ColumnFamilyOptions accounts_opts;
                rocksdb::ColumnFamilyOptions storage_opts;
                accounts_opts.comparator = &accounts_comparator;
                storage_opts.comparator = &storage_comparator;

                return {
                    {rocksdb::kDefaultColumnFamilyName, {}},
                    {"AccountTrieLeaves", accounts_opts},
                    {"AccountTrieAll", accounts_opts},
                    {"StorageTrieLeaves", storage_opts},
                    {"StorageTrieAll", storage_opts}};
            }())
            , cfs()
            , db([&]() {
                rocksdb::DB *db = nullptr;

                auto const path = prepare_state(*this, block_number);
                if (!path.has_value()) {
                    throw std::runtime_error(path.error());
                }
                rocksdb::Status const s =
                    rocksdb::DB::Open(options, path.value(), cfds, &cfs, &db);

                MONAD_ROCKS_ASSERT(s);
                MONAD_ASSERT(cfds.size() == cfs.size());

                return db;
            }())
            , accounts_trie(db, cfs[1], cfs[2])
            , storage_trie(db, cfs[3], cfs[4])
        {
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
        // DBInterface implementations
        ////////////////////////////////////////////////////////////////////

        void create_and_prune_block_history(uint64_t block_number)
        {
            auto const s = ::monad::db::create_and_prune_block_history(
                *this, block_number);
            if (!s.has_value()) {
                // this is not a critical error in production, we can continue
                // executing with the current database while someone
                // investigates
                MONAD_LOG_ERROR(
                    base_t::logger,
                    "Unable to save block_number {} for {} error={}",
                    block_number,
                    as_string<RocksTrieDB>(),
                    s.error());
            }

            // kill in debug
            MONAD_DEBUG_ASSERT(s.has_value());
        }

        void commit(state::changeset auto const &obj)
        {
            base_t::commit(obj);
            accounts_trie.reset_cursor();
            storage_trie.reset_cursor();
        }

        ////////////////////////////////////////////////////////////////////
        // TrieDBInterface implementations
        ////////////////////////////////////////////////////////////////////

        auto &accounts() { return accounts_trie; }
        auto &storage() { return storage_trie; }
        auto const &accounts() const { return accounts_trie; }
        auto const &storage() const { return storage_trie; }
    };
};

using RocksTrieDB = detail::RocksTrieDB<monad::execution::BoostFiberExecution>;

MONAD_DB_NAMESPACE_END

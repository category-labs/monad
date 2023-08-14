#pragma once

#include <monad/db/auto_detect_start_block_number.hpp>
#include <monad/db/config.hpp>
#include <monad/db/create_and_prune_block_history.hpp>
#include <monad/db/prepare_state.hpp>
#include <monad/db/rocks_db_helper.hpp>
#include <monad/db/trie_db_interface.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/rocks_cursor.hpp>
#include <monad/trie/rocks_writer.hpp>
#include <monad/trie/trie.hpp>

#include <quill/bundled/fmt/chrono.h>
#include <quill/bundled/fmt/format.h>

#include <filesystem>

namespace fmt = fmtquill::v10;

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    // Database impl with trie root generating logic, backed by rocksdb
    template <typename TExecutor, Permission TPermission>
    struct RocksTrieDB
        : public TrieDBInterface<
              RocksTrieDB<TExecutor, TPermission>, TExecutor, TPermission>
    {
        using this_t = RocksTrieDB<TExecutor, TPermission>;
        using base_t = TrieDBInterface<this_t, TExecutor, TPermission>;

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

        uint64_t const starting_block_number;
        rocksdb::Options options;
        trie::PathComparator accounts_comparator;
        trie::PrefixPathComparator storage_comparator;
        std::vector<rocksdb::ColumnFamilyDescriptor> cfds;
        std::vector<rocksdb::ColumnFamilyHandle *> cfs;
        std::shared_ptr<rocksdb::DB> db;
        Trie accounts_trie;
        Trie storage_trie;

        struct Empty
        {
        };
        using block_history_size_t =
            std::conditional_t<Writable<TPermission>, uint64_t, Empty>;
        using batch_t = std::conditional_t<
            Writable<TPermission>, rocksdb::WriteBatch, Empty>;

        [[no_unique_address]] block_history_size_t const block_history_size;
        [[no_unique_address]] batch_t batch;

        ////////////////////////////////////////////////////////////////////
        // Constructor & Destructor
        ////////////////////////////////////////////////////////////////////

        RocksTrieDB(std::filesystem::path root, uint64_t block_history_size)
            requires Writable<TPermission>
            : RocksTrieDB(
                  root, auto_detect_start_block_number(root),
                  block_history_size)
        {
        }

        RocksTrieDB(
            std::filesystem::path root, uint64_t const starting_block_number)
            requires(!Writable<TPermission>)
            : RocksTrieDB(root, starting_block_number, Empty{})
        {
        }

        RocksTrieDB(
            std::filesystem::path root, uint64_t const starting_block_number,
            block_history_size_t block_history_size)
            requires Readable<TPermission>
            : root(root)
            , starting_block_number(starting_block_number)
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
                    {"StorageTrieAll", storage_opts},
                    {"Code", {}}};
            }())
            , cfs()
            , db([&]() {
                rocksdb::DB *db = nullptr;

                auto const path = [&]() {
                    if constexpr (Writable<TPermission>) {
                        return prepare_state<
                            RocksTrieDB,
                            TExecutor,
                            TPermission>(root, starting_block_number);
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
            , accounts_trie(db, cfs[1], cfs[2])
            , storage_trie(db, cfs[3], cfs[4])
            , block_history_size(block_history_size)
            , batch()

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
        // Helper functions
        ////////////////////////////////////////////////////////////////////

        [[nodiscard]] constexpr auto *code_cf() { return cfs[5]; }

        ////////////////////////////////////////////////////////////////////
        // DBInterface implementations
        ////////////////////////////////////////////////////////////////////

        void create_and_prune_block_history(uint64_t block_number)
            requires Writable<TPermission>
        {
            auto const s = ::monad::db::create_and_prune_block_history(
                root, db, block_number, block_history_size);
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

        [[nodiscard]] bool contains_impl(bytes32_t const &ch)
        {
            return rocks_db_contains_impl(ch, db, code_cf());
        }

        [[nodiscard]] byte_string try_find_impl(bytes32_t const &ch)
        {
            return rocks_db_try_find_impl(ch, db, code_cf());
        }

        void commit(state::changeset auto const &obj)
            requires Writable<TPermission>
        {
            commit_code_to_rocks_db_batch(batch, obj, code_cf());
            rocksdb::WriteOptions options;
            options.disableWAL = true;
            db->Write(options, &batch);
            batch.Clear();

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

using RocksTrieDB =
    detail::RocksTrieDB<monad::execution::BoostFiberExecution, ReadWrite>;
using ReadOnlyRocksTrieDB =
    detail::RocksTrieDB<monad::execution::BoostFiberExecution, ReadOnly>;

MONAD_DB_NAMESPACE_END

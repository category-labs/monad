#pragma once

#include <monad/db/config.hpp>
#include <monad/db/trie_db_interface.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/rocks_cursor.hpp>
#include <monad/trie/rocks_writer.hpp>
#include <monad/trie/trie.hpp>

#include <fmt/chrono.h>
#include <fmt/format.h>

MONAD_DB_NAMESPACE_BEGIN

// Database impl with trie root generating logic, backed by rocksdb
struct RocksTrieDB : TrieDBInterface<RocksTrieDB>
{
    struct Trie
    {
        trie::RocksCursor leaves_cursor;
        trie::RocksCursor trie_cursor;
        trie::RocksWriter leaves_writer;
        trie::RocksWriter trie_writer;

        trie::Trie<trie::RocksCursor, trie::RocksWriter> trie;

        Trie(
            std::shared_ptr<rocksdb::DB> db, rocksdb::ColumnFamilyHandle *lc,
            rocksdb::ColumnFamilyHandle *tc, rocksdb::Snapshot const *snapshot)
            : leaves_cursor(db, lc, snapshot)
            , trie_cursor(db, tc, snapshot)
            , leaves_writer(trie::RocksWriter{
                  .db = db, .batch = rocksdb::WriteBatch{}, .cf = lc})
            , trie_writer(trie::RocksWriter{
                  .db = db, .batch = rocksdb::WriteBatch{}, .cf = tc})
            , trie(leaves_cursor, trie_cursor, leaves_writer, trie_writer)
        {
        }

        void set_snapshot(rocksdb::Snapshot const *snapshot)
        {
            leaves_cursor.set_snapshot(snapshot);
            trie_cursor.set_snapshot(snapshot);
        }

        void reset_cursor()
        {
            leaves_cursor.reset();
            trie_cursor.reset();
        }

        [[nodiscard]] trie::RocksCursor make_leaf_cursor() const
        {
            return trie::RocksCursor{
                leaves_cursor.db_,
                leaves_cursor.cf_,
                leaves_cursor.read_opts_.snapshot};
        }

        [[nodiscard]] trie::RocksCursor make_trie_cursor() const
        {
            return trie::RocksCursor{
                trie_cursor.db_,
                trie_cursor.cf_,
                trie_cursor.read_opts_.snapshot};
        }
    };

    std::filesystem::path const name;
    rocksdb::Options options;
    trie::PathComparator accounts_comparator;
    trie::PrefixPathComparator storage_comparator;
    std::vector<rocksdb::ColumnFamilyDescriptor> cfds;
    std::vector<rocksdb::ColumnFamilyHandle *> cfs;
    std::shared_ptr<rocksdb::DB> db;
    rocksdb::Snapshot const *snapshot;
    Trie accounts_trie;
    Trie storage_trie;

    RocksTrieDB(
        std::filesystem::path name = std::filesystem::absolute("rocks_trie_db"))
        : name(name)
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
        , snapshot(db->GetSnapshot())
        , accounts_trie(db, cfs[1], cfs[2], snapshot)
        , storage_trie(db, cfs[3], cfs[4], snapshot)
    {
    }

    ~RocksTrieDB()
    {
        accounts_trie.reset_cursor();
        storage_trie.reset_cursor();
        release_snapshot();

        rocksdb::Status res;
        for (auto *const cf : cfs) {
            res = db->DestroyColumnFamilyHandle(cf);
            MONAD_ASSERT(res.ok());
        }

        res = db->Close();
        MONAD_ROCKS_ASSERT(res);
    }

    ////////////////////////////////////////////////////////////////////
    // TrieDBInterface implementations
    ////////////////////////////////////////////////////////////////////

    auto &accounts() { return accounts_trie; }
    auto &storage() { return storage_trie; }
    auto const &accounts() const { return accounts_trie; }
    auto const &storage() const { return storage_trie; }

    void take_snapshot()
    {
        release_snapshot();
        snapshot = db->GetSnapshot();
        accounts_trie.set_snapshot(snapshot);
        storage_trie.set_snapshot(snapshot);
    }

    void release_snapshot()
    {
        MONAD_DEBUG_ASSERT(snapshot);
        db->ReleaseSnapshot(snapshot);
    }
};

MONAD_DB_NAMESPACE_END

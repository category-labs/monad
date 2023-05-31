#pragma once

#include "hard_updates.hpp"

#include <monad/trie/comparator.hpp>
#include <monad/trie/in_memory_cursor.hpp>
#include <monad/trie/in_memory_writer.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/rocks_cursor.hpp>
#include <monad/trie/rocks_writer.hpp>
#include <monad/trie/trie.hpp>

#include <gtest/gtest.h>
#include <rocksdb/db.h>

MONAD_TRIE_NAMESPACE_BEGIN

// TODO: these no longer compile due to interface changes. Fix when we
// decide to add in rocksdb support for trie building and would like
// unit tests to run with rocksdb.
//
// class rocks_fixture : public ::testing::Test
// {
// public:
//     std::filesystem::path const name_;
//     rocksdb::Options options_;
//     std::vector<rocksdb::ColumnFamilyDescriptor> cfds_;
//     std::vector<rocksdb::ColumnFamilyHandle *> cfs_;
//     PathComparator comparator_;
//     std::shared_ptr<rocksdb::DB> db_;
//     RocksCursor leaves_cursor_;
//     RocksCursor trie_cursor_;
//     RocksWriter writer_;
//
//     Trie<RocksCursor, RocksWriter> trie_;
//
//     rocks_fixture()
//         : name_(std::filesystem::absolute("rocksdb"))
//         , db_([&]() {
//             options_.IncreaseParallelism(2);
//             options_.OptimizeLevelStyleCompaction();
//             options_.create_if_missing = true;
//             options_.create_missing_column_families = true;
//
//             rocksdb::DB *db = nullptr;
//
//             rocksdb::ColumnFamilyOptions col_opts;
//             col_opts.comparator = &comparator_;
//
//             cfds_ = {
//                 {rocksdb::kDefaultColumnFamilyName, col_opts},
//                 {"AccountTrieLeaves", {}},
//                 {"AccountTrieAll", col_opts}};
//
//             rocksdb::Status const s =
//                 rocksdb::DB::Open(options_, name_, cfds_, &cfs_, &db);
//
//             if (!s.ok()) {
//                 std::cerr << s.ToString() << std::endl;
//                 MONAD_ASSERT(false);
//             }
//             MONAD_ASSERT(cfds_.size() == cfs_.size());
//
//             return db;
//         }())
//         , leaves_cursor_(db_, cfs_[1])
//         , trie_cursor_(db_, cfs_[2])
//         , writer_(RocksWriter{
//               .db = db_,
//               .batch = rocksdb::WriteBatch{},
//               .cfs = {cfs_[1], nullptr, cfs_[2], nullptr}})
//         , trie_(
//               leaves_cursor_, trie_cursor_, writer_,
//               WriterColumn::ACCOUNT_LEAVES, WriterColumn::ACCOUNT_TRIE)
//     {
//         EXPECT_TRUE(leaves_cursor_.empty());
//         EXPECT_TRUE(trie_cursor_.empty());
//     }
//
//     ~rocks_fixture()
//     {
//         leaves_cursor_.release_snapshots();
//         trie_cursor_.release_snapshots();
//
//         rocksdb::Status res;
//         for (auto *const cf : cfs_) {
//             res = db_->DestroyColumnFamilyHandle(cf);
//             MONAD_ASSERT(res.ok());
//         }
//
//         res = db_->Close();
//         MONAD_ASSERT(res.ok());
//
//         res = rocksdb::DestroyDB(name_, options_, cfds_);
//         MONAD_ASSERT(res.ok());
//     }
//
//     void process_updates(std::vector<Update> const &updates)
//     {
//         trie_.process_updates(updates);
//
//         writer_.write();
//         leaves_cursor_.take_snapshot();
//         trie_cursor_.take_snapshot();
//     }
// };
//
// class rocks_prefix_fixture : public ::testing::Test
// {
// public:
//     std::filesystem::path const name_;
//     rocksdb::Options options_;
//     std::vector<rocksdb::ColumnFamilyDescriptor> cfds_;
//     std::vector<rocksdb::ColumnFamilyHandle *> cfs_;
//     PrefixPathComparator comparator_;
//     std::shared_ptr<rocksdb::DB> db_;
//     RocksCursor leaves_cursor_;
//     RocksCursor trie_cursor_;
//     RocksWriter writer_;
//
//     Trie<RocksCursor, RocksWriter> trie_;
//
//     std::vector<Update> const hard_updates_only_upserts_;
//
//     rocks_prefix_fixture()
//         : name_(std::filesystem::absolute("rocksdb"))
//         , db_([&]() {
//             options_.IncreaseParallelism(2);
//             options_.OptimizeLevelStyleCompaction();
//             options_.create_if_missing = true;
//             options_.create_missing_column_families = true;
//
//             rocksdb::DB *db = nullptr;
//
//             rocksdb::ColumnFamilyOptions col_opts;
//             col_opts.comparator = &comparator_;
//
//             cfds_ = {
//                 {rocksdb::kDefaultColumnFamilyName, col_opts},
//                 {"StorageTrieLeaves", col_opts},
//                 {"StorageTrieAll", col_opts}};
//
//             rocksdb::Status const s =
//                 rocksdb::DB::Open(options_, name_, cfds_, &cfs_, &db);
//
//             if (!s.ok()) {
//                 std::cerr << s.ToString() << std::endl;
//                 MONAD_ASSERT(false);
//             }
//             MONAD_ASSERT(cfds_.size() == cfs_.size());
//
//             return db;
//         }())
//         , leaves_cursor_(db_, cfs_[1])
//         , trie_cursor_(db_, cfs_[2])
//         , writer_(RocksWriter{
//               .db = db_,
//               .batch = rocksdb::WriteBatch{},
//               .cfs = {nullptr, cfs_[1], nullptr, cfs_[2]}})
//         , trie_(
//               leaves_cursor_, trie_cursor_, writer_,
//               WriterColumn::STORAGE_LEAVES, WriterColumn::STORAGE_TRIE)
//     {
//         EXPECT_TRUE(leaves_cursor_.empty());
//         EXPECT_TRUE(trie_cursor_.empty());
//     }
//
//     ~rocks_prefix_fixture()
//     {
//         leaves_cursor_.release_snapshots();
//         trie_cursor_.release_snapshots();
//
//         rocksdb::Status res;
//         for (auto *const cf : cfs_) {
//             res = db_->DestroyColumnFamilyHandle(cf);
//             MONAD_ASSERT(res.ok());
//         }
//
//         res = db_->Close();
//         MONAD_ASSERT(res.ok());
//
//         res = rocksdb::DestroyDB(name_, options_, cfds_);
//         MONAD_ASSERT(res.ok());
//     }
//
//     void process_updates(std::vector<Update> const &updates)
//     {
//         trie_.process_updates(updates);
//
//         writer_.write();
//         leaves_cursor_.take_snapshot();
//         trie_cursor_.take_snapshot();
//     }
// };

template <comparator TComparator>
struct in_memory_fixture : public ::testing::Test
{
    using cursor_t = InMemoryCursor<TComparator>;
    using writer_t = InMemoryWriter<TComparator>;
    using trie_t = Trie<cursor_t, writer_t>;

    std::vector<std::pair<byte_string, byte_string>> leaves_storage_;
    std::vector<std::pair<byte_string, byte_string>> trie_storage_;
    cursor_t leaves_cursor_;
    cursor_t trie_cursor_;
    writer_t leaves_writer_;
    writer_t trie_writer_;
    trie_t trie_;

    in_memory_fixture()
        : leaves_cursor_(leaves_storage_)
        , trie_cursor_(trie_storage_)
        , leaves_writer_(leaves_storage_)
        , trie_writer_(trie_storage_)
        , trie_(leaves_cursor_, trie_cursor_, leaves_writer_, trie_writer_)
    {
    }

    void flush()
    {
        leaves_writer_.write();
        trie_writer_.write();
        leaves_cursor_.take_snapshot();
        trie_cursor_.take_snapshot();
    }

    void process_updates(std::vector<Update> const &updates)
    {
        trie_.process_updates(updates);
        flush();
    }

    void clear()
    {
        trie_.clear();
        flush();
    }

    bool storage_empty() const
    {
        return leaves_storage_.empty() && trie_storage_.empty();
    }

    void print_trie_storage() const
    {
        auto const pretty = [](byte_string const &bytes) {
            std::ostringstream oss;
            oss << "0x";
            for (auto b : bytes) {
                oss << std::setw(2) << std::setfill('0') << std::hex << int(b);
            }
            return oss.str();
        };

        for (auto const &[key, val] : trie_storage_) {
            std::cout << pretty(key) << " " << pretty(val) << std::endl;
        }
    }
};

MONAD_TRIE_NAMESPACE_END

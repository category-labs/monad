#pragma once

#include <monad/test/make_db.hpp>
#include <monad/test/one_hundred_updates.hpp>
#include <monad/trie/comparator.hpp>
#include <monad/trie/in_memory_cursor.hpp>
#include <monad/trie/in_memory_writer.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/rocks_cursor.hpp>
#include <monad/trie/rocks_writer.hpp>
#include <monad/trie/trie.hpp>

#include <filesystem>
#include <fmt/chrono.h>
#include <fmt/format.h>
#include <gtest/gtest.h>
#include <rocksdb/db.h>

MONAD_TEST_NAMESPACE_BEGIN

template <typename TComparator>
struct rocks_fixture : public ::testing::Test
{
    rocksdb::Options options_;
    TComparator comparator_;
    std::vector<rocksdb::ColumnFamilyDescriptor> cfds_;
    std::vector<rocksdb::ColumnFamilyHandle *> cfs_;
    std::shared_ptr<rocksdb::DB> db_;
    rocksdb::Snapshot const *snapshot_;

    monad::trie::RocksCursor leaves_cursor_;
    monad::trie::RocksCursor trie_cursor_;
    monad::trie::RocksWriter leaves_writer_;
    monad::trie::RocksWriter trie_writer_;

    monad::trie::Trie<monad::trie::RocksCursor, monad::trie::RocksWriter> trie_;

    rocks_fixture()
        : options_([]() {
            rocksdb::Options ret;
            ret.IncreaseParallelism(2);
            ret.OptimizeLevelStyleCompaction();
            ret.create_if_missing = true;
            ret.create_missing_column_families = true;
            return ret;
        }())
        , comparator_()
        , cfds_([&]() -> decltype(cfds_) {
            rocksdb::ColumnFamilyOptions col_opts;
            col_opts.comparator = &comparator_;

            return {
                {rocksdb::kDefaultColumnFamilyName, col_opts},
                {"monad::trie::TrieLeaves", {}},
                {"monad::trie::TrieAll", col_opts}};
        }())
        , cfs_()
        , db_([&]() {
            rocksdb::DB *db = nullptr;

            auto const *info =
                testing::UnitTest::GetInstance()->current_test_info();
            MONAD_ASSERT(info);

            rocksdb::Status const s = rocksdb::DB::Open(
                options_, test::make_db_name(*info), cfds_, &cfs_, &db);

            if (!s.ok()) {
                std::cerr << s.ToString() << std::endl;
                MONAD_ASSERT(false);
            }
            MONAD_ASSERT(cfds_.size() == cfs_.size());

            return db;
        }())
        , snapshot_(db_->GetSnapshot())
        , leaves_cursor_(db_, cfs_[1], snapshot_)
        , trie_cursor_(db_, cfs_[2], snapshot_)
        , leaves_writer_(monad::trie::RocksWriter{
              .db = db_, .batch = rocksdb::WriteBatch{}, .cf = cfs_[1]})
        , trie_writer_(monad::trie::RocksWriter{
              .db = db_, .batch = rocksdb::WriteBatch{}, .cf = cfs_[2]})
        , trie_(leaves_cursor_, trie_cursor_, leaves_writer_, trie_writer_)
    {
        EXPECT_TRUE(leaves_cursor_.empty());
        EXPECT_TRUE(trie_cursor_.empty());
    }

    ~rocks_fixture()
    {
        leaves_cursor_.reset();
        trie_cursor_.reset();
        release_snapshot();

        rocksdb::Status res;
        for (auto *const cf : cfs_) {
            res = db_->DestroyColumnFamilyHandle(cf);
            MONAD_ASSERT(res.ok());
        }

        res = db_->Close();
        MONAD_ASSERT(res.ok());
    }

    void take_snapshot()
    {
        release_snapshot();
        snapshot_ = db_->GetSnapshot();
        leaves_cursor_.set_snapshot(snapshot_);
        trie_cursor_.set_snapshot(snapshot_);
    }

    void release_snapshot()
    {
        MONAD_DEBUG_ASSERT(snapshot_);
        db_->ReleaseSnapshot(snapshot_);
    }

    void process_updates(std::vector<monad::trie::Update> const &updates)
    {
        trie_.process_updates(updates);

        flush();
    }

    void flush()
    {
        leaves_writer_.write();
        trie_writer_.write();
        take_snapshot();
    }

    void clear()
    {
        trie_.clear();
        flush();
    }

    bool storage_empty() const
    {
        std::unique_ptr<rocksdb::Iterator> leaves(
            db_->NewIterator({}, cfs_[1]));
        std::unique_ptr<rocksdb::Iterator> trie(db_->NewIterator({}, cfs_[2]));
        leaves->SeekToFirst();
        trie->SeekToFirst();
        return !leaves->Valid() && !trie->Valid();
    }
};

template <typename TComparator>
struct in_memory_fixture : public ::testing::Test
{
    using cursor_t = monad::trie::InMemoryCursor<TComparator>;
    using writer_t = monad::trie::InMemoryWriter<TComparator>;
    using trie_t = monad::trie::Trie<cursor_t, writer_t>;

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
    }

    void process_updates(std::vector<monad::trie::Update> const &updates)
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
};

[[nodiscard]] constexpr monad::trie::Update
make_upsert(monad::trie::Nibbles const &key, byte_string const &value)
{
    return monad::trie::Upsert{
        .key = key,
        .value = value,
    };
}

[[nodiscard]] constexpr monad::trie::Update
make_upsert(bytes32_t key, byte_string const &value)
{
    return make_upsert(monad::trie::Nibbles(key), value);
}

[[nodiscard]] inline monad::trie::Update
make_upsert(bytes32_t const &key, bytes32_t const &value)
{
    return make_upsert(
        monad::trie::Nibbles(key),
        byte_string(
            reinterpret_cast<byte_string::value_type const *>(&value.bytes),
            sizeof(value.bytes)));
}

[[nodiscard]] constexpr monad::trie::Update
make_del(monad::trie::Nibbles const &key)
{
    return monad::trie::Delete{
        .key = key,
    };
}

[[nodiscard]] constexpr monad::trie::Update make_del(evmc::bytes32 key)
{
    return make_del(monad::trie::Nibbles(key));
}

[[nodiscard]] constexpr std::vector<monad::trie::Update>
make_updates(std::ranges::range auto const &updates)
{
    std::vector<monad::trie::Update> ret;
    for (auto const &[key, value] : updates) {
        ret.emplace_back(make_upsert(key, value));
    }
    return ret;
}

MONAD_TEST_NAMESPACE_END

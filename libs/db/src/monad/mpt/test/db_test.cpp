#include "test_fixtures_base.hpp"

#include <gtest/gtest.h>

#include <monad/async/config.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/util.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/core/result.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/db_error.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/operations.hpp>

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <initializer_list>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <thread>
#include <type_traits>
#include <utility>
#include <vector>

#include <stdlib.h>
#include <unistd.h>

using namespace monad::mpt;
using namespace monad::test;

namespace
{
    constexpr unsigned DBTEST_HISTORY_LENGTH = 1000;

    template <class... Updates>
    void upsert_updates_flat_list(
        Db &db, NibblesView prefix, uint64_t const block_id, Updates... updates)
    {
        UpdateList ul;
        (ul.push_front(updates), ...);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);

        db.upsert(std::move(ul_prefix), block_id);
    };

    struct InMemoryDbFixture : public ::testing::Test
    {
        StateMachineAlwaysMerkle machine;
        Db db{machine};
    };

    struct OnDiskDbFixture : public ::testing::Test
    {
        StateMachineAlwaysMerkle machine;
        Db db{machine, OnDiskDbConfig{.history_length = DBTEST_HISTORY_LENGTH}};
    };

    struct OnDiskDbWithFileFixture : public ::testing::Test
    {
        std::filesystem::path const dbname;
        StateMachineAlwaysMerkle machine;
        OnDiskDbConfig config;
        Db db;

        OnDiskDbWithFileFixture()
            : dbname{[] {
                std::filesystem::path ret(
                    MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                    "monad_db_test_XXXXXX");
                int const fd = ::mkstemp((char *)ret.native().data());
                MONAD_ASSERT(fd != -1);
                MONAD_ASSERT(
                    -1 !=
                    ::ftruncate(
                        fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
                ::close(fd);
                return ret;
            }()}
            , machine{StateMachineAlwaysMerkle{}}
            , config{OnDiskDbConfig{
                  .dbname_paths = {dbname},
                  .history_length = DBTEST_HISTORY_LENGTH}}
            , db{machine, config}
        {
        }

        ~OnDiskDbWithFileFixture()
        {
            std::filesystem::remove(dbname);
        }
    };

    struct OnDiskDbWithFileAsyncFixture : public OnDiskDbWithFileFixture
    {
        using result_t = monad::Result<monad::byte_string>;

        Db ro_db;
        AsyncContextUniquePtr ctx;
        std::atomic<size_t> cbs{0}; // callbacks when found

        OnDiskDbWithFileAsyncFixture()
            : ro_db([&] {
                ReadOnlyOnDiskDbConfig const ro_config{
                    .dbname_paths = this->config.dbname_paths};
                return Db{ro_config};
            }())
            , ctx(async_context_create(ro_db))
        {
        }

        void async_get(auto &&sender, std::function<void(result_t)> callback)
        {
            using sender_type = std::decay_t<decltype(sender)>;

            struct receiver_t
            {
                OnDiskDbWithFileAsyncFixture *parent;
                std::function<void(result_t)> callback;

                void set_value(
                    monad::async::erased_connected_operation *state,
                    sender_type::result_type res)
                {
                    ++parent->cbs;
                    callback(std::move(res));
                    delete state;
                }
            };

            auto *state = new auto(monad::async::connect(
                std::move(sender), receiver_t{this, std::move(callback)}));
            state->initiate();
        }

        void poll_until(size_t num_callbacks)
        {
            while (cbs < num_callbacks) {
                ro_db.poll(false);
                std::this_thread::sleep_for(std::chrono::microseconds(50));
            }
        }
    };

    template <typename DbBase>
    struct DbTraverseFixture : public DbBase

    {
        uint64_t const block_id{0x123};
        monad::byte_string const prefix{0x00_hex};

        using DbBase::db;

        DbTraverseFixture()
            : DbBase()
        {
            auto const k1 = 0x12345678_hex;
            auto const v1 = 0xcafebabe_hex;
            auto const k2 = 0x12346678_hex;
            auto const v2 = 0xdeadbeef_hex;
            auto const k3 = 0x12445678_hex;
            auto const v3 = 0xdeadbabe_hex;
            auto u1 = make_update(k1, v1);
            auto u2 = make_update(k2, v2);
            auto u3 = make_update(k3, v3);
            UpdateList ul;
            ul.push_front(u1);
            ul.push_front(u2);
            ul.push_front(u3);

            auto u_prefix = Update{
                .key = prefix,
                .value = monad::byte_string_view{},
                .incarnation = false,
                .next = std::move(ul)};

            UpdateList ul_prefix;
            ul_prefix.push_front(u_prefix);
            this->db.upsert(std::move(ul_prefix), block_id);

            /*
                    00
                    |
                    12
                  /    \
                 34      445678
                / \
             5678  6678
            */
        }
    };

    struct DummyTraverseMachine : public TraverseMachine
    {
        Nibbles path{};

        virtual bool down(unsigned char branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                return true;
            }
            path = concat(NibblesView{path}, branch, node.path_nibble_view());

            if (node.has_value()) {
                EXPECT_EQ(path.nibble_size(), KECCAK256_SIZE * 2);
            }
            return true;
        }

        virtual void up(unsigned char branch, Node const &node) override
        {
            auto const path_view = NibblesView{path};
            auto const rem_size = [&] {
                if (branch == INVALID_BRANCH) {
                    MONAD_ASSERT(path_view.nibble_size() == 0);
                    return 0;
                }
                int const rem_size = path_view.nibble_size() - 1 -
                                     node.path_nibble_view().nibble_size();
                MONAD_ASSERT(rem_size >= 0);
                MONAD_ASSERT(
                    path_view.substr(static_cast<unsigned>(rem_size)) ==
                    concat(branch, node.path_nibble_view()));
                return rem_size;
            }();
            path = path_view.substr(0, static_cast<unsigned>(rem_size));
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<DummyTraverseMachine>(*this);
        }
    };

    std::pair<std::vector<monad::byte_string>, std::vector<Update>>
    prepare_random_updates(unsigned size)
    {
        std::vector<monad::byte_string> bytes_alloc;
        std::vector<Update> updates_alloc;
        for (size_t i = 0; i < size; ++i) {
            monad::byte_string kv(KECCAK256_SIZE, 0);
            MONAD_ASSERT(kv.size() == KECCAK256_SIZE);
            keccak256((unsigned char const *)&i, 8, kv.data());
            bytes_alloc.emplace_back(kv);
            updates_alloc.push_back(Update{
                .key = bytes_alloc.back(),
                .value = bytes_alloc.back(),
                .incarnation = false,
                .next = UpdateList{}});
        }
        return std::make_pair(std::move(bytes_alloc), std::move(updates_alloc));
    }
}

template <typename TFixture>
struct DbTest : public TFixture
{
};

using DbTypes = ::testing::Types<InMemoryDbFixture, OnDiskDbFixture>;
TYPED_TEST_SUITE(DbTest, DbTypes);

TEST_F(OnDiskDbWithFileFixture, read_only_db_single_thread)
{
    auto const &kv = fixed_updates::kv;

    auto const prefix = 0x00_hex;
    uint64_t const first_block_id = 0x123;
    uint64_t const second_block_id = first_block_id + 1;

    {
        auto u1 = make_update(kv[0].first, kv[0].second);
        auto u2 = make_update(kv[1].first, kv[1].second);
        UpdateList ul;
        ul.push_front(u1);
        ul.push_front(u2);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);

        this->db.upsert(std::move(ul_prefix), first_block_id);
    }

    // Verify RW
    EXPECT_EQ(
        this->db.get(prefix + kv[0].first, first_block_id).value(),
        kv[0].second);
    EXPECT_EQ(
        this->db.get(prefix + kv[1].first, first_block_id).value(),
        kv[1].second);
    EXPECT_EQ(
        this->db.get_data(prefix, first_block_id).value(),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);

    ReadOnlyOnDiskDbConfig const ro_config{
        .dbname_paths = this->config.dbname_paths};
    Db ro_db{ro_config};

    // Verify RO
    EXPECT_EQ(
        ro_db.get(prefix + kv[0].first, first_block_id).value(), kv[0].second);
    EXPECT_EQ(
        ro_db.get(prefix + kv[1].first, first_block_id).value(), kv[1].second);
    EXPECT_EQ(
        ro_db.get_data(prefix, first_block_id).value(),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);

    {
        auto u1 = make_update(kv[2].first, kv[2].second);
        auto u2 = make_update(kv[3].first, kv[3].second);
        UpdateList ul;
        ul.push_front(u1);
        ul.push_front(u2);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);

        this->db.upsert(std::move(ul_prefix), second_block_id);
    }

    // Verify RW database can read new data
    EXPECT_EQ(
        this->db.get(prefix + kv[2].first, second_block_id).value(),
        kv[2].second);
    EXPECT_EQ(
        this->db.get(prefix + kv[3].first, second_block_id).value(),
        kv[3].second);
    EXPECT_EQ(
        this->db.get_data(prefix, second_block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);

    // Verify RO database can read new data
    EXPECT_EQ(
        ro_db.get(prefix + kv[2].first, second_block_id).value(), kv[2].second);
    EXPECT_EQ(
        ro_db.get(prefix + kv[3].first, second_block_id).value(), kv[3].second);
    EXPECT_EQ(
        ro_db.get_data(prefix, second_block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);

    // Can still read data at previous block id
    EXPECT_EQ(
        ro_db.get(prefix + kv[0].first, first_block_id).value(), kv[0].second);
    EXPECT_EQ(
        ro_db.get(prefix + kv[1].first, first_block_id).value(), kv[1].second);
    EXPECT_EQ(
        ro_db.get_data(prefix, first_block_id).value(),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);
}

TEST_F(OnDiskDbWithFileAsyncFixture, read_only_db_single_thread_async)
{
    auto const &kv = fixed_updates::kv;

    auto const prefix = 0x00_hex;
    uint64_t const starting_block_id = 0x0;

    upsert_updates_flat_list(
        db,
        prefix,
        starting_block_id,
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second));

    constexpr uint8_t const test_cached_level = 1;
    size_t i;
    constexpr size_t read_per_iteration = 3;
    size_t const expected_num_success_callbacks =
        (ro_db.get_history_length() - 1) * read_per_iteration;
    for (i = 1; i < ro_db.get_history_length(); ++i) {
        // upsert new version
        upsert_updates_flat_list(
            db,
            prefix,
            starting_block_id + i,
            make_update(kv[2].first, kv[2].second),
            make_update(kv[3].first, kv[3].second));

        // ensure we can still async query the old version
        async_get(
            make_get_sender(
                ctx.get(),
                prefix + kv[0].first,
                starting_block_id,
                test_cached_level),
            [&](result_t res) {
                ASSERT_TRUE(res.has_value());
                EXPECT_EQ(res.value(), kv[0].second);
            });
        async_get(
            make_get_sender(
                ctx.get(),
                prefix + kv[1].first,
                starting_block_id,
                test_cached_level),
            [&](result_t res) {
                ASSERT_TRUE(res.has_value());
                EXPECT_EQ(res.value(), kv[1].second);
            });
        async_get(
            make_get_data_sender(
                ctx.get(), prefix, starting_block_id, test_cached_level),
            [&](result_t res) {
                ASSERT_TRUE(res.has_value());
                EXPECT_EQ(
                    res.value(),
                    0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);
            });
    }

    // Need to poll here because next read will trigger compaction
    poll_until(expected_num_success_callbacks);

    // This will exceed the ring buffer capacity, evicting the first block
    cbs = 0;
    upsert_updates_flat_list(
        db,
        prefix,
        starting_block_id + i,
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));

    async_get(
        make_get_sender(
            ctx.get(),
            prefix + kv[0].first,
            starting_block_id,
            test_cached_level),
        [&](result_t res) {
            EXPECT_TRUE(res.has_error());
            EXPECT_EQ(res.error(), DbError::key_not_found);
        });

    poll_until(1);
}

TEST_F(OnDiskDbWithFileAsyncFixture, async_rodb_level_based_cache_works)
{
    // Insert keys
    constexpr unsigned nkeys = 1000;
    auto [kv_alloc, updates_alloc] = prepare_random_updates(nkeys);
    uint64_t const version = 0;
    UpdateList ls;
    for (auto &u : updates_alloc) {
        ls.push_front(u);
    }
    db.upsert(std::move(ls), version);

    constexpr uint8_t test_cached_level = 3;

    // Do async reads
    for (auto const &kv : kv_alloc) {
        async_get(
            make_get_sender(ctx.get(), kv, version, test_cached_level),
            [&](result_t res) {
                EXPECT_TRUE(res.has_value());
                EXPECT_EQ(res.value(), kv);
            });
    }

    poll_until(nkeys);

    // Do an in memory traverse to verify all cached nodes are above
    // test_cached_level
    struct InMemoryTraverseMachine : public TraverseMachine
    {
        uint8_t const expected_cache_level{3};
        uint8_t curr_level{0};

        constexpr InMemoryTraverseMachine(uint8_t const expected_cache_level_)
            : expected_cache_level(expected_cache_level_)
        {
        }

        virtual bool down(unsigned char, Node const &) override
        {
            ++curr_level;
            return true;
        }

        virtual void up(unsigned char, Node const &) override
        {
            --curr_level;
        }

        virtual bool
        should_visit(Node const &node, unsigned char branch) override
        {
            bool next_is_in_memory =
                node.next(node.to_child_index(branch)) != nullptr;
            EXPECT_EQ(next_is_in_memory, curr_level <= expected_cache_level);
            return next_is_in_memory;
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<InMemoryTraverseMachine>(*this);
        }
    };

    InMemoryTraverseMachine traverse_machine{test_cached_level};
    AsyncContext::TrieRootCache::ConstAccessor acc;
    ASSERT_TRUE(ctx->root_cache.find(acc, version));
    auto root = acc->second->val;
    ro_db.traverse(NodeCursor{*root}, traverse_machine, version);
}

TEST(ReadOnlyDbTest, open_empty_rodb)
{
    std::filesystem::path const dbname{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_db_test_empty"};

    // construct RWDb, storage pool is set up but db remains empty
    StateMachineAlwaysMerkle machine{};
    OnDiskDbConfig const config{
        .compaction = true, .dbname_paths = {dbname}, .file_size_db = 8};
    Db const db{machine, config};

    // construct RODb
    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbname}};
    // RODb root is invalid
    Db const ro_db{ro_config};
    EXPECT_FALSE(ro_db.root().is_valid());
    EXPECT_EQ(ro_db.get_latest_block_id(), INVALID_BLOCK_ID);
    EXPECT_EQ(ro_db.get_earliest_block_id(), INVALID_BLOCK_ID);
    // RODb get() from any block will fail
    EXPECT_EQ(ro_db.get({}, 0).assume_error(), DbError::key_not_found);
}

TEST(ReadOnlyDbTest, read_only_db_concurrent)
{
    // Have one thread make forward progress by updating new versions and
    // erasing outdated ones. Meanwhile spwan a read thread that queries
    // historical states.
    std::atomic<bool> done{false};
    std::filesystem::path const dbname{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_db_test_concurrent"};

    auto const prefix = 0x00_hex;

    auto upsert_new_version = [&](Db &db, uint64_t const version) {
        UpdateList ul;
        auto version_bytes = serialize_as_big_endian<6>(version);
        auto u = make_update(version_bytes, version_bytes);
        ul.push_front(u);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = true,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);

        db.upsert(std::move(ul_prefix), version);
    };

    auto keep_query = [&]() {
        // construct RODb
        ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbname}};
        Db ro_db{ro_config};

        uint64_t read_version = 0;
        auto start_version_bytes = serialize_as_big_endian<6>(read_version);

        unsigned nsuccess = 0;
        unsigned nfailed = 0;

        while (ro_db.get_latest_block_id() == INVALID_BLOCK_ID &&
               !done.load(std::memory_order_acquire)) {
        }
        // now the first version is written to db
        ASSERT_TRUE(ro_db.get_latest_block_id() != INVALID_BLOCK_ID);
        ASSERT_TRUE(ro_db.get_earliest_block_id() != INVALID_BLOCK_ID);
        while (!done.load(std::memory_order_acquire)) {
            auto version_bytes = serialize_as_big_endian<6>(read_version);
            auto res = ro_db.get(prefix + version_bytes, read_version);
            if (res.has_value()) {
                ASSERT_EQ(res.value(), version_bytes) << "Corrupted database";
                ++nsuccess;
            }
            else {
                auto const min_block_id = ro_db.get_earliest_block_id();
                EXPECT_TRUE(min_block_id != INVALID_BLOCK_ID);
                read_version = min_block_id + 100;
                ++nfailed;
            }
        }
        std::cout << "Reader thread finished. Currently read till version "
                  << read_version << ". Did " << nsuccess << " successful and "
                  << nfailed << " failed reads" << std::endl;
        EXPECT_TRUE(nsuccess > 0);
        EXPECT_TRUE(read_version <= ro_db.get_latest_block_id());
        EXPECT_TRUE(read_version >= ro_db.get_earliest_block_id());
    };

    // construct RWDb
    uint64_t version = 0;
    StateMachineAlwaysMerkle machine{};
    OnDiskDbConfig const config{
        .compaction = true, .dbname_paths = {dbname}, .file_size_db = 8};
    Db db{machine, config};

    std::thread reader(keep_query);

    // run rodb and rwdb concurrently for 10s
    auto const begin_test = std::chrono::steady_clock::now();
    while (std::chrono::duration_cast<std::chrono::seconds>(
               std::chrono::steady_clock::now() - begin_test)
               .count() < 10) {
        upsert_new_version(db, version);
        ++version;
    }
    done.store(true, std::memory_order_release);
    reader.join();

    std::cout << "Writer finished. Max version in rwdb is "
              << db.get_latest_block_id() << ", min version in rwdb is "
              << db.get_earliest_block_id() << std::endl;
}

TEST(DbTest, read_only_db_traverse_concurrent)
{
    std::filesystem::path const dbname{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_db_test_traverse_concurrent"};
    StateMachineAlwaysMerkle machine{};
    OnDiskDbConfig config{// with compaction
                          .compaction = true,
                          .dbname_paths = {dbname},
                          .file_size_db = 8,
                          .history_length = DBTEST_HISTORY_LENGTH};
    Db db{machine, config};
    EXPECT_EQ(db.get_history_length(), DBTEST_HISTORY_LENGTH);
    auto [bytes_alloc, updates_alloc] = prepare_random_updates(20);

    uint64_t version = 0;
    auto upsert_once = [&] {
        UpdateList ls;
        for (auto &u : updates_alloc) {
            ls.push_front(u);
        }
        db.upsert(std::move(ls), version);
    };

    std::atomic<bool> done{false};

    std::thread writer([&]() {
        while (!done.load(std::memory_order_acquire)) {
            upsert_once();
            ++version;
        }
    });

    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbname}};
    Db ro_db{ro_config};
    EXPECT_EQ(ro_db.get_history_length(), DBTEST_HISTORY_LENGTH);
    DummyTraverseMachine traverse_machine;

    // read thread loop to traverse block 0 until it gets erased
    while (!ro_db.load_root_for_version(0).is_valid()) {
    } // first block data is written to db by writer thread
    auto const root_cursor = ro_db.load_root_for_version(0);
    ASSERT_TRUE(root_cursor.is_valid());
    while (ro_db.traverse(root_cursor, traverse_machine, 0)) {
    }

    done.store(true, std::memory_order_release);
    writer.join();
    EXPECT_TRUE(version >= ro_db.get_history_length())
        << "Version " << version << " should be gte"
        << ro_db.get_history_length();
}

TEST(DBTest, benchmark_blocking_parallel_traverse)
{
    std::filesystem::path const dbname{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_db_test_benchmark_traverse"};
    StateMachineAlwaysMerkle machine{};
    OnDiskDbConfig config{// with compaction
                          .compaction = true,
                          .sq_thread_cpu{std::nullopt},
                          .dbname_paths = {dbname},
                          .file_size_db = 8};
    Db db{machine, config};
    auto [bytes_alloc, updates_alloc] = prepare_random_updates(2000);
    UpdateList ls;
    for (auto &u : updates_alloc) {
        ls.push_front(u);
    }
    db.upsert(std::move(ls), 0);

    // benchmark traverse
    DummyTraverseMachine traverse_machine{};
    auto begin = std::chrono::steady_clock::now();
    ASSERT_TRUE(db.traverse(db.root(), traverse_machine, 0));
    auto end = std::chrono::steady_clock::now();
    auto const parallel_elapsed =
        std::chrono::duration_cast<std::chrono::microseconds>(end - begin)
            .count();
    std::cout << "RODb parallel traversal takes " << parallel_elapsed
              << " ms, ";

    begin = std::chrono::steady_clock::now();
    ASSERT_TRUE(db.traverse_blocking(db.root(), traverse_machine, 0));
    end = std::chrono::steady_clock::now();
    auto const blocking_elapsed =
        std::chrono::duration_cast<std::chrono::microseconds>(end - begin)
            .count();
    std::cout << "RWDb blocking traversal takes " << blocking_elapsed << " ms."
              << std::endl;

    EXPECT_TRUE(parallel_elapsed < blocking_elapsed);
}

TEST(ReadOnlyDbTest, load_correct_root_upon_reopen_nonempty_db)
{
    std::filesystem::path const dbname{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_db_test_reopen"};
    StateMachineAlwaysMerkle machine{};
    OnDiskDbConfig config{.dbname_paths = {dbname}, .file_size_db = 8};

    auto const &kv = fixed_updates::kv;
    auto const prefix = 0x00_hex;
    uint64_t const block_id = 0x123;

    {
        Db const db{machine, config};
        // db is init to empty
        EXPECT_FALSE(db.root().is_valid());
        EXPECT_EQ(db.get_latest_block_id(), INVALID_BLOCK_ID);

        Db const ro_db{ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
        EXPECT_FALSE(ro_db.root().is_valid());
        EXPECT_EQ(ro_db.get_latest_block_id(), INVALID_BLOCK_ID);
    }

    { // reopen the same db with append flag turned on
        config.append = true;
        Db db{machine, config};
        // db is still empty
        EXPECT_FALSE(db.root().is_valid());
        EXPECT_EQ(db.get_latest_block_id(), INVALID_BLOCK_ID);

        auto u1 = make_update(kv[2].first, kv[2].second);
        auto u2 = make_update(kv[3].first, kv[3].second);
        UpdateList ul;
        ul.push_front(u1);
        ul.push_front(u2);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);

        // db will have a valid root and root offset after this line
        db.upsert(std::move(ul_prefix), block_id);
    }

    { // reopen the same db again, this time we will have a valid root loaded
        config.append = true;
        Db const db{machine, config};
        EXPECT_TRUE(db.root().is_valid());
        EXPECT_EQ(db.get_latest_block_id(), block_id);
        EXPECT_EQ(db.get_earliest_block_id(), block_id);

        Db const ro_db{ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
        EXPECT_TRUE(db.root().is_valid());
        EXPECT_EQ(db.get_latest_block_id(), block_id);
        EXPECT_EQ(db.get_earliest_block_id(), block_id);
    }
}

TYPED_TEST(DbTest, simple_with_same_prefix)
{
    auto const &kv = fixed_updates::kv;

    auto const prefix = 0x00_hex;
    uint64_t const block_id = 0x123;

    {
        auto u1 = make_update(kv[0].first, kv[0].second);
        auto u2 = make_update(kv[1].first, kv[1].second);
        UpdateList ul;
        ul.push_front(u1);
        ul.push_front(u2);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);

        this->db.upsert(std::move(ul_prefix), block_id);
    }

    EXPECT_EQ(
        this->db.get(prefix + kv[0].first, block_id).value(), kv[0].second);
    EXPECT_EQ(
        this->db.get(prefix + kv[1].first, block_id).value(), kv[1].second);
    EXPECT_EQ(
        this->db.get_data(prefix, block_id).value(),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);

    {
        auto u1 = make_update(kv[2].first, kv[2].second);
        auto u2 = make_update(kv[3].first, kv[3].second);
        UpdateList ul;
        ul.push_front(u1);
        ul.push_front(u2);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);

        this->db.upsert(std::move(ul_prefix), block_id);
    }

    // test get with both apis
    EXPECT_EQ(
        this->db.get(prefix + kv[2].first, block_id).value(), kv[2].second);
    EXPECT_EQ(
        this->db.get(prefix + kv[3].first, block_id).value(), kv[3].second);
    EXPECT_EQ(
        this->db.get_data(prefix, block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);

    auto res = this->db.find(prefix, block_id);
    ASSERT_TRUE(res.has_value());
    NodeCursor const root_under_prefix = res.value();
    EXPECT_EQ(
        this->db.find(root_under_prefix, kv[2].first, block_id)
            .value()
            .node->value(),
        kv[2].second);
    EXPECT_EQ(
        this->db.find(root_under_prefix, kv[3].first, block_id)
            .value()
            .node->value(),
        kv[3].second);
    EXPECT_EQ(
        this->db.get_data(root_under_prefix, {}, block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
    EXPECT_EQ(
        this->db.get_data(this->db.root(), prefix, block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);

    EXPECT_FALSE(this->db.get(0x01_hex, block_id).has_value());
}

TYPED_TEST(DbTest, simple_with_increasing_block_id_prefix)
{
    auto const &kv = fixed_updates::kv;

    auto const prefix = 0x00_hex;
    uint64_t block_id = 0x123;

    upsert_updates_flat_list(
        this->db,
        prefix,
        block_id,
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second));
    EXPECT_EQ(
        this->db.get(prefix + kv[0].first, block_id).value(), kv[0].second);
    EXPECT_EQ(
        this->db.get(prefix + kv[1].first, block_id).value(), kv[1].second);
    EXPECT_EQ(
        this->db.get_data(prefix, block_id).value(),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);

    ++block_id;
    upsert_updates_flat_list(
        this->db,
        prefix,
        block_id,
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));

    // test get with both apis
    EXPECT_EQ(
        this->db.get(prefix + kv[2].first, block_id).value(), kv[2].second);
    EXPECT_EQ(
        this->db.get(prefix + kv[3].first, block_id).value(), kv[3].second);
    EXPECT_EQ(
        this->db.get_data(prefix, block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);

    auto res = this->db.find(NibblesView{prefix}, block_id);
    ASSERT_TRUE(res.has_value());
    NodeCursor const root_under_prefix = res.value();
    EXPECT_EQ(
        this->db.find(root_under_prefix, kv[2].first, block_id)
            .value()
            .node->value(),
        kv[2].second);
    EXPECT_EQ(
        this->db.find(root_under_prefix, kv[3].first, block_id)
            .value()
            .node->value(),
        kv[3].second);
    EXPECT_EQ(
        this->db.get_data(root_under_prefix, {}, block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
    EXPECT_EQ(
        this->db.get_data(this->db.root(), NibblesView{prefix}, block_id)
            .value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);

    EXPECT_FALSE(this->db.get(0x01_hex, block_id).has_value());
}

template <typename TFixture>
struct DbTraverseTest : public TFixture
{
};

using DbTraverseTypes = ::testing::Types<
    DbTraverseFixture<InMemoryDbFixture>, DbTraverseFixture<OnDiskDbFixture>>;
TYPED_TEST_SUITE(DbTraverseTest, DbTraverseTypes);

TYPED_TEST(DbTraverseTest, traverse)
{
    struct SimpleTraverse : public TraverseMachine
    {
        size_t &num_leaves;
        size_t index{0};
        size_t num_up{0};

        SimpleTraverse(size_t &num_leaves)
            : num_leaves(num_leaves)
        {
        }

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (node.has_value()) {
                ++num_leaves;
            }
            if (branch == INVALID_BRANCH) {
                EXPECT_EQ(node.number_of_children(), 1);
                EXPECT_EQ(node.mask, 0b10);
                EXPECT_TRUE(node.has_value());
                EXPECT_EQ(node.value(), monad::byte_string_view{});
                EXPECT_TRUE(node.has_path());
                EXPECT_EQ(node.path_nibble_view(), make_nibbles({0x0, 0x0}));
            }
            else if (branch == 1) {
                EXPECT_EQ(node.number_of_children(), 2);
                EXPECT_EQ(node.mask, 0b11000);
                EXPECT_FALSE(node.has_value());
                EXPECT_TRUE(node.has_path());
                EXPECT_EQ(node.path_nibble_view(), make_nibbles({0x2}));
            }
            else if (branch == 3) {
                EXPECT_EQ(node.number_of_children(), 2);
                EXPECT_EQ(node.mask, 0b1100000);
                EXPECT_FALSE(node.has_value());
                EXPECT_TRUE(node.has_path());
                EXPECT_EQ(node.path_nibble_view(), make_nibbles({0x4}));
            }
            else if (branch == 4) {
                EXPECT_EQ(node.number_of_children(), 0);
                EXPECT_EQ(node.mask, 0);
                EXPECT_TRUE(node.has_value());
                EXPECT_EQ(node.value(), 0xdeadbabe_hex);
                EXPECT_TRUE(node.has_path());
                EXPECT_EQ(
                    node.path_nibble_view(),
                    make_nibbles({0x4, 0x5, 0x6, 0x7, 0x8}));
            }
            else if (branch == 5) {
                EXPECT_EQ(node.number_of_children(), 0);
                EXPECT_EQ(node.mask, 0);
                EXPECT_TRUE(node.has_value());
                EXPECT_EQ(node.value(), 0xcafebabe_hex);
                EXPECT_TRUE(node.has_path());
                EXPECT_EQ(
                    node.path_nibble_view(), make_nibbles({0x6, 0x7, 0x8}));
            }
            else if (branch == 6) {
                EXPECT_EQ(node.number_of_children(), 0);
                EXPECT_EQ(node.mask, 0);
                EXPECT_TRUE(node.has_value());
                EXPECT_EQ(node.value(), 0xdeadbeef_hex);
                EXPECT_TRUE(node.has_path());
                EXPECT_EQ(
                    node.path_nibble_view(), make_nibbles({0x6, 0x7, 0x8}));
            }
            else {
                MONAD_ASSERT(false);
            }
            ++index;
            return true;
        }

        virtual void up(unsigned char const, Node const &) override
        {
            ++num_up;
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<SimpleTraverse>(*this);
        }

        Nibbles make_nibbles(std::initializer_list<uint8_t> nibbles)
        {
            Nibbles ret{nibbles.size()};
            for (auto const *it = nibbles.begin(); it < nibbles.end(); ++it) {
                MONAD_ASSERT(*it <= 0xf);
                ret.set(
                    static_cast<unsigned>(std::distance(nibbles.begin(), it)),
                    *it);
            }
            return ret;
        }
    };

    {
        size_t num_leaves = 0;
        SimpleTraverse traverse{num_leaves};
        ASSERT_TRUE(
            this->db.traverse(this->db.root(), traverse, this->block_id));
        EXPECT_EQ(num_leaves, 4);
    }

    {
        size_t num_leaves = 0;
        SimpleTraverse traverse{num_leaves};
        ASSERT_TRUE(this->db.traverse_blocking(
            this->db.root(), traverse, this->block_id));
        EXPECT_EQ(traverse.num_up, 6);
        EXPECT_EQ(num_leaves, 4);
    }
}

TYPED_TEST(DbTraverseTest, trimmed_traverse)
{
    // Trimmed traversal
    struct TrimmedTraverse : public TraverseMachine
    {
        size_t &num_leaves;

        TrimmedTraverse(size_t &num_leaves)
            : num_leaves(num_leaves)
        {
        }

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (node.path_nibbles_len() == 3 && branch == 5) {
                // trim one leaf
                return false;
            }
            if (node.has_value()) {
                ++num_leaves;
            }
            return true;
        }

        virtual void up(unsigned char const, Node const &) override {}

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<TrimmedTraverse>(*this);
        }

        virtual bool
        should_visit(Node const &, unsigned char const branch) override
        {
            // trim the right most leaf
            return branch != 4;
        }
    };

    auto res_cursor = this->db.find(this->prefix, this->block_id);
    ASSERT_TRUE(res_cursor.has_value());
    ASSERT_TRUE(res_cursor.value().is_valid());
    {
        size_t num_leaves = 0;
        TrimmedTraverse traverse{num_leaves};
        ASSERT_TRUE(
            this->db.traverse(res_cursor.value(), traverse, this->block_id));
        EXPECT_EQ(num_leaves, 2);
    }
    {
        size_t num_leaves = 0;
        TrimmedTraverse traverse{num_leaves};
        ASSERT_TRUE(this->db.traverse_blocking(
            res_cursor.value(), traverse, this->block_id));
        EXPECT_EQ(num_leaves, 2);
    }
}

TEST_F(OnDiskDbFixture, rw_query_old_version)
{
    auto const &kv = fixed_updates::kv;

    auto const prefix = 0x00_hex;
    uint64_t const block_id = 0;

    auto write = [&](monad::byte_string_view k,
                     monad::byte_string_view v,
                     uint64_t const upsert_block_id) {
        auto u = make_update(k, v);
        UpdateList ul;
        ul.push_front(u);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);

        this->db.upsert(std::move(ul_prefix), upsert_block_id);
    };

    // Write first block_id
    write(kv[0].first, kv[0].second, block_id);
    EXPECT_EQ(
        this->db.get(prefix + kv[0].first, block_id).value(), kv[0].second);

    size_t i;
    for (i = 1; i < this->db.get_history_length(); ++i) {
        // Write next block_id
        write(kv[1].first, kv[1].second, block_id + i);
        // can still query earlier block_id from rw
        EXPECT_EQ(
            this->db.get(prefix + kv[0].first, block_id).value(), kv[0].second);
        // New block is written too...
        EXPECT_EQ(
            this->db.get(prefix + kv[1].first, block_id + i).value(),
            kv[1].second);
    }

    // This will exceed the ring buffer capacity, kicking out the first write.
    write(kv[1].first, kv[1].second, block_id + i);
    auto bad_read = this->db.get(prefix + kv[0].first, block_id);
    EXPECT_TRUE(bad_read.has_error());
    EXPECT_EQ(bad_read.error(), DbError::key_not_found);
}

TEST(DbTest, move_trie_causes_discontinuous_history)
{
    std::filesystem::path const dbname{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_db_test_discontinuous_history"};
    StateMachineAlwaysMerkle machine{};
    OnDiskDbConfig config{// with compaction
                          .compaction = true,
                          .sq_thread_cpu{std::nullopt},
                          .dbname_paths = {dbname},
                          .file_size_db = 8,
                          .history_length = DBTEST_HISTORY_LENGTH};
    Db db{machine, config};
    EXPECT_EQ(db.get_history_length(), DBTEST_HISTORY_LENGTH);
    Db ro_db{ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
    EXPECT_EQ(ro_db.get_history_length(), DBTEST_HISTORY_LENGTH);

    // continuous upsert() and move_trie_version_forward() leads to
    // discontinuity in history
    auto const &kv = fixed_updates::kv;
    auto const prefix = 0x00_hex;
    uint64_t block_id = 0;

    // Upsert the same data in block 0 - 10
    for (; block_id <= 10; ++block_id) {
        upsert_updates_flat_list(
            db,
            prefix,
            block_id,
            make_update(kv[0].first, kv[0].second),
            make_update(kv[1].first, kv[1].second));
        EXPECT_TRUE(db.get(prefix + kv[0].first, block_id).has_value());
        EXPECT_TRUE(db.get(prefix + kv[1].first, block_id).has_value());

        // ro_db
        EXPECT_EQ(
            ro_db.get(prefix + kv[0].first, block_id).value(), kv[0].second);
        EXPECT_EQ(
            ro_db.get(prefix + kv[1].first, block_id).value(), kv[1].second);
        EXPECT_EQ(
            ro_db.get_data(prefix, block_id).value(),
            0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);
    }
    block_id = 10;
    EXPECT_EQ(ro_db.get_earliest_block_id(), 0);
    EXPECT_EQ(ro_db.get_latest_block_id(), block_id);

    // Upsert again at block 10
    upsert_updates_flat_list(
        db,
        prefix,
        block_id,
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));
    EXPECT_EQ(ro_db.get(prefix + kv[2].first, block_id).value(), kv[2].second);
    EXPECT_EQ(ro_db.get(prefix + kv[3].first, block_id).value(), kv[3].second);
    EXPECT_EQ(
        ro_db.get_data(prefix, block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);

    EXPECT_EQ(ro_db.get_earliest_block_id(), 0);
    EXPECT_EQ(ro_db.get_latest_block_id(), block_id);

    // Move trie version to a later dest_block_id, which invalidates some
    // but not all history versions
    uint64_t const dest_block_id = ro_db.get_history_length() + 5;
    db.move_trie_version_forward(block_id, dest_block_id);

    // Now valid version are 6-9, 1005 (DBTEST_HISTORY_LENGTH+5)
    EXPECT_EQ(ro_db.get_latest_block_id(), dest_block_id);
    EXPECT_EQ(
        ro_db.get_earliest_block_id(),
        dest_block_id - ro_db.get_history_length() + 1);

    // src block 10 should be invalid
    EXPECT_TRUE(ro_db.find(prefix, block_id).has_error());

    // block before earliest block id should be invalid
    for (uint64_t i = 0; i < ro_db.get_earliest_block_id(); ++i) {
        EXPECT_TRUE(ro_db.find(prefix, i).has_error());
    }

    // block before `block_id` that being moved from should still work
    for (auto i = ro_db.get_earliest_block_id(); i < block_id; ++i) {
        EXPECT_EQ(ro_db.get(prefix + kv[0].first, i).value(), kv[0].second);
        EXPECT_EQ(ro_db.get(prefix + kv[1].first, i).value(), kv[1].second);
        EXPECT_EQ(
            ro_db.get_data(prefix, i).value(),
            0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);
    }

    // More empty upserts to invalidate the version at front
    block_id = dest_block_id + 1;
    for (auto lower_bound = db.get_earliest_block_id(); lower_bound <= 10;
         ++lower_bound) {
        upsert_updates_flat_list(db, prefix, block_id);
        ++block_id;
    }
    auto const max_block_id = block_id - 1;
    EXPECT_EQ(
        ro_db.get_data(prefix, max_block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
    EXPECT_EQ(ro_db.get_earliest_block_id(), dest_block_id);
    EXPECT_EQ(ro_db.get_latest_block_id(), max_block_id);

    // Jump way far ahead, which erases all histories
    uint64_t far_dest_block_id = ro_db.get_history_length() * 3;
    db.move_trie_version_forward(db.get_latest_block_id(), far_dest_block_id);

    EXPECT_EQ(
        db.get(prefix + kv[2].first, far_dest_block_id).value(), kv[2].second);
    EXPECT_EQ(
        db.get(prefix + kv[3].first, far_dest_block_id).value(), kv[3].second);
    EXPECT_EQ(
        db.get_data(prefix, far_dest_block_id).value(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);

    // only history version
    EXPECT_EQ(ro_db.get_latest_block_id(), far_dest_block_id);
    EXPECT_EQ(ro_db.get_earliest_block_id(), far_dest_block_id);
}

TYPED_TEST(DbTest, scalability)
{
    static constexpr size_t COUNT = 1000000;
    static constexpr size_t MAX_CONCURRENCY = 32;
    static constexpr uint64_t BLOCK_ID = 0x123;
    std::vector<monad::byte_string> keys;
    {
        std::vector<monad::mpt::Update> updates;
        keys.reserve(COUNT);
        updates.reserve(COUNT);
        monad::small_prng rand;
        UpdateList ul;
        for (size_t n = 0; n < COUNT; n++) {
            monad::byte_string key(16, 0);
            auto *key_ = (uint32_t *)key.data();
            key_[0] = rand();
            key_[1] = rand();
            key_[2] = rand();
            key_[3] = rand();
            keys.emplace_back(std::move(key));
            updates.emplace_back(make_update(keys.back(), keys.back()));
            ul.push_front(updates.back());
        }
        this->db.upsert(std::move(ul), BLOCK_ID);
    }
    std::vector<std::thread> threads;
    std::vector<::boost::fibers::fiber> fibers;
    threads.reserve(MAX_CONCURRENCY);
    fibers.reserve(MAX_CONCURRENCY);
    for (size_t n = 1; n <= MAX_CONCURRENCY; n <<= 1) {
        std::cout << "\n   Testing " << n
                  << " kernel threads concurrently doing Db::get() ..."
                  << std::endl;
        threads.clear();
        std::atomic<size_t> latch(0);
        std::atomic<uint32_t> ops(0);
        for (size_t i = 0; i < n; i++) {
            threads.emplace_back(
                [&](size_t myid) {
                    monad::small_prng rand{uint32_t(myid)};
                    latch++;
                    while (latch != 0) {
                        ::boost::this_fiber::yield();
                    }
                    while (latch.load(std::memory_order_relaxed) == 0) {
                        size_t const idx = rand() % COUNT;
                        auto r = this->db.get(keys[idx], BLOCK_ID);
                        MONAD_ASSERT(r);
                        ops.fetch_add(1, std::memory_order_relaxed);
                        ::boost::this_fiber::yield();
                    }
                    latch++;
                },
                i);
        }
        while (latch < n) {
            ::boost::this_fiber::yield();
        }
        auto begin = std::chrono::steady_clock::now();
        latch = 0;
        ::boost::this_fiber::sleep_for(std::chrono::seconds(5));
        latch = 1;
        auto end = std::chrono::steady_clock::now();
        std::cout << "      Did "
                  << (1000000.0 * ops /
                      double(
                          std::chrono::duration_cast<std::chrono::microseconds>(
                              end - begin)
                              .count()))
                  << " ops/sec." << std::endl;
        std::cout << "      Awaiting threads to exit ..." << std::endl;
        while (latch < n + 1) {
            ::boost::this_fiber::yield();
        }
        std::cout << "      Joining ..." << std::endl;
        for (auto &i : threads) {
            i.join();
        }

        std::cout << "   Testing " << n
                  << " fibers concurrently doing Db::get() ..." << std::endl;
        fibers.clear();
        latch = 0;
        ops = 0;
        for (size_t i = 0; i < n; i++) {
            fibers.emplace_back(
                [&](size_t myid) {
                    monad::small_prng rand{uint32_t(myid)};
                    latch++;
                    while (latch != 0) {
                        ::boost::this_fiber::yield();
                    }
                    while (latch.load(std::memory_order_relaxed) == 0) {
                        size_t const idx = rand() % COUNT;
                        auto r = this->db.get(keys[idx], BLOCK_ID);
                        MONAD_ASSERT(r);
                        ops.fetch_add(1, std::memory_order_relaxed);
                        ::boost::this_fiber::yield();
                    }
                    latch++;
                },
                i);
        }
        while (latch < n) {
            ::boost::this_fiber::yield();
        }
        begin = std::chrono::steady_clock::now();
        latch = 0;
        ::boost::this_fiber::sleep_for(std::chrono::seconds(5));
        latch = 1;
        end = std::chrono::steady_clock::now();
        std::cout << "      Did "
                  << (1000000.0 * ops /
                      double(
                          std::chrono::duration_cast<std::chrono::microseconds>(
                              end - begin)
                              .count()))
                  << " ops/sec." << std::endl;
        std::cout << "      Awaiting fibers to exit ..." << std::endl;
        while (latch < n + 1) {
            ::boost::this_fiber::yield();
        }
        std::cout << "      Joining ..." << std::endl;
        for (auto &i : fibers) {
            ::boost::this_fiber::yield();
            i.join();
        }
    }
}

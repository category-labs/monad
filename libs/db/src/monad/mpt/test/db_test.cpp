#include "test_fixtures_base.hpp"

#include <monad/async/config.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/util.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/core/result.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/core/unaligned.hpp>
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
#include <deque>
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
            .next = std::move(ul),
            .version = static_cast<int64_t>(block_id)};
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
        Db db{
            machine,
            OnDiskDbConfig{.fixed_history_length = DBTEST_HISTORY_LENGTH}};
    };

    std::filesystem::path create_temp_file(long size_gb)
    {
        std::filesystem::path const filename{
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_db_test_XXXXXX"};
        int const fd = ::mkstemp((char *)filename.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(-1 != ::ftruncate(fd, size_gb * 1024 * 1024 * 1024));
        ::close(fd);
        return filename;
    }

    struct OnDiskDbWithFileFixture : public ::testing::Test
    {
        std::filesystem::path const dbname;
        StateMachineAlwaysMerkle machine;
        OnDiskDbConfig config;
        Db db;

        OnDiskDbWithFileFixture()
            : dbname{create_temp_file(8)}
            , machine{StateMachineAlwaysMerkle{}}
            , config{OnDiskDbConfig{
                  .compaction = true,
                  .sq_thread_cpu = std::nullopt,
                  .dbname_paths = {dbname},
                  .fixed_history_length = DBTEST_HISTORY_LENGTH}}
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

    monad::byte_string keccak_int_to_string(size_t const n)
    {
        monad::byte_string ret(KECCAK256_SIZE, 0);
        keccak256((unsigned char const *)&n, 8, ret.data());
        return ret;
    }

    std::pair<std::vector<monad::byte_string>, std::vector<Update>>
    prepare_random_updates(unsigned size)
    {
        std::vector<monad::byte_string> bytes_alloc;
        std::vector<Update> updates_alloc;
        for (size_t i = 0; i < size; ++i) {
            auto &kv = bytes_alloc.emplace_back(keccak_int_to_string(i));
            updates_alloc.push_back(Update{
                .key = kv,
                .value = kv,
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
    ASSERT_EQ(ctx->root_cache.size(), 1);
    auto const offset = ctx->aux.get_root_offset_at_version(version);
    ASSERT_NE(offset, INVALID_OFFSET);

    AsyncContext::TrieRootCache::ConstAccessor acc;
    ASSERT_TRUE(ctx->root_cache.find(acc, offset));
    auto root = acc->second->val;
    ro_db.traverse(NodeCursor{*root}, traverse_machine, version);
}

TEST_F(OnDiskDbWithFileAsyncFixture, root_cache_invalidation)
{
    auto const &kv = fixed_updates::kv;

    auto const prefix0 = 0x001234_hex;
    auto const final_prefix = 0x10_hex;
    uint64_t const block_id = 0;
    upsert_updates_flat_list(
        db, prefix0, block_id, make_update(kv[0].first, kv[0].second));

    async_get(
        make_get_sender(ctx.get(), prefix0 + kv[0].first, block_id),
        [&](result_t res) {
            ASSERT_TRUE(res.has_value());
            EXPECT_EQ(res.value(), kv[0].second);
        });
    poll_until(1);

    ASSERT_EQ(ctx.get()->root_cache.size(), 1);

    // Copy trie to new prefix. This rewrites the root offset in memory
    db.copy_trie(block_id, prefix0, block_id, final_prefix, true);

    // Do another async read on the same version
    async_get(
        make_get_sender(ctx.get(), final_prefix + kv[0].first, block_id),
        [&](result_t res) {
            ASSERT_TRUE(res.has_value());
            EXPECT_EQ(res.value(), kv[0].second);
        });
    poll_until(2);

    // There should be 2 elements in the root cache because the offset in memory
    // has changed.
    EXPECT_EQ(ctx.get()->root_cache.size(), 2);
}

TEST_F(OnDiskDbWithFileFixture, open_emtpy_rodb)
{
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

TEST_F(OnDiskDbWithFileFixture, read_only_db_concurrent)
{
    // Have one thread make forward progress by updating new versions and
    // erasing outdated ones. Meanwhile spwan a read thread that queries
    // historical states.
    std::atomic<bool> done{false};
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
                EXPECT_GT(min_block_id, read_version);
                read_version = min_block_id + 100;
                ++nfailed;
            }
        }
        std::cout << "Reader thread finished. Currently read till version "
                  << read_version << ". Did " << nsuccess << " successful and "
                  << nfailed << " failed reads" << std::endl;
        EXPECT_TRUE(nsuccess > 0);
        EXPECT_LE(read_version, ro_db.get_latest_block_id());
    };

    // construct RWDb
    uint64_t version = 0;

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

TEST_F(OnDiskDbWithFileFixture, upsert_but_not_write_root)
{
    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbname}};
    Db ro_db{ro_config};

    // upsert not write root, rodb reads nothing
    auto const k1 = 0x12345678_hex;
    auto const k2 = 0x22345678_hex;
    auto u1 = make_update(k1, k1);
    UpdateList ul;
    ul.push_front(u1);

    constexpr uint64_t block_id = 0;
    // upsert disable write root
    this->db.upsert(std::move(ul), block_id, true, true, false);

    EXPECT_TRUE(ro_db.get(NibblesView{k1}, block_id).has_error());

    ul.clear();
    auto u2 = make_update(k2, k2);
    ul.push_front(u2);
    this->db.upsert(std::move(ul), block_id); // write root to disk

    auto const res1 = ro_db.get(NibblesView{k1}, block_id);
    ASSERT_TRUE(res1.has_value());
    EXPECT_EQ(res1.value(), k1);

    auto const res2 = ro_db.get(NibblesView{k2}, block_id);
    ASSERT_TRUE(res2.has_value());
    EXPECT_EQ(res2.value(), k2);
}

TEST_F(OnDiskDbWithFileFixture, read_only_db_traverse_concurrent)
{
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

TEST_F(OnDiskDbWithFileFixture, benchmark_blocking_parallel_traverse)
{
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

TEST_F(OnDiskDbWithFileFixture, load_correct_root_upon_reopen_nonempty_db)
{
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

TEST(DbTest, out_of_order_upserts_to_nonexist_earlier_version)
{
    auto const dbname = create_temp_file(2); // 2Gb db
    auto undb = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dbname); });
    StateMachineAlwaysEmpty machine{};
    OnDiskDbConfig config{
        .compaction = true,
        .sq_thread_cpu{std::nullopt},
        .dbname_paths = {dbname},
        .fixed_history_length = DBTEST_HISTORY_LENGTH};
    Db db{machine, config};

    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbname}};
    Db rodb{ro_config};

    constexpr size_t total_keys = 10000;
    auto [bytes_alloc, updates_alloc] = prepare_random_updates(total_keys);

    UpdateList ls;
    for (unsigned i = 0; i < total_keys; ++i) {
        ls.push_front(updates_alloc[i]);
    }
    db.upsert(std::move(ls), 0);
    constexpr uint64_t start_version = 1000;

    db.move_trie_version_forward(0, start_version);
    EXPECT_EQ(rodb.get_earliest_block_id(), start_version);
    EXPECT_EQ(rodb.get_latest_block_id(), start_version);
    EXPECT_EQ(rodb.get_history_length(), DBTEST_HISTORY_LENGTH);

    constexpr uint64_t min_version = 900;
    for (uint64_t v = start_version - 1; v >= min_version; --v) {
        UpdateList ls;
        ls.push_front(updates_alloc.front());
        db.upsert(std::move(ls), v);
        EXPECT_EQ(rodb.get_earliest_block_id(), v);
        EXPECT_EQ(rodb.get_latest_block_id(), start_version);
    }

    db.load_root_for_version(start_version);
    uint64_t const max_version = 2000;
    for (uint64_t v = start_version + 1; v <= max_version; ++v) {
        // upsert existing
        UpdateList ls;
        ls.push_front(updates_alloc.front());
        db.upsert(std::move(ls), v);
        EXPECT_EQ(
            rodb.get_earliest_block_id(),
            std::max(v - DBTEST_HISTORY_LENGTH + 1, min_version));
        EXPECT_EQ(rodb.get_latest_block_id(), v);
    }

    // lookup
    for (auto const &k : bytes_alloc) {
        auto res = rodb.get(k, max_version);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value(), k);
    }
}

TEST(DbTest, out_of_order_upserts_with_compaction)
{
    auto const dbname = create_temp_file(3); // 3Gb db
    auto undb = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dbname); });
    StateMachineAlwaysMerkle machine{};
    OnDiskDbConfig config{
        .compaction = true,
        .sq_thread_cpu{std::nullopt},
        .dbname_paths = {dbname},
        .fixed_history_length = DBTEST_HISTORY_LENGTH};
    Db db{machine, config};
    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbname}};
    Db rodb{ro_config};

    auto get_release_offsets = [](monad::byte_string_view const bytes)
        -> std::pair<uint32_t, uint32_t> {
        MONAD_ASSERT(bytes.size() == 8);
        return {
            monad::unaligned_load<uint32_t>(bytes.data()),
            monad::unaligned_load<uint32_t>(bytes.data() + sizeof(uint32_t))};
    };

    auto const prefix = 0x00_hex;
    constexpr unsigned keys_per_version = 5;
    uint64_t block_id = 0;
    uint64_t n = 0;

    for (block_id = 0; block_id < 1000; ++block_id) {
        std::deque<monad::byte_string> kv_alloc;
        for (unsigned i = 0; i < keys_per_version; ++i) {
            kv_alloc.emplace_back(keccak_int_to_string(n++));
        }
        // upsert N
        upsert_updates_flat_list(
            db,
            prefix,
            block_id,
            make_update(kv_alloc[0], kv_alloc[0]),
            make_update(kv_alloc[1], kv_alloc[1]),
            make_update(kv_alloc[2], kv_alloc[2]),
            make_update(kv_alloc[3], kv_alloc[3]),
            make_update(kv_alloc[4], kv_alloc[4]));
        if (block_id == 0) {
            continue;
        }
        auto const result_n = rodb.get({}, block_id);
        EXPECT_TRUE(result_n.has_value());
        auto const [fast_n, slow_n] = get_release_offsets(result_n.value());
        auto const result_before = rodb.get({}, block_id - 1);
        EXPECT_TRUE(result_before.has_value());
        auto const [fast_n_1, slow_n_1] =
            get_release_offsets(result_before.value());
        EXPECT_GE(fast_n, fast_n_1);
        EXPECT_GE(slow_n, slow_n_1);
        // upsert on top of N-1
        upsert_updates_flat_list(
            db,
            prefix,
            block_id - 1,
            make_update(kv_alloc[0], kv_alloc[0]),
            make_update(kv_alloc[1], kv_alloc[1]),
            make_update(kv_alloc[2], kv_alloc[2]),
            make_update(kv_alloc[3], kv_alloc[3]),
            make_update(kv_alloc[4], kv_alloc[4]));
        auto const result_after = rodb.get({}, block_id - 1);
        EXPECT_TRUE(result_after.has_value());
        // offsets remain the same after the second upsert
        EXPECT_EQ(result_before.value(), result_after.value());
        // convert to byte_string so that both data are in scope
        monad::byte_string const data_n_1{
            rodb.get_data({prefix}, block_id - 1).value()};
        monad::byte_string const data_n{
            rodb.get_data({prefix}, block_id).value()};
        EXPECT_EQ(data_n_1, data_n) << block_id;
        // prepare for upserting N+1 on top of N
        db.load_root_for_version(block_id);
    }

    ASSERT_EQ(n, block_id * keys_per_version);
    auto const result_n = rodb.get({}, block_id - 1);
    EXPECT_TRUE(result_n.has_value());
    auto const [fast_n, slow_n] = get_release_offsets(result_n.value());
    EXPECT_EQ(
        rodb.get_data({prefix}, block_id - 1).value(),
        0x03786bcd10037502a4e08158de71f8078a40ce46c93ba13db90cb11841679f5e_hex);
    EXPECT_GT(fast_n, 0);
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
            if (node.has_value() && branch != INVALID_BRANCH) {
                ++num_leaves;
            }
            if (branch == INVALID_BRANCH) {
                // root is always a leaf
                EXPECT_TRUE(node.has_value());
                EXPECT_EQ(node.path_nibbles_len(), 0);
                EXPECT_GT(node.mask, 0);
            }
            else if (branch == 0) { // immediate node under root
                EXPECT_EQ(node.mask, 0b10);
                EXPECT_TRUE(node.has_value());
                EXPECT_EQ(node.value(), monad::byte_string_view{});
                EXPECT_TRUE(node.has_path());
                EXPECT_EQ(node.path_nibble_view(), make_nibbles({0x0}));
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
        EXPECT_EQ(traverse.num_up, 7);
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

TEST(DbTest, auto_expire_large_set)
{
    auto const dbname = create_temp_file(8);
    auto undb = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dbname); });
    StateMachineAlways<
        EmptyCompute,
        StateMachineConfig{.expire = true, .cache_depth = 3}>
        machine{};
    constexpr auto history_len = 20;
    OnDiskDbConfig config{
        .compaction = true,
        .sq_thread_cpu{std::nullopt},
        .dbname_paths = {dbname},
        .fixed_history_length = history_len};
    Db db{machine, config};

    auto const prefix = 0x00_hex;
    monad::byte_string const value(256 * 1024, 0);
    std::vector<monad::byte_string> keys;
    std::vector<monad::byte_string> values;
    constexpr unsigned keys_per_block = 5;
    constexpr uint64_t blocks = 1000;
    keys.reserve(blocks * keys_per_block);

    // randomize keys
    auto const seed = static_cast<uint32_t>(time(NULL));
    std::cout << "seed to reproduce: " << seed << std::endl;
    monad::small_prng rand(seed);
    for (uint64_t block_id = 0; block_id < blocks; ++block_id) {
        for (unsigned i = 0; i < keys_per_block; ++i) {
            auto &key = keys.emplace_back(monad::byte_string(32, 0));
            uint64_t raw = rand();
            keccak256((unsigned char const *)&raw, 8, key.data());
        }
        uint64_t const index = keys_per_block * block_id;
        upsert_updates_flat_list(
            db,
            prefix,
            block_id,
            make_update(keys[index], value, false, UpdateList{}, block_id),
            make_update(keys[index + 1], value, false, UpdateList{}, block_id),
            make_update(keys[index + 2], value, false, UpdateList{}, block_id),
            make_update(keys[index + 3], value, false, UpdateList{}, block_id),
            make_update(keys[index + 4], value, false, UpdateList{}, block_id));
        if (block_id >= history_len) {
            // query keys of block before (block_id - history_length + 1) should
            // fail
            auto index = (unsigned)(block_id - history_len) * keys_per_block;
            for (unsigned i = 0; i < keys_per_block; ++i) {
                EXPECT_FALSE(db.get(prefix + keys[index], block_id))
                    << "Expect failed look up of key = keccak(" << index
                    << ") at block " << block_id;
                ++index;
            }
            for (; index < keys_per_block * block_id; ++index) {
                EXPECT_TRUE(db.get(prefix + keys[index], block_id))
                    << "Expect successful look up of key = keccak(" << index
                    << ") at block " << block_id;
            }
        }
    }
}

TEST(DbTest, auto_expire)
{
    auto const dbname = create_temp_file(8);
    auto undb = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dbname); });
    StateMachineAlways<
        EmptyCompute,
        StateMachineConfig{.expire = true, .cache_depth = 3}>
        machine{};
    OnDiskDbConfig config{
        .compaction = true,
        .sq_thread_cpu{std::nullopt},
        .dbname_paths = {dbname},
        .fixed_history_length = 5};
    Db db{machine, config};
    auto const prefix = 0x00_hex;
    // insert 10 keys
    std::vector<monad::byte_string> keys;
    for (uint64_t i = 0; i < 10; ++i) {
        keys.emplace_back(serialize_as_big_endian<8>(i));
    }

    for (uint64_t block_id = 0; block_id < 10; ++block_id) {
        upsert_updates_flat_list(
            db,
            prefix,
            block_id,
            make_update(
                keys[block_id], keys[block_id], false, UpdateList{}, block_id));
        EXPECT_TRUE(db.get(prefix + keys[block_id], block_id).has_value())
            << block_id;
    }

    uint64_t latest_block_id = db.get_latest_block_id(),
             earliest_block_id = db.get_earliest_block_id();
    for (unsigned i = 0; i <= latest_block_id; ++i) {
        auto const res = db.get(prefix + keys[i], latest_block_id);
        if (i < earliest_block_id) { // keys 0-4 are expired
            EXPECT_FALSE(res.has_value()) << i;
        }
        else {
            EXPECT_TRUE(res.has_value()) << i;
            EXPECT_EQ(res.value(), keys[i]);
        }
    }

    // insert 5 more keys, branch out at an earlier nibble
    constexpr uint64_t offset = 0x100;
    for (uint64_t i = 0; i < 5; ++i) {
        keys.emplace_back(serialize_as_big_endian<8>(i + offset));
    }
    for (uint64_t block_id = latest_block_id + 1;
         block_id <= 5 + latest_block_id;
         ++block_id) {
        upsert_updates_flat_list(
            db,
            prefix,
            block_id,
            make_update(
                keys[block_id], keys[block_id], false, UpdateList{}, block_id));
        EXPECT_TRUE(db.get(prefix + keys[block_id], block_id).has_value())
            << block_id;
    }

    latest_block_id = db.get_latest_block_id(); // 14
    earliest_block_id = db.get_earliest_block_id(); // 10
    for (unsigned i = 0; i <= latest_block_id; ++i) {
        auto const res = db.get(prefix + keys[i], latest_block_id);
        if (i < earliest_block_id) { // keys 0-9 are expired
            EXPECT_FALSE(res.has_value()) << i;
        }
        else {
            EXPECT_TRUE(res.has_value()) << i;
            EXPECT_EQ(res.value(), keys[i]);
        }
    }
}

TYPED_TEST(DbTest, copy_trie_from_to_same_version)
{
    // insert random updates under a src prefix
    constexpr unsigned nkeys = 20;
    auto [kv_alloc, updates_alloc] = prepare_random_updates(nkeys);
    auto const src_prefix = 0x00_hex;
    auto const dest_prefix = 0x01_hex;
    auto const dest_prefix2 = 0x02_hex;
    auto const long_dest_prefix = 0x1010_hex;
    uint64_t const version = 0;
    UpdateList ls;
    for (auto &u : updates_alloc) {
        ls.push_front(u);
    }
    UpdateList updates;
    Update top_update{
        .key = src_prefix,
        .value = monad::byte_string_view{},
        .incarnation = true,
        .next = std::move(ls),
        .version = version};
    updates.push_front(top_update);
    this->db.upsert(std::move(updates), version);
    auto const src_prefix_data =
        monad::byte_string{this->db.get_data(src_prefix, version).value()};

    auto verify_dest_state = [&](Db &db, monad::byte_string const prefix) {
        EXPECT_EQ(db.get_latest_block_id(), version);
        auto const data_res = db.get_data(prefix, version);
        EXPECT_TRUE(data_res.has_value()) << NibblesView{prefix};
        EXPECT_EQ(src_prefix_data, data_res.value()) << NibblesView{prefix};
        // look up from prefix, assert same data as src trie
        for (unsigned i = 0; i < nkeys; ++i) {
            auto const res = db.get(prefix + kv_alloc[i], version);
            EXPECT_TRUE(res.has_value()) << NibblesView{prefix};
            EXPECT_EQ(res.value(), kv_alloc[i]) << NibblesView{prefix};
        }
    };
    // copy to dest prefix, switch to dest_version
    this->db.copy_trie(version, src_prefix, version, dest_prefix);
    if (this->db.is_on_disk()) {
        verify_dest_state(this->db, src_prefix);
    }
    verify_dest_state(this->db, dest_prefix);

    this->db.copy_trie(version, dest_prefix, version, dest_prefix2);
    if (this->db.is_on_disk()) {
        verify_dest_state(this->db, src_prefix);
        verify_dest_state(this->db, dest_prefix);
    }
    verify_dest_state(this->db, dest_prefix2);

    // copy from src to an existing prefix
    if (this->db.is_on_disk()) {
        this->db.copy_trie(version, src_prefix, version, dest_prefix);
        verify_dest_state(this->db, src_prefix);
        verify_dest_state(this->db, dest_prefix);
    }

    // copy from dest2 to longer prefix
    this->db.copy_trie(version, dest_prefix2, version, long_dest_prefix);
    if (this->db.is_on_disk()) {
        verify_dest_state(this->db, src_prefix);
        verify_dest_state(this->db, dest_prefix2);
    }
    verify_dest_state(this->db, long_dest_prefix);
}

TEST_F(OnDiskDbWithFileFixture, copy_trie_to_different_version_modify_state)
{
    std::deque<monad::byte_string> kv_alloc;
    for (size_t i = 0; i < 10; ++i) {
        kv_alloc.emplace_back(keccak_int_to_string(i));
    }
    auto const prefix = 0x0012_hex;
    auto const prefix0 = 0x001233_hex;
    auto const prefix1 = 0x001235_hex;
    auto const prefix2 = 0x001239_hex;
    auto const last_prefix = 0x10_hex;
    uint64_t const block_id = 0;
    upsert_updates_flat_list(
        db, prefix, block_id, make_update(kv_alloc[0], kv_alloc[0]));

    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbname}};
    Db rodb{ro_config};

    // copy trie to a new version
    // read: can't read new dest version until upserting
    db.copy_trie(block_id, prefix, block_id + 1, prefix0);
    EXPECT_FALSE(rodb.get({}, block_id + 1).has_value());
    db.upsert({}, block_id + 1);

    db.copy_trie(block_id, prefix, block_id + 1, prefix1);
    upsert_updates_flat_list(
        db, prefix1, block_id + 1, make_update(kv_alloc[1], kv_alloc[1]));

    auto verify_before1 = [&](int const invoke_count) {
        auto res = rodb.get(prefix1 + kv_alloc[0], block_id + 1);
        ASSERT_TRUE(res.has_value()) << invoke_count;
        EXPECT_EQ(res.value(), kv_alloc[0]);
        res = rodb.get(prefix1 + kv_alloc[1], block_id + 1);
        ASSERT_TRUE(res.has_value()) << invoke_count;
        EXPECT_EQ(res.value(), kv_alloc[1]);
        ASSERT_FALSE(rodb.get(prefix1 + kv_alloc[2], block_id + 1))
            << invoke_count;

        res = rodb.get(prefix0 + kv_alloc[0], block_id + 1);
        ASSERT_TRUE(res.has_value()) << invoke_count;
        EXPECT_EQ(res.value(), kv_alloc[0]);
        ASSERT_FALSE(rodb.get(prefix0 + kv_alloc[1], block_id + 1))
            << invoke_count;
        ASSERT_FALSE(rodb.get(prefix0 + kv_alloc[2], block_id + 1))
            << invoke_count;
    };
    int invoke_idx = 0;
    verify_before1(invoke_idx++);

    db.copy_trie(block_id, prefix, block_id + 1, prefix2);
    upsert_updates_flat_list(
        db, prefix2, block_id + 1, make_update(kv_alloc[2], kv_alloc[2]));

    auto verify_before2 = [&](int const invoke_count) {
        auto res = rodb.get(prefix2 + kv_alloc[0], block_id + 1);
        ASSERT_TRUE(res.has_value()) << invoke_count;
        EXPECT_EQ(res.value(), kv_alloc[0]);
        res = rodb.get(prefix2 + kv_alloc[2], block_id + 1);
        ASSERT_TRUE(res.has_value()) << invoke_count;
        EXPECT_EQ(res.value(), kv_alloc[2]);
        ASSERT_FALSE(rodb.get(prefix2 + kv_alloc[1], block_id + 1))
            << invoke_count;

        verify_before1(invoke_count);
    };
    verify_before2(invoke_idx++);

    // copy trie to a different prefix within the same version
    db.copy_trie(block_id + 1, prefix1, block_id + 1, last_prefix, false);
    EXPECT_FALSE(rodb.get(last_prefix, block_id + 1).has_value());
    upsert_updates_flat_list(
        db, last_prefix, block_id + 1, make_update(kv_alloc[3], kv_alloc[3]));
    {
        auto res = rodb.get(last_prefix + kv_alloc[0], block_id + 1);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value(), kv_alloc[0]);
        res = rodb.get(last_prefix + kv_alloc[1], block_id + 1);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value(), kv_alloc[1]);
        res = rodb.get(last_prefix + kv_alloc[3], block_id + 1);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value(), kv_alloc[3]);
        ASSERT_FALSE(rodb.get(last_prefix + kv_alloc[2], block_id + 1));

        verify_before2(invoke_idx++);
    }
}

TEST_F(OnDiskDbWithFileFixture, move_trie_causes_discontinuous_history)
{
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

TEST_F(OnDiskDbWithFileFixture, reset_history_length_concurrent)
{
    std::atomic<bool> done{false};
    Db ro_db{ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
    auto const prefix = 0x00_hex;

    // fille rwdb with some blocks
    auto const &kv = fixed_updates::kv;
    for (uint64_t block_id = 0; block_id < DBTEST_HISTORY_LENGTH; ++block_id) {
        upsert_updates_flat_list(
            db, prefix, block_id, make_update(kv[0].first, kv[0].second));
    }

    EXPECT_EQ(ro_db.get_history_length(), DBTEST_HISTORY_LENGTH);
    EXPECT_EQ(ro_db.get_latest_block_id(), DBTEST_HISTORY_LENGTH - 1);
    auto const res = ro_db.get(prefix + kv[0].first, 0);
    EXPECT_TRUE(res.has_value());
    EXPECT_EQ(res.value(), kv[0].second);

    uint64_t const end_history_length =
        DBTEST_HISTORY_LENGTH - DBTEST_HISTORY_LENGTH / 2;
    uint64_t const expected_earliest_block =
        DBTEST_HISTORY_LENGTH - end_history_length;

    // ro db starts reading from block 0, increment read block id when fail
    // reading current block
    auto ro_query = [&] {
        uint64_t read_block_id = 0;
        while (!done.load(std::memory_order_acquire)) {
            auto const get_res = ro_db.get(prefix + kv[0].first, read_block_id);
            if (get_res.has_error()) {
                ++read_block_id;
            }
            else {
                EXPECT_EQ(get_res.value(), kv[0].second);
            }
        } // update has finished
        EXPECT_EQ(ro_db.get_earliest_block_id(), expected_earliest_block);
        std::cout << "Reader thread finished. Currently reading block "
                  << read_block_id << ". Earliest block number is "
                  << ro_db.get_earliest_block_id() << std::endl;
        EXPECT_LE(read_block_id, ro_db.get_earliest_block_id());

        while (ro_db.get(prefix + kv[0].first, read_block_id).has_error()) {
            ++read_block_id;
        }
        EXPECT_EQ(read_block_id, expected_earliest_block);
        EXPECT_EQ(ro_db.get_history_length(), end_history_length);
    };

    // start read thread
    std::thread reader(ro_query);

    // current thread starts to shorten history
    config.append = true;
    while (config.fixed_history_length > end_history_length) {
        config.fixed_history_length = *config.fixed_history_length - 1;
        Db new_db{machine, config};
        EXPECT_EQ(new_db.get_history_length(), config.fixed_history_length);
        EXPECT_EQ(new_db.get_latest_block_id(), DBTEST_HISTORY_LENGTH - 1);
    }

    EXPECT_EQ(ro_db.get_history_length(), end_history_length);
    EXPECT_EQ(ro_db.get_earliest_block_id(), expected_earliest_block);

    done.store(true, std::memory_order_release);
    reader.join();
    std::cout << "Writer finished. History length is shortened to "
              << db.get_history_length() << ". Max version in rwdb is "
              << db.get_latest_block_id() << ", min version in rwdb is "
              << db.get_earliest_block_id() << std::endl;
}

TEST_F(OnDiskDbWithFileFixture, rwdb_reset_history_length)
{
    EXPECT_EQ(db.get_history_length(), DBTEST_HISTORY_LENGTH);

    // Insert more than history length number of blocks
    auto const &kv = fixed_updates::kv;
    auto const prefix = 0x00_hex;
    uint64_t const max_block_id = DBTEST_HISTORY_LENGTH + 10;
    for (uint64_t block_id = 0; block_id <= max_block_id; ++block_id) {
        upsert_updates_flat_list(
            db,
            prefix,
            block_id,
            make_update(kv[0].first, kv[0].second),
            make_update(kv[1].first, kv[1].second));
    }

    EXPECT_TRUE(db.get(prefix + kv[1].first, 0).has_error());
    EXPECT_TRUE(db.get(prefix + kv[1].first, max_block_id).has_value());
    auto const min_block_num_before = max_block_id - DBTEST_HISTORY_LENGTH + 1;
    EXPECT_EQ(db.get_earliest_block_id(), min_block_num_before);
    EXPECT_TRUE(db.get(prefix + kv[1].first, min_block_num_before).has_value());

    Db ro_db{ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
    EXPECT_EQ(ro_db.get_history_length(), DBTEST_HISTORY_LENGTH);
    EXPECT_TRUE(ro_db.get(prefix + kv[1].first, 0).has_error());
    EXPECT_TRUE(ro_db.get(prefix + kv[1].first, max_block_id).has_value());
    EXPECT_EQ(
        ro_db.get_earliest_block_id(),
        max_block_id - DBTEST_HISTORY_LENGTH + 1);
    EXPECT_TRUE(ro_db.get(prefix + kv[1].first, ro_db.get_earliest_block_id())
                    .has_value());

    // Reopen rwdb with a shorter history length
    config.fixed_history_length = DBTEST_HISTORY_LENGTH / 2;
    config.append = true;
    {
        Db new_rw{machine, config};
        EXPECT_EQ(new_rw.get_history_length(), config.fixed_history_length);
        EXPECT_EQ(new_rw.get_latest_block_id(), max_block_id);
    }
    EXPECT_EQ(ro_db.get_history_length(), config.fixed_history_length);
    EXPECT_EQ(ro_db.get_latest_block_id(), max_block_id);
    EXPECT_TRUE(ro_db.get(prefix + kv[1].first, max_block_id).has_value());
    EXPECT_TRUE(
        ro_db.get(prefix + kv[1].first, min_block_num_before).has_error());
    auto const min_block_num_after =
        max_block_id - *config.fixed_history_length + 1;
    EXPECT_EQ(ro_db.get_earliest_block_id(), min_block_num_after);
    EXPECT_TRUE(
        ro_db.get(prefix + kv[1].first, min_block_num_after).has_value());
    EXPECT_TRUE(
        ro_db.get(prefix + kv[1].first, min_block_num_after - 1).has_error());

    // Reopen rwdb with a longer history length
    config.fixed_history_length = DBTEST_HISTORY_LENGTH;
    Db new_rw{machine, config};
    EXPECT_EQ(new_rw.get_history_length(), config.fixed_history_length);
    EXPECT_EQ(new_rw.get_earliest_block_id(), min_block_num_after);
    EXPECT_EQ(ro_db.get_history_length(), config.fixed_history_length);
    EXPECT_EQ(ro_db.get_earliest_block_id(), min_block_num_after);
    EXPECT_EQ(ro_db.get_latest_block_id(), max_block_id);
    EXPECT_TRUE(
        ro_db.get(prefix + kv[1].first, min_block_num_before).has_error());
    // Inserts more blocks
    auto const new_max_block_id =
        min_block_num_after + *config.fixed_history_length - 1;
    for (uint64_t block_id = max_block_id + 1; block_id <= new_max_block_id;
         ++block_id) {
        upsert_updates_flat_list(
            db,
            prefix,
            block_id,
            make_update(kv[0].first, kv[0].second),
            make_update(kv[1].first, kv[1].second));
    }
    EXPECT_EQ(ro_db.get_latest_block_id(), new_max_block_id);
    EXPECT_EQ(ro_db.get_earliest_block_id(), min_block_num_after);
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

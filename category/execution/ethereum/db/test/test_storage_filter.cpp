// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/storage_filter.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/test/test_fixtures_gtest.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <memory>
#include <optional>
#include <string>
#include <unistd.h>

using namespace monad;
using namespace monad::test;
using namespace monad::literals;

namespace
{
    // Slots 1 and 2 share a page on a page-encoded db; 0x1000 and 0x2000 are
    // on pages of their own.
    constexpr auto k_a = bytes32_t{uint64_t{0x01}};
    constexpr auto k_b = bytes32_t{uint64_t{0x02}};
    constexpr auto k_c = bytes32_t{uint64_t{0x1000}};
    constexpr auto k_d = bytes32_t{uint64_t{0x2000}};
    constexpr auto v1 =
        0x0000000000000000000000000000000000000000000000000000000000000011_bytes32;
    constexpr auto v2 =
        0x0000000000000000000000000000000000000000000000000000000000000022_bytes32;
    constexpr auto v3 =
        0x0000000000000000000000000000000000000000000000000000000000000033_bytes32;

    Incarnation const INC{0, 0};
    constexpr StorageFilter::Config SMALL{
        .size_bytes = 64 << 10, .num_probes = 6};

    Account const account{.nonce = 1};

    template <class Machine>
    struct InMemoryDb : public ::testing::Test
    {
        mpt::Db db{std::make_unique<Machine>()};
    };

    template <class Machine>
    struct OnDiskDb : public ::testing::Test
    {
        mpt::Db db{std::make_unique<Machine>(), mpt::OnDiskDbConfig{}};
    };

    // Block 0: ADDR_A holds k_a and k_c.
    void commit_block_0(TrieDb &tdb)
    {
        commit_sequential(
            tdb,
            StateDeltas(
                {{ADDR_A,
                  StateDelta{
                      .account = {std::nullopt, account},
                      .storage =
                          {{k_a, {bytes32_t{}, v1}},
                           {k_c, {bytes32_t{}, v2}}}}}}),
            Code{},
            BlockHeader{.number = 0});
    }

    std::shared_ptr<StorageFilter>
    built_filter(mpt::Db &db, TrieDb const &tdb, uint64_t const block_number)
    {
        auto filter = std::make_shared<StorageFilter>(
            SMALL, tdb.is_page_encoded(), block_number);
        EXPECT_TRUE(
            insert_storage_leaves(*filter, db, tdb.get_root(), block_number)
                .has_value());
        filter->set_ready();
        return filter;
    }

    std::filesystem::path temp_path()
    {
        return std::filesystem::temp_directory_path() /
               (std::string{"storage_filter_test_"} +
                ::testing::UnitTest::GetInstance()
                    ->current_test_info()
                    ->name() +
                std::to_string(::getpid()));
    }
}

template <typename T>
struct StorageFilterTest : public T
{
};

using DbTypes = ::testing::Types<
    InMemoryDb<InMemoryMachine>, InMemoryDb<MonadInMemoryMachine>,
    OnDiskDb<OnDiskMachine>, OnDiskDb<MonadOnDiskMachine>>;
TYPED_TEST_SUITE(StorageFilterTest, DbTypes);

TYPED_TEST(StorageFilterTest, build_inserts_every_storage_leaf)
{
    TrieDb tdb{this->db};
    commit_block_0(tdb);
    StorageFilter filter{SMALL, tdb.is_page_encoded(), 0};
    // k_a and k_c: two slots, or two pages
    EXPECT_EQ(insert_storage_leaves(filter, this->db, tdb.get_root(), 0), 2);
    // The 256 subtries below the first two nibbles partition the leaves
    StorageFilter parts{SMALL, tdb.is_page_encoded(), 0};
    uint64_t sum = 0;
    for (unsigned part = 0; part < 256; ++part) {
        auto const leaves = insert_storage_leaves(
            parts,
            this->db,
            tdb.get_root(),
            0,
            static_cast<uint16_t>(1u << (part >> 4)),
            static_cast<uint16_t>(1u << (part & 15)));
        ASSERT_TRUE(leaves.has_value());
        sum += leaves.value();
    }
    EXPECT_EQ(sum, 2);
    // No subtrie visited
    StorageFilter empty{SMALL, tdb.is_page_encoded(), 0};
    EXPECT_EQ(
        insert_storage_leaves(
            empty, this->db, tdb.get_root(), 0, /*first_nibbles=*/0),
        0);
}

TYPED_TEST(StorageFilterTest, absent_storage_skips_the_trie)
{
    TrieDb tdb{this->db};
    commit_block_0(tdb);
    tdb.set_storage_filter(built_filter(this->db, tdb, 0));

    uint64_t const finds = tdb.storage_read_count();
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_a), v1);
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_c), v2);
    EXPECT_EQ(tdb.storage_read_count(), finds + 2);

    // A slot on a page of its own, and an account without storage
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_d), bytes32_t{});
    EXPECT_EQ(tdb.read_storage(ADDR_B, INC, k_a), bytes32_t{});
    EXPECT_EQ(tdb.storage_read_count(), finds + 2);

    // On a page-encoded db k_b shares k_a's page, which exists
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_b), bytes32_t{});
    EXPECT_EQ(
        tdb.storage_read_count(), finds + 2 + (tdb.is_page_encoded() ? 1 : 0));
}

TYPED_TEST(StorageFilterTest, commit_inserts_the_leaves_a_block_creates)
{
    TrieDb tdb{this->db};
    commit_block_0(tdb);
    tdb.set_storage_filter(built_filter(this->db, tdb, 0));

    // Block 1: a new page (or slot) for ADDR_A, a slot on an existing page,
    // and a new account with storage
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {account, account},
                  .storage =
                      {{k_d, {bytes32_t{}, v3}}, {k_b, {bytes32_t{}, v3}}}}},
             {ADDR_B,
              StateDelta{
                  .account = {std::nullopt, account},
                  .storage = {{k_a, {bytes32_t{}, v2}}}}}}),
        Code{},
        BlockHeader{.number = 1});
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_d), v3);
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_b), v3);
    EXPECT_EQ(tdb.read_storage(ADDR_B, INC, k_a), v2);

    // Block 2: deleting leaves leaves them in the filter; reads still see the
    // deletion through the trie
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {account, account},
                  .storage =
                      {{k_d, {v3, bytes32_t{}}}, {k_c, {v2, bytes32_t{}}}}}}}),
        Code{},
        BlockHeader{.number = 2});
    uint64_t const finds = tdb.storage_read_count();
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_d), bytes32_t{});
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_c), bytes32_t{});
    EXPECT_EQ(tdb.storage_read_count(), finds + 2);
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_a), v1);
}

TYPED_TEST(StorageFilterTest, unused_until_ready_and_before_its_base_block)
{
    TrieDb tdb{this->db};
    commit_block_0(tdb);
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{.account = {account, account}, .storage = {}}}}),
        Code{},
        BlockHeader{.number = 1});

    auto filter =
        std::make_shared<StorageFilter>(SMALL, tdb.is_page_encoded(), 1);
    tdb.set_storage_filter(filter);
    uint64_t finds = tdb.storage_read_count();
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_d), bytes32_t{});
    EXPECT_EQ(tdb.storage_read_count(), ++finds);

    ASSERT_TRUE(insert_storage_leaves(*filter, this->db, tdb.get_root(), 1)
                    .has_value());
    filter->set_ready();
    EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_d), bytes32_t{});
    EXPECT_EQ(tdb.storage_read_count(), finds);

    // Block 0 is older than the filter's base block
    if (this->db.is_on_disk()) {
        tdb.set_block_and_prefix(0);
        EXPECT_EQ(tdb.read_storage(ADDR_A, INC, k_d), bytes32_t{});
        EXPECT_EQ(tdb.storage_read_count(), ++finds);
    }
}

TYPED_TEST(StorageFilterTest, save_and_load)
{
    TrieDb tdb{this->db};
    commit_block_0(tdb);
    auto const filter = built_filter(this->db, tdb, 0);
    auto const tag = finalized_storage_filter_tag(
        this->db, tdb.get_root(), 0, tdb.is_page_encoded());
    ASSERT_TRUE(tag.has_value());
    EXPECT_EQ(tag->state_root, tdb.state_root());

    auto const path = temp_path();
    ASSERT_TRUE(filter->save(path, tag.value()));
    EXPECT_FALSE(std::filesystem::exists(path.string() + ".tmp"));

    auto const loaded = StorageFilter::load(path, tag.value(), SMALL);
    ASSERT_NE(loaded, nullptr);
    EXPECT_TRUE(loaded->is_ready());
    EXPECT_EQ(loaded->base_block_number(), 0);
    EXPECT_EQ(loaded->is_page_encoded(), tdb.is_page_encoded());
    for (auto const &[addr, key] :
         {std::pair{ADDR_A, k_a},
          {ADDR_A, k_c},
          {ADDR_A, k_d},
          {ADDR_B, k_a}}) {
        bytes32_t const lookup =
            tdb.is_page_encoded() ? compute_page_key(key) : key;
        auto const a = keccak256({addr.bytes, sizeof(addr.bytes)});
        auto const k = keccak256({lookup.bytes, sizeof(lookup.bytes)});
        EXPECT_EQ(loaded->may_contain(a, k), filter->may_contain(a, k));
    }

    // Saved for another state, encoding or configuration
    auto other = tag.value();
    other.block_number = 1;
    EXPECT_EQ(StorageFilter::load(path, other, SMALL), nullptr);
    other = tag.value();
    other.state_root = NULL_ROOT;
    EXPECT_EQ(StorageFilter::load(path, other, SMALL), nullptr);
    other = tag.value();
    other.page_encoded = !other.page_encoded;
    EXPECT_EQ(StorageFilter::load(path, other, SMALL), nullptr);
    EXPECT_EQ(
        StorageFilter::load(
            path,
            tag.value(),
            {.size_bytes = SMALL.size_bytes, .num_probes = 5}),
        nullptr);
    EXPECT_EQ(
        StorageFilter::load(
            path,
            tag.value(),
            {.size_bytes = 2 * SMALL.size_bytes, .num_probes = 6}),
        nullptr);

    // A damaged file
    {
        std::fstream f{path, std::ios::in | std::ios::out | std::ios::binary};
        f.seekp(100);
        char c = 0;
        f.seekg(100);
        f.read(&c, 1);
        c = static_cast<char>(c ^ 0x5a);
        f.seekp(100);
        f.write(&c, 1);
    }
    EXPECT_EQ(StorageFilter::load(path, tag.value(), SMALL), nullptr);
    std::filesystem::resize_file(path, 1000);
    EXPECT_EQ(StorageFilter::load(path, tag.value(), SMALL), nullptr);
    std::filesystem::remove(path);
    EXPECT_EQ(StorageFilter::load(path, tag.value(), SMALL), nullptr);
}

TEST(StorageFilter, default_config)
{
    EXPECT_EQ(
        StorageFilter::default_config(true).size_bytes, size_t{512} << 20);
    EXPECT_EQ(StorageFilter::default_config(true).num_probes, 8);
    EXPECT_EQ(
        StorageFilter::default_config(false).size_bytes, size_t{2048} << 20);
    EXPECT_EQ(StorageFilter::default_config(false).num_probes, 6);
}

template <typename T>
struct StorageFilterBuildTest : public T
{
};

using FileDbTypes = ::testing::Types<
    OnDiskDbWithFileFixtureBase<OnDiskMachine>,
    OnDiskDbWithFileFixtureBase<MonadOnDiskMachine>>;
TYPED_TEST_SUITE(StorageFilterBuildTest, FileDbTypes);

TYPED_TEST(StorageFilterBuildTest, parallel_build_from_read_only_handles)
{
    TrieDb tdb{this->db};
    // 40 accounts with 3 slots each: on a page-encoded db, slots 1 and 2
    // share a page
    StateDeltas deltas;
    for (uint64_t i = 0; i < 40; ++i) {
        Address addr{};
        addr.bytes[19] = static_cast<uint8_t>(i + 1);
        deltas.emplace(
            addr,
            StateDelta{
                .account = {std::nullopt, account},
                .storage = {
                    {k_a, {bytes32_t{}, v1}},
                    {k_b, {bytes32_t{}, v2}},
                    {k_c, {bytes32_t{}, v3}}}});
    }
    commit_sequential(tdb, deltas, Code{}, BlockHeader{.number = 0});
    uint64_t const leaves = tdb.is_page_encoded() ? 2 * 40 : 3 * 40;

    for (unsigned const threads : {1u, 3u, 16u}) {
        StorageFilter filter{SMALL, tdb.is_page_encoded(), 0};
        EXPECT_EQ(
            build_storage_filter(filter, this->dbname, 0, threads), leaves)
            << threads << " threads";
        for (uint64_t i = 0; i < 40; ++i) {
            Address addr{};
            addr.bytes[19] = static_cast<uint8_t>(i + 1);
            auto const a = keccak256({addr.bytes, sizeof(addr.bytes)});
            for (auto const &key : {k_a, k_b, k_c}) {
                bytes32_t const lookup =
                    tdb.is_page_encoded() ? compute_page_key(key) : key;
                EXPECT_TRUE(filter.may_contain(
                    a, keccak256({lookup.bytes, sizeof(lookup.bytes)})));
            }
        }
    }
    // A version the db does not have
    StorageFilter filter{SMALL, tdb.is_page_encoded(), 0};
    EXPECT_EQ(build_storage_filter(filter, this->dbname, 7, 2), std::nullopt);
    EXPECT_EQ(
        finalized_storage_filter_tag(this->db, 7, tdb.is_page_encoded()),
        std::nullopt);
}

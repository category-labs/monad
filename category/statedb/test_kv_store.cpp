// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/byte_string.hpp>
#include <category/statedb/kv_store.hpp>
#include <category/statedb/schema.hpp>

#include <rocksdb/iterator.h>
#include <rocksdb/write_batch.h>

#include <gtest/gtest.h>

#include <array>
#include <filesystem>
#include <memory>
#include <span>
#include <string>
#include <string_view>

using namespace monad;
using namespace monad::statedb;

namespace
{
    byte_string_view bv(std::string_view const s) noexcept
    {
        return byte_string_view{
            reinterpret_cast<unsigned char const *>(s.data()), s.size()};
    }

    byte_string bs(std::string_view const s)
    {
        return byte_string{
            reinterpret_cast<unsigned char const *>(s.data()), s.size()};
    }

    struct KvStoreTest : public ::testing::Test
    {
        std::filesystem::path dir;
        std::unique_ptr<KvStore> kv;

        void SetUp() override
        {
            auto const *const info =
                ::testing::UnitTest::GetInstance()->current_test_info();
            dir = std::filesystem::temp_directory_path() /
                  (std::string{"monad_kvstore_"} + info->test_suite_name() +
                   "_" + info->name());
            std::filesystem::remove_all(dir);
            kv = KvStore::open(dir);
        }

        void TearDown() override
        {
            kv.reset();
            std::filesystem::remove_all(dir);
        }
    };
}

TEST_F(KvStoreTest, put_get_erase)
{
    EXPECT_FALSE(kv->get(Cf::flat_state, bv("a")).has_value());
    kv->put(Cf::flat_state, bv("a"), bv("1"));
    auto const v = kv->get(Cf::flat_state, bv("a"));
    ASSERT_TRUE(v.has_value());
    EXPECT_EQ(*v, bs("1"));
    kv->erase(Cf::flat_state, bv("a"));
    EXPECT_FALSE(kv->get(Cf::flat_state, bv("a")).has_value());
}

TEST_F(KvStoreTest, column_families_are_isolated)
{
    kv->put(Cf::flat_state, bv("k"), bv("flat"));
    kv->put(Cf::code, bv("k"), bv("code"));
    EXPECT_EQ(*kv->get(Cf::flat_state, bv("k")), bs("flat"));
    EXPECT_EQ(*kv->get(Cf::code, bv("k")), bs("code"));
}

TEST_F(KvStoreTest, multi_get_reports_misses_in_order)
{
    kv->put(Cf::trie_nodes, bv("x"), bv("X"));
    kv->put(Cf::trie_nodes, bv("z"), bv("Z"));
    std::array<byte_string_view, 3> const keys{bv("x"), bv("y"), bv("z")};
    auto const got = kv->multi_get(Cf::trie_nodes, keys);
    ASSERT_EQ(got.size(), 3u);
    ASSERT_TRUE(got[0].has_value());
    EXPECT_EQ(*got[0], bs("X"));
    EXPECT_FALSE(got[1].has_value());
    ASSERT_TRUE(got[2].has_value());
    EXPECT_EQ(*got[2], bs("Z"));
}

TEST_F(KvStoreTest, write_batch_is_atomic_across_cfs)
{
    rocksdb::WriteBatch batch;
    kv->batch_put(batch, Cf::flat_state, bv("acct"), bv("v1"));
    kv->batch_put(batch, Cf::meta, bv("finalized"), bv("100"));
    kv->write(batch);
    EXPECT_EQ(*kv->get(Cf::flat_state, bv("acct")), bs("v1"));
    EXPECT_EQ(*kv->get(Cf::meta, bv("finalized")), bs("100"));
}

TEST_F(KvStoreTest, snapshot_pins_a_consistent_view)
{
    kv->put(Cf::flat_state, bv("k"), bv("old"));
    auto const *const snap = kv->take_snapshot();
    kv->put(Cf::flat_state, bv("k"), bv("new"));
    EXPECT_EQ(*kv->get(Cf::flat_state, bv("k"), snap), bs("old"));
    EXPECT_EQ(*kv->get(Cf::flat_state, bv("k")), bs("new"));
    kv->release(snap);
}

TEST_F(KvStoreTest, iterator_scans_one_cf_in_key_order)
{
    kv->put(Cf::code, bv("b"), bv("2"));
    kv->put(Cf::code, bv("a"), bv("1"));
    kv->put(Cf::code, bv("c"), bv("3"));
    auto it = kv->new_iterator(Cf::code);
    std::string keys;
    for (it->SeekToFirst(); it->Valid(); it->Next()) {
        keys += it->key().ToString();
    }
    EXPECT_EQ(keys, "abc");
}

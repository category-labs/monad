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
#include <category/core/bytes.hpp>
#include <category/statedb/kv_store.hpp>
#include <category/statedb/trie_node_store.hpp>

#include <rocksdb/write_batch.h>

#include <gtest/gtest.h>

#include <filesystem>
#include <memory>
#include <string>
#include <string_view>

using namespace monad;
using namespace monad::statedb;

namespace
{
    byte_string bs(std::string_view const s)
    {
        return byte_string{
            reinterpret_cast<unsigned char const *>(s.data()), s.size()};
    }

    // A distinct node_hash per small integer.
    bytes32_t node_hash(unsigned char const n)
    {
        bytes32_t h{};
        h.bytes[31] = n;
        return h;
    }

    struct TrieNodeStoreTest : public ::testing::Test
    {
        std::filesystem::path dir;
        std::unique_ptr<KvStore> kv;

        void SetUp() override
        {
            auto const *const info =
                ::testing::UnitTest::GetInstance()->current_test_info();
            dir = std::filesystem::temp_directory_path() /
                  (std::string{"monad_trienode_"} + info->test_suite_name() +
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

TEST_F(TrieNodeStoreTest, put_then_get)
{
    TrieNodeStore store{*kv, 16};
    EXPECT_FALSE(store.get(node_hash(1)).has_value());
    store.put(node_hash(1), bs("node-one"));
    auto const v = store.get(node_hash(1));
    ASSERT_TRUE(v.has_value());
    EXPECT_EQ(*v, bs("node-one"));
}

TEST_F(TrieNodeStoreTest, reads_through_to_disk_on_cold_cache)
{
    {
        TrieNodeStore writer{*kv, 16};
        writer.put(node_hash(7), bs("persisted"));
    }
    // A fresh store has an empty LRU, so this must read CF_TRIE_NODES and strip
    // the [version][prune_epoch] frame.
    TrieNodeStore reader{*kv, 16};
    auto const v = reader.get(node_hash(7));
    ASSERT_TRUE(v.has_value());
    EXPECT_EQ(*v, bs("persisted"));
}

TEST_F(TrieNodeStoreTest, eviction_falls_back_to_disk)
{
    TrieNodeStore store{*kv, 2}; // tiny LRU
    store.put(node_hash(1), bs("a"));
    store.put(node_hash(2), bs("b"));
    store.put(node_hash(3), bs("c")); // evicts node 1 from the LRU
    // Node 1 is gone from the cache but still on disk.
    auto const v = store.get(node_hash(1));
    ASSERT_TRUE(v.has_value());
    EXPECT_EQ(*v, bs("a"));
}

TEST_F(TrieNodeStoreTest, batch_put_visible_in_cache_and_after_write)
{
    TrieNodeStore store{*kv, 16};
    rocksdb::WriteBatch batch;
    store.batch_put(batch, node_hash(5), bs("batched"));
    // batch_put warms the LRU immediately, before the batch is committed.
    auto const cached = store.get(node_hash(5));
    ASSERT_TRUE(cached.has_value());
    EXPECT_EQ(*cached, bs("batched"));
    kv->write(batch);
    // After commit, a fresh store reads it from disk.
    TrieNodeStore reader{*kv, 16};
    auto const v = reader.get(node_hash(5));
    ASSERT_TRUE(v.has_value());
    EXPECT_EQ(*v, bs("batched"));
}

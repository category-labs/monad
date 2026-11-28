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

#include "test_fixtures_base.hpp"

#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/recent_node_cache.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/update.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

using namespace ::monad;
using namespace ::monad::mpt;
using namespace ::monad::test;

namespace
{
    // The first prefix_len nibbles are in cache() and name a section, like
    // the proposal and finalized prefixes; everything below is a
    // cache_recent() position.
    class RecentMachine final : public StateMachine
    {
        size_t prefix_len_;
        size_t depth_{0};

    public:
        explicit RecentMachine(size_t const prefix_len)
            : prefix_len_{prefix_len}
        {
        }

        std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<RecentMachine>(*this);
        }

        void down(unsigned char) override
        {
            ++depth_;
        }

        void up(size_t const n) override
        {
            depth_ -= n;
        }

        Compute &get_compute() const override
        {
            static MerkleCompute compute{};
            return compute;
        }

        bool cache() const override
        {
            return depth_ <= prefix_len_;
        }

        bool cache_recent() const override
        {
            return depth_ > prefix_len_;
        }

        std::optional<size_t>
        recent_key_prefix_len(unsigned char) const override
        {
            return prefix_len_;
        }

        bool compact() const override
        {
            return true;
        }

        bool is_variable_length() const override
        {
            return false;
        }
    };

    auto const k1 = 0x10000000_bytes;
    auto const k2 = 0x20000000_bytes;
    auto const k3 = 0x30000000_bytes;
    auto const k11 = 0x11000000_bytes;
    auto const k12 = 0x12000000_bytes;

    struct RecentDb
    {
        Db db;
        Node::SharedPtr root;

        explicit RecentDb(
            RecentNodeCacheConfig const &config, size_t const prefix_len = 0)
            : db{std::make_unique<RecentMachine>(prefix_len),
                 OnDiskDbConfig{
                     .fixed_history_length = MPT_TEST_HISTORY_LENGTH,
                     .recent_node_cache = config}}
        {
        }

        explicit RecentDb(Db &&other)
            : db{std::move(other)}
        {
        }

        // The keys must outlive the call: the updates point into them.
        void write(
            uint64_t const version,
            std::initializer_list<byte_string const *> const keys)
        {
            std::vector<byte_string> values;
            std::vector<Update> storage;
            values.reserve(keys.size());
            storage.reserve(keys.size());
            UpdateList updates;
            for (byte_string const *const key : keys) {
                values.push_back(
                    *key + byte_string(1, static_cast<unsigned char>(version)));
                storage.push_back(make_update(
                    *key, values.back(), false, UpdateList{}, version));
                updates.push_front(storage.back());
            }
            root = db.upsert(std::move(root), std::move(updates), version);
        }

        // Whether every node down to `key` is in memory.
        bool resident(byte_string const &key) const
        {
            NibblesView const path{key};
            Node const *node = root.get();
            unsigned i = node->path_nibbles_len();
            while (i < path.nibble_size()) {
                unsigned char const branch = path.get(i);
                if ((node->mask & (1u << branch)) == 0) {
                    return false;
                }
                Node const *const child =
                    node->next(node->to_child_index(branch)).get();
                if (child == nullptr) {
                    return false;
                }
                i += 1 + child->path_nibbles_len();
                node = child;
            }
            return true;
        }

        bool reads_back(byte_string const &key, uint64_t const version)
        {
            // The first byte may name the section the value was written in.
            auto const res = db.find(root, key, version);
            return res.has_value() && res.value().node->value().substr(
                                          1, key.size() - 1) == key.substr(1);
        }
    };

    // At version 1: `account` with one storage slot, k1, then `other` and
    // k3. `account` and `other` share their first nibble, 1. The slot's value
    // makes the storage node larger than the account's node.
    void write_accounts(
        RecentDb &t, byte_string const &account, byte_string const &other)
    {
        auto const value = 0xaa_bytes;
        byte_string const slot_value(256, 0xaa);
        UpdateList storage;
        Update s1 = make_update(k1, slot_value, false, UpdateList{}, 1);
        storage.push_front(s1);
        UpdateList updates;
        Update u1 = make_update(account, value, false, std::move(storage), 1);
        Update u2 = make_update(other, value, false, UpdateList{}, 1);
        Update u3 = make_update(k3, value, false, UpdateList{}, 1);
        updates.push_front(u1);
        updates.push_front(u2);
        updates.push_front(u3);
        t.root = t.db.upsert(std::move(t.root), std::move(updates), 1);
    }

    // Of the account's node and of its storage node, as write_accounts
    // writes them; `account` continues with nibble 0.
    std::pair<size_t, size_t>
    account_bytes(byte_string const &account, byte_string const &other)
    {
        RecentDb probe{{.window_versions = 100}, 1};
        write_accounts(probe, account, other);
        Node const &branch = *probe.root->next(probe.root->to_child_index(1));
        Node const &leaf = *branch.next(branch.to_child_index(0));
        return {leaf.get_mem_size(), leaf.next(0)->get_mem_size()};
    }

    // Of a leaf the tests write; all of them are the same size.
    size_t leaf_bytes()
    {
        RecentDb probe{{.window_versions = 100}};
        probe.write(1, {&k1, &k2});
        return probe.root->next(probe.root->to_child_index(1))->get_mem_size();
    }
}

TEST(RecentNodeCache, disabled_frees_written_nodes)
{
    RecentDb t{{}};
    t.write(1, {&k1, &k2});
    EXPECT_FALSE(t.resident(k1));
    EXPECT_FALSE(t.resident(k2));
}

TEST(RecentNodeCache, keeps_written_nodes_for_the_window)
{
    RecentDb t{{.window_versions = 4}};
    t.write(1, {&k1, &k2});
    for (uint64_t v = 2; v <= 4; ++v) {
        t.write(v, {&k3});
    }
    EXPECT_TRUE(t.resident(k1));
    EXPECT_TRUE(t.resident(k2));

    t.write(5, {&k3});
    EXPECT_FALSE(t.resident(k1));
    EXPECT_FALSE(t.resident(k2));
    EXPECT_TRUE(t.resident(k3));
    EXPECT_TRUE(t.reads_back(k1, 5));
    EXPECT_TRUE(t.reads_back(k2, 5));
}

TEST(RecentNodeCache, rewritten_node_stays_for_its_later_version)
{
    RecentDb t{{.window_versions = 2}};
    t.write(1, {&k1});
    t.write(2, {&k1});
    t.write(3, {&k3});
    EXPECT_TRUE(t.resident(k1));

    t.write(4, {&k3});
    EXPECT_FALSE(t.resident(k1));
    EXPECT_TRUE(t.reads_back(k1, 4));
}

TEST(RecentNodeCache, old_sibling_under_rewritten_parent_leaves_on_time)
{
    RecentDb t{{.window_versions = 2}};
    t.write(1, {&k11, &k12});
    t.write(2, {&k11});
    t.write(3, {&k11});
    EXPECT_FALSE(t.resident(k12));
    EXPECT_TRUE(t.resident(k11));
    EXPECT_TRUE(t.reads_back(k12, 3));
}

TEST(RecentNodeCache, evicts_nodes_a_find_attached)
{
    RecentDb t{{.window_versions = 2}};
    t.write(1, {&k1, &k2});
    t.write(2, {&k3});
    t.write(3, {&k3});
    ASSERT_FALSE(t.resident(k1));
    ASSERT_TRUE(t.reads_back(k1, 3));
    EXPECT_TRUE(t.resident(k1));

    t.write(4, {&k3});
    EXPECT_TRUE(t.resident(k1));
    t.write(5, {&k3});
    EXPECT_FALSE(t.resident(k1));
    EXPECT_TRUE(t.resident(k3));
}

// k11 is moved below a new branch when k12 splits its path.
TEST(RecentNodeCache, node_moved_by_a_split_stays_for_its_version)
{
    RecentDb t{{.window_versions = 4}};
    t.write(1, {&k11, &k3});
    t.write(2, {&k12});
    EXPECT_TRUE(t.resident(k11));
    EXPECT_TRUE(t.resident(k12));

    for (uint64_t v = 3; v <= 5; ++v) {
        t.write(v, {&k3});
    }
    EXPECT_FALSE(t.resident(k11));
    EXPECT_TRUE(t.resident(k12));
    EXPECT_TRUE(t.reads_back(k11, 5));
}

// a1 has an empty path, so a cursor at it has prefix_index 0.
TEST(RecentNodeCache, finds_from_a_subtrie_do_not_attach)
{
    RecentDb t{{.window_versions = 2}};
    auto const a1 = 0x10_bytes;
    auto const a2 = 0x11_bytes;
    auto const value = 0xaa_bytes;
    {
        UpdateList storage;
        Update s1 = make_update(k1, value, false, UpdateList{}, 1);
        storage.push_front(s1);
        UpdateList accounts;
        Update u1 = make_update(a1, value, false, std::move(storage), 1);
        Update u2 = make_update(a2, value, false, UpdateList{}, 1);
        accounts.push_front(u1);
        accounts.push_front(u2);
        t.root = t.db.upsert(std::move(t.root), std::move(accounts), 1);
    }
    t.write(2, {&k3});
    t.write(3, {&k3});
    ASSERT_FALSE(t.resident(a1));

    auto const account = t.db.find(t.root, a1, 3);
    ASSERT_TRUE(account.has_value());
    ASSERT_EQ(account.value().prefix_index, 0);
    ASSERT_TRUE(t.db.find(account.value(), k1, 3).has_value());
    Node const &node = *account.value().node;
    EXPECT_EQ(node.next(node.to_child_index(1)), nullptr);
}

// Only primary-timeline upserts walk recorded keys.
TEST(RecentNodeCache, finds_on_the_secondary_timeline_do_not_attach)
{
    RecentDb t{{.window_versions = 4}};
    t.write(1, {&k3});
    RecentDb s{
        t.db.activate_secondary_timeline(std::make_unique<RecentMachine>(0))};
    s.write(1, {&k1, &k2});
    ASSERT_FALSE(s.resident(k1));
    ASSERT_TRUE(s.reads_back(k1, 1));
    EXPECT_FALSE(s.resident(k1));
}

TEST(RecentNodeCache, finds_over_the_key_budget_do_not_attach)
{
    RecentDb t{{.window_versions = 4, .max_keys_per_version = 2}};
    t.write(1, {&k1, &k2, &k3});
    ASSERT_FALSE(t.resident(k1));
    ASSERT_TRUE(t.reads_back(k1, 1));
    ASSERT_TRUE(t.reads_back(k2, 1));
    ASSERT_TRUE(t.reads_back(k3, 1));
    EXPECT_TRUE(t.resident(k1));
    EXPECT_TRUE(t.resident(k2));
    EXPECT_FALSE(t.resident(k3));
}

// Each leaf's path starts inside the two-nibble recorded-key prefix and
// ends below it.
TEST(RecentNodeCache, node_crossing_the_key_prefix_leaves_on_time)
{
    RecentDb t{{.window_versions = 2}, 2};
    auto const x = 0x00100000_bytes;
    auto const y = 0x10100000_bytes;
    t.write(1, {&x, &y});
    t.write(2, {&y});
    t.write(3, {&y});
    EXPECT_FALSE(t.resident(x));
    EXPECT_TRUE(t.resident(y));
    EXPECT_TRUE(t.reads_back(x, 3));
}

// Execution writes each block under a new proposal prefix, which copy_trie
// makes share the previous proposal's subtrie.
TEST(RecentNodeCache, keys_follow_the_subtrie_to_a_new_prefix)
{
    RecentDb t{{.window_versions = 2}, 2};
    auto const p1 = 0x01_bytes;
    auto const p2 = 0x02_bytes;
    auto const p3 = 0x03_bytes;
    auto const p1k1 = p1 + k1;
    auto const p1k2 = p1 + k2;
    auto const p2k2 = p2 + k2;
    auto const p3k3 = p3 + k3;
    auto const p3k1 = p3 + k1;
    auto const p3k2 = p3 + k2;

    t.write(1, {&p1k1, &p1k2});
    t.root = t.db.copy_trie(
        t.root, NibblesView{p1}, nullptr, NibblesView{p2}, 2, false);
    t.write(2, {&p2k2});
    t.root = t.db.copy_trie(
        t.root, NibblesView{p2}, nullptr, NibblesView{p3}, 3, false);
    ASSERT_TRUE(t.resident(p3k1));
    t.write(3, {&p3k3});
    EXPECT_FALSE(t.resident(p3k1));
    EXPECT_TRUE(t.resident(p3k2));
    EXPECT_TRUE(t.resident(p3k3));
    EXPECT_TRUE(t.reads_back(p3k1, 3));
}

TEST(RecentNodeCache, an_upsert_over_the_key_budget_keeps_none_of_its_nodes)
{
    RecentDb t{{.window_versions = 4, .max_keys_per_version = 2}};
    t.write(1, {&k1, &k2, &k3});
    EXPECT_FALSE(t.resident(k1));
    EXPECT_FALSE(t.resident(k2));
    EXPECT_FALSE(t.resident(k3));
}

// Like a snapshot load, which writes all its batches at one version.
TEST(RecentNodeCache, upserts_at_one_version_share_its_key_budget)
{
    RecentDb t{{.window_versions = 4, .max_keys_per_version = 2}};
    t.write(1, {&k1, &k2});
    t.write(1, {&k3});
    EXPECT_TRUE(t.resident(k1));
    EXPECT_TRUE(t.resident(k2));
    EXPECT_FALSE(t.resident(k3));

    t.write(2, {&k3});
    EXPECT_TRUE(t.resident(k3));
}

TEST(RecentNodeCache, byte_bound_holds_across_upserts_at_one_version)
{
    RecentDb t{
        {.window_versions = 4, .max_bytes = leaf_bytes() + leaf_bytes() / 2}};
    t.write(1, {&k1});
    t.write(1, {&k2});
    EXPECT_TRUE(t.resident(k1));
    EXPECT_FALSE(t.resident(k2));
    EXPECT_TRUE(t.reads_back(k2, 1));
}

// An account-only write reads the account's only storage node back, and
// keeping the account keeps that node too.
TEST(RecentNodeCache, byte_bound_counts_the_only_child_a_kept_leaf_holds)
{
    auto const account = 0x10_bytes;
    auto const other = 0x11_bytes;
    auto const [account_size, slot_size] = account_bytes(account, other);
    RecentDb t{
        {.window_versions = 2, .max_bytes = account_size + slot_size / 2}, 1};
    write_accounts(t, account, other);
    t.write(2, {&k3});
    t.write(3, {&k3});
    ASSERT_FALSE(t.resident(account));

    t.write(4, {&account});
    EXPECT_FALSE(t.resident(account));
}

// The account and its only storage node are in memory, by a find, when the
// account is written again.
TEST(RecentNodeCache, byte_bound_counts_a_resident_only_child_on_a_rewrite)
{
    auto const account = 0x10_bytes;
    auto const other = 0x11_bytes;
    auto const [account_size, slot_size] = account_bytes(account, other);
    RecentDb t{
        {.window_versions = 2, .max_bytes = account_size + slot_size / 2}, 1};
    write_accounts(t, account, other);
    t.write(2, {&k3});
    t.write(3, {&k3});
    ASSERT_FALSE(t.resident(account));
    auto const slot = account + k1;
    ASSERT_TRUE(t.db.find(t.root, slot, 3).has_value());
    ASSERT_TRUE(t.resident(slot));

    t.write(4, {&account});
    EXPECT_FALSE(t.resident(account));
}

// `sibling` splits the account's path, which moves the account, with its
// only storage node in memory by a find, below a new branch. Recorded keys
// start at nibble 3, so that new branch is in cache() and only the moved
// account is charged.
TEST(RecentNodeCache, byte_bound_counts_the_only_child_of_a_moved_leaf)
{
    auto const account = 0x1000_bytes;
    auto const other = 0x1100_bytes;
    auto const sibling = 0x1010_bytes;
    auto const [account_size, slot_size] = account_bytes(account, other);
    RecentDb t{
        {.window_versions = 4, .max_bytes = account_size + slot_size / 2}, 3};
    write_accounts(t, account, other);
    ASSERT_FALSE(t.resident(account));
    auto const slot = account + k1;
    ASSERT_TRUE(t.db.find(t.root, slot, 1).has_value());
    ASSERT_TRUE(t.resident(slot));

    t.write(2, {&sibling});
    EXPECT_FALSE(t.resident(account));
}

TEST(RecentNodeCache, byte_bound_evicts_oldest_first)
{
    RecentDb t{
        {.window_versions = 3,
         .max_bytes = 2 * leaf_bytes() + leaf_bytes() / 2}};
    t.write(1, {&k1});
    t.write(2, {&k2});
    EXPECT_TRUE(t.resident(k1));
    EXPECT_TRUE(t.resident(k2));
    t.write(3, {&k3});
    EXPECT_FALSE(t.resident(k1));
    EXPECT_TRUE(t.resident(k2));
    EXPECT_TRUE(t.resident(k3));
    EXPECT_TRUE(t.reads_back(k1, 3));
}

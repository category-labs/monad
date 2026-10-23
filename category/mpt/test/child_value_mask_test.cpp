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

#include "child_value_mask_checker.hpp"
#include "test_fixtures_base.hpp"

#include <category/core/byte_string.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/update.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <deque>
#include <map>
#include <random>
#include <set>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test;

namespace
{
    // Only the root level stays cached, so most children are carried over
    // from disk unread.
    using Machine =
        StateMachineAlways<EmptyCompute, StateMachineConfig{.cache_depth = 1}>;

    // Outer keys carry a value and, like accounts with storage, may hold an
    // inner trie, so branches can have values. Keys share most nibbles.
    template <class Base>
    struct ChildValueMaskFixture : public Base
    {
        Machine sm;
        uint64_t version{0};
        std::map<byte_string, std::set<byte_string>> live;

        struct OuterOp
        {
            byte_string key;
            bool erase{false};
            std::vector<std::pair<byte_string, bool>> inner; // key, erase
        };

        void apply(std::vector<OuterOp> const &ops)
        {
            std::deque<Update> updates;
            std::deque<byte_string> values;
            UpdateList outer;
            for (auto const &op : ops) {
                if (op.erase) {
                    outer.push_front(updates.emplace_back(make_erase(op.key)));
                    live.erase(op.key);
                    continue;
                }
                auto &inner_keys = live[op.key];
                UpdateList inner;
                for (auto const &[key, erase] : op.inner) {
                    if (erase) {
                        inner.push_front(updates.emplace_back(make_erase(key)));
                        inner_keys.erase(key);
                    }
                    else {
                        values.emplace_back(key.size() + version % 2, 0xcd);
                        inner.push_front(updates.emplace_back(
                            make_update(key, values.back())));
                        inner_keys.insert(key);
                    }
                }
                values.emplace_back(version % 3, 0xab);
                outer.push_front(updates.emplace_back(make_update(
                    op.key, values.back(), false, std::move(inner))));
            }
            this->root = upsert(
                this->aux,
                version,
                sm,
                std::move(this->root),
                std::move(outer),
                true,
                timeline_id::primary);
            if (this->root) {
                ++version;
            }
        }

        // Returns how many children were checked.
        size_t expect_masks_consistent()
        {
            if (!this->root) {
                return 0;
            }
            ChildValueMaskChecker checker;
            EXPECT_TRUE(preorder_traverse_blocking(
                this->aux, *this->root, checker, version - 1));
            EXPECT_EQ(checker.mismatches, 0u);
            return checker.children_checked;
        }
    };

    byte_string random_key(std::mt19937_64 &rng)
    {
        byte_string key(2, 0);
        for (auto &b : key) {
            b = static_cast<unsigned char>(rng() % 3);
        }
        return key;
    }
}

template <typename F>
struct ChildValueMaskTest : public F
{
};

using ChildValueMaskFixtures = ::testing::Types<
    ChildValueMaskFixture<InMemoryTrieBase<::testing::Test>>,
    ChildValueMaskFixture<OnDiskTrieBase<::testing::Test>>>;
TYPED_TEST_SUITE(ChildValueMaskTest, ChildValueMaskFixtures);

TYPED_TEST(ChildValueMaskTest, follows_children_through_updates_and_erases)
{
    std::mt19937_64 rng{9};
    size_t checked = 0;
    for (int batch = 0; batch < 40; ++batch) {
        std::map<byte_string, typename TypeParam::OuterOp> ops;
        for (int i = 0; i < 4; ++i) {
            auto const key = random_key(rng);
            auto &op = ops[key];
            op.key = key;
            auto const it = this->live.find(key);
            if (it != this->live.end() && rng() % 4 == 0) {
                op.erase = true;
                continue;
            }
            std::map<byte_string, bool> inner;
            for (uint64_t n = rng() % 4; n > 0; --n) {
                inner[random_key(rng)] = false;
            }
            if (it != this->live.end()) {
                for (auto const &k : it->second) {
                    if (rng() % 3 == 0) {
                        inner[k] = true;
                    }
                }
            }
            op.inner.assign(inner.begin(), inner.end());
        }
        std::vector<typename TypeParam::OuterOp> batch_ops;
        batch_ops.reserve(ops.size());
        for (auto &[k, op] : ops) {
            batch_ops.push_back(std::move(op));
        }
        this->apply(batch_ops);
        checked += this->expect_masks_consistent();
    }
    EXPECT_GT(checked, 400u);
}

TYPED_TEST(ChildValueMaskTest, value_bearing_branch_loses_and_gains_children)
{
    using Op = typename TypeParam::OuterOp;
    byte_string const outer_a{0x01, 0x02};
    byte_string const outer_b{0x01, 0x03};
    byte_string const inner_x{0x00, 0x01};
    byte_string const inner_y{0x00, 0x02};
    this->apply(
        {Op{.key = outer_a, .inner = {{inner_x, false}, {inner_y, false}}},
         Op{.key = outer_b, .inner = {}}});
    EXPECT_GT(this->expect_masks_consistent(), 0u);
    this->apply({Op{.key = outer_a, .inner = {{inner_x, true}}}});
    this->expect_masks_consistent();
    this->apply({Op{.key = outer_b, .erase = true, .inner = {}}});
    this->expect_masks_consistent();
    this->apply({Op{.key = outer_a, .inner = {{inner_y, true}}}});
    this->expect_masks_consistent();
}

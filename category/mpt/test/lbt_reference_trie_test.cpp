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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/mpt/lbt/commit.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/test/lbt_test_support.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <random>
#include <vector>

using namespace monad;
using namespace monad::mpt;
using namespace monad::mpt::lbt;
using namespace monad::test;

namespace
{
    NibblesView nibbles(bytes32_t const &k)
    {
        return NibblesView{byte_string_view{k.bytes, sizeof(k.bytes)}};
    }

    bytes32_t key_with_nibbles(std::initializer_list<uint8_t> const prefix)
    {
        bytes32_t k{};
        unsigned i = 0;
        for (auto const n : prefix) {
            k.bytes[i / 2] |= static_cast<uint8_t>(i % 2 == 0 ? n << 4 : n);
            ++i;
        }
        return k;
    }
}

TEST(LbtReferenceTrie, empty_root_is_zero)
{
    ReferenceTrie const t;
    EXPECT_EQ(t.root(), bytes32_t{});
    EXPECT_EQ(t.size(), 0u);
}

TEST(LbtReferenceTrie, single_key_root_is_its_leaf)
{
    ReferenceTrie t;
    auto const k = key_with_nibbles({0xa, 0x3});
    t.upsert(k, bytes32_t{7});
    EXPECT_EQ(t.root(), commit_leaf(nibbles(k), bytes32_t{7}).hash());
}

TEST(LbtReferenceTrie, history_independent)
{
    std::mt19937_64 rng{7};
    std::vector<bytes32_t> keys;
    for (int i = 0; i < 300; ++i) {
        bytes32_t k;
        for (auto &byte : k.bytes) {
            byte = static_cast<uint8_t>(rng());
        }
        keys.push_back(k);
    }
    ReferenceTrie forward;
    ReferenceTrie shuffled;
    ReferenceTrie survivors;
    auto order = keys;
    std::ranges::shuffle(order, rng);
    for (auto const &k : keys) {
        forward.upsert(k, bytes32_t{k.bytes[0]});
    }
    for (auto const &k : order) {
        shuffled.upsert(k, bytes32_t{k.bytes[0]});
    }
    EXPECT_EQ(forward.root(), shuffled.root());
    for (size_t i = 0; i < 100; ++i) {
        forward.erase(keys[i]);
    }
    for (size_t i = 100; i < keys.size(); ++i) {
        survivors.upsert(keys[i], bytes32_t{keys[i].bytes[0]});
    }
    EXPECT_EQ(forward.root(), survivors.root());
    EXPECT_EQ(forward.size(), 200u);
}

TEST(LbtReferenceTrie, erase_collapses_chain_back_to_leaf)
{
    ReferenceTrie t;
    ReferenceTrie only_a;
    auto const a = key_with_nibbles({0x5, 0x6, 0x7, 0x1});
    auto const b = key_with_nibbles({0x5, 0x6, 0x7, 0x2});
    t.upsert(a, bytes32_t{1});
    t.upsert(b, bytes32_t{2});
    t.erase(b);
    only_a.upsert(a, bytes32_t{1});
    EXPECT_EQ(t.root(), only_a.root());
}

TEST(LbtReferenceTrie, update_changes_root_and_same_value_does_not)
{
    ReferenceTrie t;
    auto const k = key_with_nibbles({0x2});
    t.upsert(k, bytes32_t{1});
    auto const r1 = t.root();
    t.upsert(k, bytes32_t{1});
    EXPECT_EQ(t.root(), r1);
    t.upsert(k, bytes32_t{2});
    EXPECT_NE(t.root(), r1);
}

TEST(LbtReferenceTrie, splits_on_first_differing_bit)
{
    ReferenceTrie t;
    auto const a = key_with_nibbles({0x1});
    auto const b = key_with_nibbles({0x9});
    t.upsert(a, bytes32_t{1});
    t.upsert(b, bytes32_t{2});
    auto const la = commit_leaf(nibbles(a), bytes32_t{1});
    auto const lb = commit_leaf(nibbles(b), bytes32_t{2});
    EXPECT_EQ(t.root(), merge(la, lb).hash());
}

TEST(LbtReferenceTrie, hashes_shared_bits_one_sided)
{
    // 0x1 = 0b0001 and 0x3 = 0b0011 share their first two bits.
    ReferenceTrie t;
    auto const a = key_with_nibbles({0x1});
    auto const b = key_with_nibbles({0x3});
    t.upsert(a, bytes32_t{1});
    t.upsert(b, bytes32_t{2});
    auto const la = commit_leaf(nibbles(a), bytes32_t{1});
    auto const lb = commit_leaf(nibbles(b), bytes32_t{2});
    auto const bit1 = merge_one_sided(merge(la, lb), false);
    EXPECT_EQ(t.root(), merge_one_sided(bit1, false).hash());
}

TEST(LbtReferenceTrie, leaf_binds_bits_it_rose_over)
{
    // 0x0 and 0x1 both rise to prefix 0 beside 0x8; only the key differs.
    ReferenceTrie t0;
    ReferenceTrie t1;
    auto const b = key_with_nibbles({0x8});
    t0.upsert(key_with_nibbles({0x0, 0x5}), bytes32_t{1});
    t1.upsert(key_with_nibbles({0x1, 0x5}), bytes32_t{1});
    t0.upsert(b, bytes32_t{2});
    t1.upsert(b, bytes32_t{2});
    EXPECT_NE(t0.root(), t1.root());
}

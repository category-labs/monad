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
#include <category/core/hex.hpp>
#include <category/mpt/lbt/commit.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <random>
#include <span>
#include <vector>

using namespace monad;
using namespace monad::literals;
using namespace monad::mpt;
using namespace monad::mpt::lbt;

namespace
{
    // A change to any of these is a change of state commitment. The inputs
    // of FULL_BRANCH and WIDE_BRANCH also depend on libstdc++'s shuffle.
    constexpr bytes32_t PIN_LEAF_FOUR_NIBBLES{
        0x6692872a995746019c94ebabfc658cf4d12cfd0bde6fddc13b2664a1bdad05de_bytes32};
    constexpr bytes32_t PIN_VALUE_HASH_ABC{
        0x2bc58a3fdc84e69176225de537e7b44c85e40a0088ed3a630e86e4a9cf082f46_bytes32};
    constexpr bytes32_t PIN_FULL_BRANCH{
        0x97e60976c19222363dbc8132cbdf9c5babbd592e1903572b8b22e9a584f6f240_bytes32};
    constexpr bytes32_t PIN_ADJACENT_LEAVES{
        0x4f938848d6303057e9e451e967b71ca743c781713be57c1beed775f56d98226f_bytes32};
    constexpr bytes32_t PIN_ADJACENT_INTERNALS{
        0x4f938848d6303057e9e451e967b71ca743c781713be57c1beed775f56d98226f_bytes32};
    constexpr bytes32_t PIN_SPLIT_LEAVES{
        0xa58663aaf6fe6b296e882871d9e06ad1337735d7ae69e991fe31920ba3e46352_bytes32};
    constexpr bytes32_t PIN_LEAF_AND_INTERNAL{
        0x560dc61af53331ff48ab3540da34c6bd70e0da7d4bad3689624a60e0d44d212c_bytes32};
    constexpr bytes32_t PIN_LONE_INTERNAL{
        0xbba15e23fea0740dc7617b24fbff26e8c4d0df5a3ea2caf36c50e4033737968b_bytes32};
    constexpr bytes32_t PIN_WIDE_BRANCH{
        0x234ba8132c6e26b5614c8416caee1b80c63fe178c7b9198b28db07befae5d171_bytes32};
    constexpr bytes32_t PIN_PATH_ONE_UNIT{
        0xadcbb2b111be4aa1b7e8224dee70f6d0ff3b2c3743290da6e88d8b0f13d948e5_bytes32};
    constexpr bytes32_t PIN_PATH_TWO_UNITS{
        0x0fac11567adf8d5005c9ad8a14a11969538bfa1be7ed2b9a4b4b98b130cd8ac2_bytes32};
    constexpr bytes32_t PIN_FULL_KEY_LEAF{
        0x30e6da5c6136126d03e0e6c5f66d52a7eaa473f763170b8c81c033bef83a6d1e_bytes32};

    bytes32_t h(uint64_t const x)
    {
        return bytes32_t{x};
    }

    // Top-down over the index bits: a lone leaf rises, and any other lone
    // subtree is hashed against a zero sibling at every level it spans.
    Commitment ref_binary(std::span<Entry const> const entries, int const bit)
    {
        if (entries.size() == 1 && (bit < 0 || entries[0].child.is_leaf())) {
            return entries[0].child;
        }
        auto const split = std::ranges::find_if(entries, [bit](Entry const &e) {
            return ((e.index >> bit) & 1) != 0;
        });
        auto const n_left = static_cast<size_t>(split - entries.begin());
        if (n_left == 0 || n_left == entries.size()) {
            return merge_one_sided(ref_binary(entries, bit - 1), n_left == 0);
        }
        return merge(
            ref_binary(entries.first(n_left), bit - 1),
            ref_binary(entries.subspan(n_left), bit - 1));
    }

    Entry leaf_at(uint16_t const index, uint64_t const x)
    {
        return Entry{.index = index, .child = Commitment::leaf(h(x))};
    }

    Entry internal_at(uint16_t const index, uint64_t const x)
    {
        return Entry{.index = index, .child = Commitment::internal(h(x))};
    }

    // Each child is a random hash, a leaf when the hash is odd.
    std::vector<Entry> random_entries(
        std::mt19937_64 &rng, unsigned const index_bits, size_t const k)
    {
        std::vector<uint16_t> all(size_t{1} << index_bits);
        for (size_t i = 0; i < all.size(); ++i) {
            all[i] = static_cast<uint16_t>(i);
        }
        std::ranges::shuffle(all, rng);
        all.resize(k);
        std::ranges::sort(all);
        std::vector<Entry> entries;
        entries.reserve(k);
        for (auto const i : all) {
            auto const x = rng();
            entries.push_back(Entry{
                .index = i,
                .child = x % 2 ? Commitment::leaf(h(x))
                               : Commitment::internal(h(x))});
        }
        return entries;
    }

    void randomly_type(std::mt19937_64 &rng, std::vector<Entry> &entries)
    {
        for (auto &entry : entries) {
            entry.child = rng() % 2 ? Commitment::leaf(entry.child.hash())
                                    : Commitment::internal(entry.child.hash());
        }
    }

    // One 8-bit branch computed as a 4-bit branch over 4-bit branches.
    Commitment two_levels(std::span<Entry const> const entries)
    {
        std::vector<Entry> top;
        size_t i = 0;
        while (i < entries.size()) {
            auto const high = static_cast<uint16_t>(entries[i].index >> 4);
            std::vector<Entry> group;
            for (; i < entries.size() && entries[i].index >> 4 == high; ++i) {
                group.push_back(Entry{
                    .index = static_cast<uint16_t>(entries[i].index & 0xf),
                    .child = entries[i].child});
            }
            top.push_back(
                Entry{.index = high, .child = branch_commit<4>(group)});
        }
        return branch_commit<4>(top);
    }
}

TEST(LbtCommit, merge_hash_binds_order)
{
    EXPECT_EQ(detail::merge_hash(h(1), h(2)), detail::merge_hash(h(1), h(2)));
    EXPECT_NE(detail::merge_hash(h(1), h(2)), detail::merge_hash(h(2), h(1)));
}

TEST(LbtCommit, leaf_and_merge_domains_differ)
{
    byte_string const empty_key{};
    EXPECT_NE(
        detail::leaf_commit(NibblesView{empty_key}, h(1)),
        detail::merge_hash(bytes32_t{}, h(1)));
}

TEST(LbtCommit, leaf_commit_binds_key_length)
{
    // Same packed bytes (0x10), different nibble counts.
    byte_string const one_byte = 0x10_bytes;
    NibblesView const two_nibbles{one_byte};
    NibblesView const one_nibble = two_nibbles.substr(0, 1);
    EXPECT_NE(
        detail::leaf_commit(two_nibbles, h(7)),
        detail::leaf_commit(one_nibble, h(7)));
}

TEST(LbtCommit, leaf_commit_binds_value_and_key)
{
    byte_string const a = 0x12_bytes;
    byte_string const b = 0x13_bytes;
    EXPECT_NE(
        detail::leaf_commit(NibblesView{a}, h(1)),
        detail::leaf_commit(NibblesView{a}, h(2)));
    EXPECT_NE(
        detail::leaf_commit(NibblesView{a}, h(1)),
        detail::leaf_commit(NibblesView{b}, h(1)));
}

TEST(LbtCommit, leaf_and_value_pins)
{
    byte_string const key = 0x1234_bytes;
    byte_string const abc{'a', 'b', 'c'};
    EXPECT_EQ(
        detail::leaf_commit(NibblesView{key}, h(7)), PIN_LEAF_FOUR_NIBBLES);
    EXPECT_EQ(value_hash(abc), PIN_VALUE_HASH_ABC);
    byte_string full_key(32, 0);
    for (size_t i = 0; i < full_key.size(); ++i) {
        full_key[i] = static_cast<unsigned char>(i);
    }
    EXPECT_EQ(
        detail::leaf_commit(NibblesView{full_key}, h(7)), PIN_FULL_KEY_LEAF);
    EXPECT_EQ(
        commit_leaf(NibblesView{full_key}, h(7)),
        Commitment::leaf(PIN_FULL_KEY_LEAF));
}

TEST(LbtCommitment, type_is_carried_beside_the_hash)
{
    auto const h1 = h(0x1234);
    EXPECT_TRUE(Commitment::leaf(h1).is_leaf());
    EXPECT_FALSE(Commitment::internal(h1).is_leaf());
    EXPECT_EQ(Commitment::leaf(h1).hash(), h1);
    EXPECT_EQ(Commitment::internal(h1).hash(), h1);
    EXPECT_NE(Commitment::leaf(h1), Commitment::internal(h1));
    byte_string const data{h1.bytes, sizeof(h1.bytes)};
    EXPECT_EQ(Commitment::from_child_data(data, true), Commitment::leaf(h1));
    EXPECT_EQ(
        Commitment::from_child_data(data, false), Commitment::internal(h1));
}

TEST(LbtCommitmentDeathTest, child_data_must_be_32_bytes)
{
    byte_string const short_data(31, 0);
    EXPECT_DEATH((void)Commitment::from_child_data(short_data, false), "");
}

TEST(LbtCommitmentDeathTest, a_leaf_is_never_merged_one_sided)
{
    EXPECT_DEATH((void)merge_one_sided(Commitment::leaf(h(1)), true), "");
}

TEST(LbtBranchCommit, lone_leaf_rises_unchanged)
{
    std::vector<Entry> const leaf{leaf_at(11, 4)};
    EXPECT_EQ(branch_commit<4>(leaf), leaf[0].child);
}

TEST(LbtBranchCommit, branch_pins)
{
    std::mt19937_64 full_rng{3};
    auto const full = random_entries(full_rng, 4, 16);
    std::mt19937_64 wide_rng{45};
    auto wide = random_entries(wide_rng, 8, 100);
    randomly_type(wide_rng, wide);

    struct Case
    {
        char const *name;
        std::vector<Entry> entries;
        bytes32_t pin;
    };

    std::vector<Case> const cases{
        {"full", full, PIN_FULL_BRANCH},
        {"adjacent_leaves",
         {leaf_at(0, 1), leaf_at(1, 2)},
         PIN_ADJACENT_LEAVES},
        {"adjacent_internals",
         {internal_at(0, 1), internal_at(1, 2)},
         PIN_ADJACENT_INTERNALS},
        {"split_leaves", {leaf_at(0, 1), leaf_at(8, 2)}, PIN_SPLIT_LEAVES},
        {"leaf_and_internal",
         {leaf_at(0, 1), internal_at(8, 2)},
         PIN_LEAF_AND_INTERNAL},
        {"lone_internal", {internal_at(11, 4)}, PIN_LONE_INTERNAL},
    };
    for (auto const &c : cases) {
        EXPECT_EQ(branch_commit<4>(c.entries).hash(), c.pin) << c.name;
        EXPECT_EQ(ref_binary(c.entries, 3).hash(), c.pin) << c.name;
    }
    EXPECT_EQ(branch_commit<8>(wide).hash(), PIN_WIDE_BRANCH);
    EXPECT_EQ(ref_binary(wide, 7).hash(), PIN_WIDE_BRANCH);
}

TEST(LbtBranchCommit, batched_matches_scalar_reference)
{
    std::mt19937_64 rng{43};
    for (int trial = 0; trial < 500; ++trial) {
        auto e4 = random_entries(rng, 4, 1 + rng() % 16);
        randomly_type(rng, e4);
        ASSERT_EQ(branch_commit<4>(e4), ref_binary(e4, 3)) << trial;
        auto e8 = random_entries(rng, 8, 1 + rng() % 256);
        randomly_type(rng, e8);
        ASSERT_EQ(branch_commit<8>(e8), ref_binary(e8, 7)) << trial;
    }
}

TEST(LbtBranchCommit, grouping_does_not_change_the_commitment)
{
    std::mt19937_64 rng{44};
    for (int trial = 0; trial < 500; ++trial) {
        size_t const k = 1 + rng() % 256;
        auto e = random_entries(rng, 8, k);
        randomly_type(rng, e);
        ASSERT_EQ(two_levels(e), branch_commit<8>(e)) << "k=" << k;
    }
}

TEST(LbtCommitPath, hashes_each_bit_one_sided)
{
    byte_string const one_unit = 0x50_bytes;
    NibblesView const path = NibblesView{one_unit}.substr(0, 1);
    auto const x = Commitment::internal(h(9));
    auto const one_sided = [](Commitment const &c, bool const right) {
        return Commitment::internal(
            right ? detail::merge_hash(bytes32_t{}, c.hash())
                  : detail::merge_hash(c.hash(), bytes32_t{}));
    };
    // 0x5 = 0b0101, lowest bit first: right, left, right, left.
    auto const expected =
        one_sided(one_sided(one_sided(one_sided(x, true), false), true), false);
    EXPECT_EQ(commit_path(path, x), expected);
    EXPECT_EQ(commit_path(path, x).hash(), PIN_PATH_ONE_UNIT);
}

TEST(LbtCommitPath, goes_deepest_unit_first)
{
    byte_string const two_units = 0x12_bytes;
    auto const x = Commitment::internal(h(9));
    // Unit 0x2 = 0b0010, then unit 0x1 = 0b0001, lowest bit first.
    Commitment expected = x;
    for (bool const right :
         {false, true, false, false, true, false, false, false}) {
        expected = merge_one_sided(expected, right);
    }
    EXPECT_EQ(commit_path(NibblesView{two_units}, x), expected);
    EXPECT_EQ(
        commit_path(NibblesView{two_units}, x).hash(), PIN_PATH_TWO_UNITS);
}

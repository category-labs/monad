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
#include <category/mpt/lbt/compute.hpp>
#include <category/mpt/lbt/key_path.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;
using namespace monad::mpt;

namespace
{
    bytes32_t some_key()
    {
        bytes32_t k;
        for (unsigned i = 0; i < sizeof(k.bytes); ++i) {
            k.bytes[i] = static_cast<uint8_t>(0x9d * i + 0x31);
        }
        return k;
    }

    NibblesView nibbles(bytes32_t const &k)
    {
        return NibblesView{byte_string_view{k.bytes, sizeof(k.bytes)}};
    }
}

TEST(LbtKeyPath, view_reads_back_the_nibbles_set)
{
    auto const k = some_key();
    auto const key = nibbles(k);
    lbt::KeyPath p;
    for (unsigned i = 0; i < key.nibble_size(); ++i) {
        p.set(i, key.get(i));
    }
    EXPECT_EQ(p.view(0, 64), key);
    EXPECT_EQ(p.view(3, 64), key.substr(3));
    EXPECT_EQ(p.view(10, 21), key.substr(10, 11));
    EXPECT_EQ(p.view(7, 7).nibble_size(), 0u);
}

TEST(LbtKeyPath, set_after_up_overwrites_only_that_depth)
{
    lbt::KeyPath p;
    p.set(0, 0xa);
    p.set(1, 0xb);
    p.set(2, 0xc);
    p.set(1, 0x4);
    auto const v = p.view(0, 3);
    EXPECT_EQ(v.get(0), 0xa);
    EXPECT_EQ(v.get(1), 0x4);
    EXPECT_EQ(v.get(2), 0xc);
}

TEST(LbtKeyPath, deepest_state_depth_fits)
{
    lbt::KeyPath p;
    p.set(193, 0x7);
    EXPECT_EQ(p.view(193, 194).get(0), 0x7);
}

TEST(LbtKeyPath, bulk_set_matches_nibble_set)
{
    byte_string bytes(35, 0);
    for (unsigned i = 0; i < bytes.size(); ++i) {
        bytes[i] = static_cast<unsigned char>(0x5b * i + 0x17);
    }
    NibblesView const path = NibblesView{bytes}.substr(0, 70);
    for (unsigned const start : {0u, 1u, 2u, 7u, 66u}) {
        for (unsigned const split : {0u, 1u, 30u, 70u}) {
            lbt::KeyPath one_by_one;
            lbt::KeyPath bulk;
            // Stale nibbles from a deeper walk must be overwritten.
            for (unsigned i = 0; i < start + 70; ++i) {
                bulk.set(i, 0xf);
            }
            for (unsigned i = 0; i < start; ++i) {
                one_by_one.set(i, static_cast<unsigned char>(i % 16));
                bulk.set(i, static_cast<unsigned char>(i % 16));
            }
            for (unsigned i = 0; i < path.nibble_size(); ++i) {
                one_by_one.set(start + i, path.get(i));
            }
            bulk.set(start, path.substr(0, split));
            bulk.set(start + split, path.substr(split));
            EXPECT_EQ(bulk.view(0, start + 70), one_by_one.view(0, start + 70))
                << "start=" << start << " split=" << split;
        }
    }
}

TEST(LbtFullLeafKey, prefix_at_the_leaf_end_is_the_key)
{
    auto const k = some_key();
    auto const key = nibbles(k);
    Nibbles storage;
    EXPECT_EQ(lbt::full_leaf_key(key, key.substr(50), storage), key);
}

TEST(LbtFullLeafKey, lifted_leaf_joins_prefix_and_path)
{
    // A coalesced leaf that starts at nibble 15, hashed while the machine is
    // still at nibble 20.
    auto const k = some_key();
    auto const key = nibbles(k);
    Nibbles storage;
    EXPECT_EQ(
        lbt::full_leaf_key(key.substr(0, 20), key.substr(15), storage), key);
}

TEST(LbtFullLeafKey, root_leaf_path_is_the_key)
{
    auto const k = some_key();
    auto const key = nibbles(k);
    Nibbles storage;
    EXPECT_EQ(lbt::full_leaf_key(NibblesView{}, key, storage), key);
}

TEST(LbtFullLeafKeyDeathTest, prefix_disagreeing_with_the_path_aborts)
{
    auto const k = some_key();
    auto const key = nibbles(k);
    bytes32_t other = k;
    other.bytes[8] ^= 0x10;
    Nibbles storage;
    // Nibble 16 differs: the recorded prefix is not the leaf's key.
    EXPECT_DEATH(
        (void)lbt::full_leaf_key(
            key.substr(0, 20), nibbles(other).substr(15), storage),
        "");
}

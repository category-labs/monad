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

#include <category/execution/ethereum/db/storage_page.hpp>

#include <gtest/gtest.h>

using namespace monad;

namespace
{
    constexpr size_t ETH_SLOT_BITS = storage_page_t::SLOT_BITS; // 0
    constexpr uint8_t ETH_SLOT_MASK = storage_page_t::SLOT_MASK; // 0

    constexpr size_t MONAD_SLOT_BITS = 6;
    constexpr uint8_t MONAD_SLOT_MASK = 0x3F;
}

TEST(MonadDb, eth_key_grouping)
{
    // With SLOT_BITS=0 every key maps to its own page (identity)
    constexpr auto slot0 = bytes32_t{0x00};
    constexpr auto slot1 = bytes32_t{0x01};
    constexpr auto slot2 = bytes32_t{0xFF};

    // Each key is its own page key
    EXPECT_EQ(compute_page_key<ETH_SLOT_BITS>(slot0), slot0);
    EXPECT_EQ(compute_page_key<ETH_SLOT_BITS>(slot1), slot1);
    EXPECT_EQ(compute_page_key<ETH_SLOT_BITS>(slot2), slot2);

    // Offset is always 0
    EXPECT_EQ(compute_slot_offset<ETH_SLOT_MASK>(slot0), 0);
    EXPECT_EQ(compute_slot_offset<ETH_SLOT_MASK>(slot1), 0);
    EXPECT_EQ(compute_slot_offset<ETH_SLOT_MASK>(slot2), 0);

    // Round-trip: slot_key == compute_slot_key(page_key, 0)
    for (uint16_t i = 0; i < 256; ++i) {
        bytes32_t const slot_key = bytes32_t{i};
        bytes32_t const pk = compute_page_key<ETH_SLOT_BITS>(slot_key);
        uint8_t const off = compute_slot_offset<ETH_SLOT_MASK>(slot_key);
        EXPECT_EQ(pk, slot_key);
        EXPECT_EQ(off, 0);
        EXPECT_EQ(compute_slot_key<ETH_SLOT_BITS>(pk, off), slot_key);
    }
}

TEST(MonadDb, monad_key_grouping)
{
    // Keys 0x00..0x3F should all map to the same page (page_key = 0)
    bytes32_t const page_key_0 =
        compute_page_key<MONAD_SLOT_BITS>(bytes32_t{0});

    for (uint8_t i = 0; i < 64; ++i) {
        bytes32_t const slot_key = bytes32_t{i};
        EXPECT_EQ(compute_page_key<MONAD_SLOT_BITS>(slot_key), page_key_0)
            << "slot " << static_cast<int>(i)
            << " should map to same page as slot 0";
        EXPECT_EQ(compute_slot_offset<MONAD_SLOT_MASK>(slot_key), i)
            << "slot " << static_cast<int>(i)
            << " should have offset equal to its low bits";
    }

    // Key 0x40 should map to a different page
    bytes32_t const slot_64 = bytes32_t{0x40};
    EXPECT_NE(compute_page_key<MONAD_SLOT_BITS>(slot_64), page_key_0);
    EXPECT_EQ(compute_slot_offset<MONAD_SLOT_MASK>(slot_64), 0);

    // Keys 0x40..0x7F should share a second page
    bytes32_t const page_key_1 =
        compute_page_key<MONAD_SLOT_BITS>(bytes32_t{0x40});
    for (uint8_t i = 0x40; i < 0x80; ++i) {
        bytes32_t const slot_key = bytes32_t{i};
        EXPECT_EQ(compute_page_key<MONAD_SLOT_BITS>(slot_key), page_key_1);
        EXPECT_EQ(
            compute_slot_offset<MONAD_SLOT_MASK>(slot_key),
            static_cast<uint8_t>(i & MONAD_SLOT_MASK));
    }

    // Round-trip for all keys 0..0xFF
    for (uint16_t i = 0; i < 256; ++i) {
        bytes32_t const slot_key = bytes32_t{static_cast<uint8_t>(i)};
        bytes32_t const pk = compute_page_key<MONAD_SLOT_BITS>(slot_key);
        uint8_t const off = compute_slot_offset<MONAD_SLOT_MASK>(slot_key);
        EXPECT_EQ(compute_slot_key<MONAD_SLOT_BITS>(pk, off), slot_key);
    }
}

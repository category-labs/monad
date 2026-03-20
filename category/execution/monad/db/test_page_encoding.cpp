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

#include <category/execution/monad/db/storage_page.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(PageEncoding, coo_1_slot)
{
    storage_page_t page{};
    page[42] = bytes32_t{0xFF};
    auto const enc = encode_storage_page(page);
    // COO: header(1) + indices(1) + values(32) = 34
    EXPECT_EQ(enc.size(), 34u);
    EXPECT_EQ(enc[0], 0x01);
    EXPECT_EQ(enc[1], 42);
    EXPECT_EQ(decode_storage_page(enc.data(), enc.size()), page);
}

TEST(PageEncoding, coo_4_slots)
{
    storage_page_t page{};
    page[0] = bytes32_t{0x01};
    page[31] = bytes32_t{0x02};
    page[64] = bytes32_t{0x03};
    page[127] = bytes32_t{0x04};
    auto const enc = encode_storage_page(page);
    // COO: header(1) + indices(4) + values(4*32) = 133
    EXPECT_EQ(enc.size(), 133u);
    EXPECT_EQ(enc[0], 0x04);
    EXPECT_EQ(decode_storage_page(enc.data(), enc.size()), page);
}

TEST(PageEncoding, bitmap_16_slots)
{
    storage_page_t page{};
    for (uint8_t i = 0; i < 16; ++i) {
        page[i * 8] = bytes32_t{static_cast<uint8_t>(i + 1)};
    }
    auto const enc = encode_storage_page(page);
    // Bitmap: header(1) + mask(16) + values(16*32) = 529
    EXPECT_EQ(enc[0] & 0x80, 0x80);
    EXPECT_EQ(enc.size(), 529u);
    EXPECT_EQ(decode_storage_page(enc.data(), enc.size()), page);
}

TEST(PageEncoding, bitmap_full_page)
{
    storage_page_t page{};
    for (uint8_t i = 0; i < 128; ++i) {
        page[i] = bytes32_t{static_cast<uint8_t>(i + 1)};
    }
    auto const enc = encode_storage_page(page);
    // Bitmap: header(1) + mask(16) + values(128*32) = 4113
    EXPECT_EQ(enc[0] & 0x80, 0x80);
    EXPECT_EQ(enc.size(), 4113u);
    EXPECT_EQ(decode_storage_page(enc.data(), enc.size()), page);
}

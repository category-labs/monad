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

TEST(PageEncoding, single_slot)
{
    storage_page_t page{};
    page[42] = bytes32_t{0xFF};
    auto const enc = encode_storage_page(page);
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

TEST(PageEncoding, four_slots)
{
    storage_page_t page{};
    page[0] = bytes32_t{0x01};
    page[31] = bytes32_t{0x02};
    page[64] = bytes32_t{0x03};
    page[127] = bytes32_t{0x04};
    auto const enc = encode_storage_page(page);
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

TEST(PageEncoding, sixteen_slots)
{
    storage_page_t page{};
    for (uint8_t i = 0; i < 16; ++i) {
        page[i * 8] = bytes32_t{static_cast<uint8_t>(i + 1)};
    }
    auto const enc = encode_storage_page(page);
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

TEST(PageEncoding, full_page)
{
    storage_page_t page{};
    for (uint8_t i = 0; i < 128; ++i) {
        page[i] = bytes32_t{static_cast<uint8_t>(i + 1)};
    }
    auto const enc = encode_storage_page(page);
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

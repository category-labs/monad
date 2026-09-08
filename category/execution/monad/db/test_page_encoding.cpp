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

#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(PageEncoding, empty_page)
{
    storage_page_t page{};
    auto const enc = encode_storage_page(page);
    EXPECT_TRUE(enc.empty());
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

TEST(PageEncoding, single_slot)
{
    storage_page_t page{};
    page.set(42, bytes32_t{0xFF});
    auto const enc = encode_storage_page(page);
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

TEST(PageEncoding, four_slots)
{
    storage_page_t page{};
    page.set(0, bytes32_t{0x01});
    page.set(31, bytes32_t{0x02});
    page.set(64, bytes32_t{0x03});
    page.set(127, bytes32_t{0x04});
    auto const enc = encode_storage_page(page);
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

TEST(PageEncoding, sixteen_slots)
{
    storage_page_t page{};
    for (uint8_t i = 0; i < 16; ++i) {
        page.set(i * 8, bytes32_t{static_cast<uint8_t>(i + 1)});
    }
    auto const enc = encode_storage_page(page);
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

TEST(PageEncoding, full_page)
{
    storage_page_t page{};
    for (uint8_t i = 0; i < 128; ++i) {
        page.set(i, bytes32_t{static_cast<uint8_t>(i + 1)});
    }
    auto const enc = encode_storage_page(page);
    EXPECT_EQ(decode_storage_page(enc).value(), page);
}

TEST(PageEncoding, decode_rejects_zero_value)
{
    // RLP empty string (0x80) decodes to the zero bytes32, which must not
    // appear as a pair value.
    byte_string enc = {0x00, 0x80};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_leading_zero_in_value)
{
    // 0x82 0x00 0x05 encodes value 5 with a leading zero byte; the
    // canonical compact form is the single byte 0x05.
    byte_string enc = {0x00, 0x82, 0x00, 0x05};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_out_of_order_indices)
{
    // Index 5 followed by index 3 violates strictly ascending order.
    byte_string enc = {0x05, 0x01, 0x03, 0x02};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_duplicate_index)
{
    // The same index appearing twice is not strictly ascending.
    byte_string enc = {0x05, 0x01, 0x05, 0x02};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_out_of_range_index)
{
    // Index 128 (0x80) equals SLOTS and is out of range.
    byte_string enc = {0x80, 0x01};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_oversized_slot)
{
    // RLP string of 33 bytes exceeds sizeof(bytes32_t).
    byte_string enc;
    enc.push_back(0x00); // slot index 0
    enc.push_back(0x80 + 33); // RLP short-string prefix for 33 bytes
    enc.append(33, 0xAB);
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::InputTooLong);
}

TEST(PageEncoding, decode_rejects_truncated_pair)
{
    // Index byte with no following value bytes.
    byte_string enc = {0x00};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::InputTooShort);
}

TEST(PageEncoding, decode_storage_page_leaf_roundtrip)
{
    constexpr bytes32_t page_key{uint64_t{0xabcd}};
    storage_page_t page{};
    page.set(0, bytes32_t{uint64_t{0x11}});
    page.set(64, bytes32_t{uint64_t{0x22}});
    page.set(127, bytes32_t{uint64_t{0x33}});

    auto const leaf = encode_storage_page_db(page_key, page);
    auto const decoded = decode_storage_page_leaf(byte_string_view{leaf});
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded.value().page_key, page_key);
    EXPECT_EQ(decoded.value().page, page);
}

TEST(PageEncoding, decode_storage_page_leaf_rejects_trailing_bytes)
{
    constexpr bytes32_t page_key{uint64_t{0xabcd}};
    storage_page_t page{};
    page.set(3, bytes32_t{uint64_t{0x44}});

    auto leaf = encode_storage_page_db(page_key, page);
    leaf.push_back(0x00); // trailing byte after the RLP list
    auto const decoded = decode_storage_page_leaf(byte_string_view{leaf});
    ASSERT_TRUE(decoded.has_error());
    EXPECT_EQ(decoded.assume_error(), rlp::DecodeError::InputTooLong);
}

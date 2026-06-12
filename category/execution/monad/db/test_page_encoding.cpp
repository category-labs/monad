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
#include <category/execution/monad/db/storage_page.hpp>

#include <gtest/gtest.h>

using namespace monad;

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

TEST(PageEncoding, decode_rejects_split_zero_runs)
{
    // 0x01 0x01 (two adjacent zero-runs) must be 0x02.
    byte_string enc = {0x01, 0x01, 0x80, 0x05, 0x00};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_split_data_runs)
{
    // Two adjacent data-runs of 1 slot must be one data-run of 2 slots.
    byte_string enc = {0x80, 0x05, 0x80, 0x06, 0x00};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_zero_run_before_terminator)
{
    // 0x05 0x00 (zero-run then terminator) must be just 0x00.
    byte_string enc = {0x05, 0x00};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_zero_value_in_data_run)
{
    // RLP empty string (0x80) decodes to the zero value, which cannot
    // appear inside a data run.
    byte_string enc = {0x80, 0x80, 0x00};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_leading_zero_in_value)
{
    // 0x82 0x00 0x05 encodes value 5 with a leading zero byte; the
    // canonical compact form is the single byte 0x05.
    byte_string enc = {0x80, 0x82, 0x00, 0x05, 0x00};
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::NonCanonical);
}

TEST(PageEncoding, decode_rejects_oversized_slot)
{
    // Malformed encoding: data-run of 1 slot whose RLP string is 33 bytes
    // long, exceeding sizeof(bytes32_t). Must error, not crash in to_bytes.
    byte_string enc;
    enc.push_back(0x80); // data-run, count = 1
    enc.push_back(0x80 + 33); // RLP short-string prefix for 33 bytes
    enc.append(33, 0xAB);
    auto const result = decode_storage_page(enc);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), rlp::DecodeError::InputTooLong);
}

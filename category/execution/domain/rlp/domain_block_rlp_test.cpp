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
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/rlp/domain_block_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::domain;

namespace
{
    DomainBlockHeader sample_header()
    {
        return DomainBlockHeader{
            .parent_id = bytes32_from_hex(
                "0x3333333333333333333333333333333333333333333333333333333333"
                "333333"),
            .number = 7,
            .l1_block_number = 1000,
            .l1_block_hash = bytes32_from_hex(
                "0x1111111111111111111111111111111111111111111111111111111111"
                "111111"),
            .timestamp = 1'700'000'000,
            .mix_hash = bytes32_from_hex(
                "0x2222222222222222222222222222222222222222222222222222222222"
                "222222"),
            .gas_limit = 300'000'000,
            .base_fee_per_gas = 100'000'000'000,
            .transactions_root = NULL_ROOT};
    }

    // Independently encoded with a minimal Python RLP encoder.
    constexpr char SAMPLE_HEADER_RLP[] =
        "f898a03333333333333333333333333333333333333333333333333333333333333333"
        "078203e8a0111111111111111111111111111111111111111111111111111111111111"
        "1111846553f100a0222222222222222222222222222222222222222222222222222222"
        "22222222228411e1a30085174876e800a056e81f171bcc55a6ff8345e692c0f86e5b48"
        "e01b996cadc001622fb5e363b421";
    constexpr char SAMPLE_EMPTY_BLOCK_RLP[] =
        "f89bf898a0333333333333333333333333333333333333333333333333333333333333"
        "3333078203e8a011111111111111111111111111111111111111111111111111111111"
        "11111111846553f100a022222222222222222222222222222222222222222222222222"
        "222222222222228411e1a30085174876e800a056e81f171bcc55a6ff8345e692c0f86e"
        "5b48e01b996cadc001622fb5e363b421c0";
    // SAMPLE_HEADER_RLP with slot_number = 0x1234.
    constexpr char SAMPLE_HEADER_WITH_SLOT_RLP[] =
        "f89ba03333333333333333333333333333333333333333333333333333333333333333"
        "078203e8a0111111111111111111111111111111111111111111111111111111111111"
        "1111846553f100a0222222222222222222222222222222222222222222222222222222"
        "22222222228411e1a30085174876e800a056e81f171bcc55a6ff8345e692c0f86e5b48"
        "e01b996cadc001622fb5e363b421821234";

    Transaction legacy_transaction()
    {
        return Transaction{
            .sc =
                {.signature = {.r = 1, .s = 2, .y_parity = 1},
                 .chain_id = 0x510000279f},
            .nonce = 3,
            .max_fee_per_gas = 100'000'000'000,
            .gas_limit = 21'000,
            .value = 0,
            .to = Address{0x1234},
            .type = TransactionType::legacy};
    }

    Transaction eip1559_transaction()
    {
        return Transaction{
            .sc =
                {.signature = {.r = 4, .s = 5, .y_parity = 0},
                 .chain_id = 0x510000279f},
            .nonce = 9,
            .max_fee_per_gas = 200'000'000'000,
            .gas_limit = 50'000,
            .value = 0,
            .to = Address{0x5678},
            .type = TransactionType::eip1559,
            .data = byte_string{0xde, 0xad, 0xbe, 0xef},
            .max_priority_fee_per_gas = 1};
    }
}

TEST(DomainBlockRlp, header_known_answer)
{
    auto const expected = *from_hex(SAMPLE_HEADER_RLP);
    EXPECT_EQ(rlp::encode_domain_block_header(sample_header()), expected);

    byte_string_view view{expected};
    auto const decoded = rlp::decode_domain_block_header(view);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded.value(), sample_header());
    EXPECT_TRUE(view.empty());
}

// keccak256 of SAMPLE_HEADER_RLP, by eth-utils.
TEST(DomainBlockRlp, block_id_known_answer)
{
    EXPECT_EQ(
        domain_block_id(sample_header()),
        bytes32_from_hex(
            "0x46113908ff8878ceb190643687840c1e56ed5ed187d75c8756939c"
            "3100f369a1"));
}

TEST(DomainBlockRlp, header_with_slot_number_known_answer)
{
    auto header = sample_header();
    header.slot_number = 0x1234;
    auto const expected = *from_hex(SAMPLE_HEADER_WITH_SLOT_RLP);
    EXPECT_EQ(rlp::encode_domain_block_header(header), expected);

    byte_string_view view{expected};
    auto const decoded = rlp::decode_domain_block_header(view);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded.value(), header);
    EXPECT_TRUE(view.empty());
}

TEST(DomainBlockRlp, empty_block_known_answer)
{
    DomainBlock const block{.header = sample_header()};
    auto const expected = *from_hex(SAMPLE_EMPTY_BLOCK_RLP);
    EXPECT_EQ(rlp::encode_domain_block(block), expected);

    byte_string_view view{expected};
    auto const decoded = rlp::decode_domain_block(view);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded.value(), block);
    EXPECT_TRUE(view.empty());
}

TEST(DomainBlockRlp, round_trips_legacy_and_typed_transactions)
{
    DomainBlock const block{
        .header = sample_header(),
        .transactions = {legacy_transaction(), eip1559_transaction()}};

    auto const encoded = rlp::encode_domain_block(block);
    byte_string_view view{encoded};
    auto const decoded = rlp::decode_domain_block(view);

    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded.value(), block);
    EXPECT_TRUE(view.empty());
}

TEST(DomainBlockRlp, rejects_extra_block_fields)
{
    auto const header = rlp::encode_domain_block_header(sample_header());
    // [header, [], 0x01]
    byte_string const payload = header + *from_hex("c001");
    ASSERT_GE(payload.size(), 56);
    ASSERT_LT(payload.size(), 256);
    byte_string encoded{0xf8, static_cast<uint8_t>(payload.size())};
    encoded += payload;

    byte_string_view view{encoded};
    auto const decoded = rlp::decode_domain_block(view);
    ASSERT_TRUE(decoded.has_error());
    EXPECT_EQ(decoded.error(), rlp::DecodeError::InputTooLong);
}

TEST(DomainBlockRlp, rejects_extra_header_fields)
{
    auto encoded = *from_hex(SAMPLE_HEADER_RLP);
    // Append a slot_number and one more field, and fix up the list length.
    encoded.push_back(0x01);
    encoded.push_back(0x01);
    encoded[1] = static_cast<uint8_t>(encoded[1] + 2);

    byte_string_view view{encoded};
    auto const decoded = rlp::decode_domain_block_header(view);
    ASSERT_TRUE(decoded.has_error());
    EXPECT_EQ(decoded.error(), rlp::DecodeError::InputTooLong);
}

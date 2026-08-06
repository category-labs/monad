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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>

#include <ankerl/unordered_dense.h>

#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

using namespace monad;

namespace
{
    byte_string make_minimal_witness()
    {
        return encode_execution_witness({}, {}, {}, {});
    }

    constexpr auto ADDR_X = 0x00000000000000000000000000000000deadbeef_address;
    constexpr auto ADDR_Y = 0x000000000000000000000000000000000baddcaf_address;
    constexpr auto ADDR_Z = 0xcafef00dcafef00dcafef00dcafef00dcafef00d_address;
}

TEST(ParseExecutionWitness, ValidMinimalWitness)
{
    auto const w = make_minimal_witness();
    auto const result = parse_execution_witness(w);
    ASSERT_FALSE(result.has_error());
    EXPECT_TRUE(result.value().block_rlp.empty());
    EXPECT_TRUE(result.value().encoded_nodes.empty());
    EXPECT_TRUE(result.value().encoded_codes.empty());
    EXPECT_TRUE(result.value().encoded_headers.empty());
    EXPECT_TRUE(result.value().encoded_parent_senders_and_authorities.empty());
    EXPECT_TRUE(
        result.value().encoded_grandparent_senders_and_authorities.empty());
}

TEST(ParseExecutionWitness, EmptyInput)
{
    auto const result = parse_execution_witness({});
    EXPECT_TRUE(result.has_error());
}

TEST(ParseExecutionWitness, OuterTypeNotList)
{
    // A single empty-string byte (0x80) is not a list.
    byte_string const bad{static_cast<unsigned char>(0x80)};
    auto const result = parse_execution_witness(bad);
    EXPECT_TRUE(result.has_error());
}

TEST(ParseExecutionWitness, Truncated)
{
    auto w = make_minimal_witness();
    w.resize(w.size() - 1);
    auto const result = parse_execution_witness(w);
    EXPECT_TRUE(result.has_error());
}

TEST(EncodeExecutionWitness, AllFieldsRoundtrip)
{
    // block_rlp is wrapped by the encoder as an RLP string; the parser hands
    // back the unwrapped payload.
    byte_string const block_rlp{0x01, 0x02, 0x03, 0x04};

    // Nodes are already complete RLP items and are emitted raw, so the parsed
    // [1] payload is their straight concatenation.
    std::vector<byte_string> const nodes{
        rlp::encode_list2(rlp::encode_string2(byte_string{0xaa})),
        rlp::encode_string2(byte_string{0xbb, 0xcc})};

    // Codes and headers are each wrapped as RLP strings by the encoder.
    std::vector<byte_string> const codes{
        byte_string{0x60, 0x00, 0x60, 0x00}, byte_string{0x00}};
    std::vector<byte_string> const headers{
        byte_string{0xde, 0xad}, byte_string{0xbe, 0xef, 0xfe}};

    ankerl::unordered_dense::segmented_set<Address> parents;
    parents.insert(ADDR_X);
    parents.insert(ADDR_Y);
    ankerl::unordered_dense::segmented_set<Address> grandparents;
    grandparents.insert(ADDR_Z);

    byte_string const encoded = encode_execution_witness(
        block_rlp, nodes, codes, headers, &parents, &grandparents);

    auto const result = parse_execution_witness(encoded);
    ASSERT_FALSE(result.has_error());
    auto const &w = result.value();

    EXPECT_EQ(w.block_rlp, byte_string_view{block_rlp});

    // [1] nodes: raw concatenation.
    EXPECT_EQ(w.encoded_nodes, byte_string_view{nodes[0] + nodes[1]});

    // [2] codes / [3] headers: each entry wrapped as an RLP string.
    EXPECT_EQ(
        w.encoded_codes,
        byte_string_view{
            rlp::encode_string2(codes[0]) + rlp::encode_string2(codes[1])});
    EXPECT_EQ(
        w.encoded_headers,
        byte_string_view{
            rlp::encode_string2(headers[0]) + rlp::encode_string2(headers[1])});

    // [4]/[5] addresses: emitted in sorted order, each wrapped as an RLP
    // string.
    std::vector<Address> sorted_parents{ADDR_X, ADDR_Y};
    std::sort(sorted_parents.begin(), sorted_parents.end());
    byte_string expected_parents;
    for (auto const &a : sorted_parents) {
        expected_parents += rlp::encode_string2(to_byte_string_view(a.bytes));
    }
    EXPECT_EQ(
        w.encoded_parent_senders_and_authorities,
        byte_string_view{expected_parents});
    EXPECT_EQ(
        w.encoded_grandparent_senders_and_authorities,
        byte_string_view{
            rlp::encode_string2(to_byte_string_view(ADDR_Z.bytes))});
}

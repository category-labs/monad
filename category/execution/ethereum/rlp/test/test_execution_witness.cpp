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

    // The node blob is opaque to the encoder and emitted raw, so the parsed
    // [1] payload is exactly the input bytes.
    byte_string const nodes{0xaa, 0xbb, 0xcc, 0xdd, 0xee};

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

    // [1] nodes: the blob emitted raw.
    EXPECT_EQ(w.encoded_nodes, byte_string_view{nodes});

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

// ---------------------------------------------------------------------------
// L2 shape: the same six fields plus [6] sk.
//
// The two shapes reject each other, which is why the envelope carries no
// version byte: the strict trailing-byte checks already do the work, in both
// directions, and a version would only add a runtime dispatch nobody wants.
// ---------------------------------------------------------------------------

namespace
{
    byte_string const SK(32, 0x42);

    byte_string make_minimal_l2_witness()
    {
        return encode_execution_witness_l2({}, {}, {}, {}, SK);
    }
}

TEST(ParseExecutionWitnessL2, ValidMinimalWitness)
{
    auto const w = make_minimal_l2_witness();
    auto const result = parse_execution_witness_l2(w);
    ASSERT_FALSE(result.has_error());
    EXPECT_TRUE(result.value().base.block_rlp.empty());
    EXPECT_EQ(result.value().sk, byte_string_view{SK});
}

TEST(ParseExecutionWitnessL2, RejectsSixFieldWitness)
{
    EXPECT_TRUE(parse_execution_witness_l2(make_minimal_witness()).has_error());
}

TEST(ParseExecutionWitness, RejectsSevenFieldWitness)
{
    EXPECT_TRUE(parse_execution_witness(make_minimal_l2_witness()).has_error());
}

TEST(ParseExecutionWitnessL2, RejectsTrailingBytes)
{
    auto w = make_minimal_l2_witness();
    w.push_back(0x00);
    EXPECT_TRUE(parse_execution_witness_l2(w).has_error());
}

TEST(ParseExecutionWitnessL2, RejectsTruncated)
{
    auto w = make_minimal_l2_witness();
    w.resize(w.size() - 1);
    EXPECT_TRUE(parse_execution_witness_l2(w).has_error());
}

// A key of the wrong width is an envelope defect, not a cipher one, so it is
// caught here rather than left to the scalar-range check.
TEST(ParseExecutionWitnessL2, RejectsWrongKeyLength)
{
    for (size_t len : {size_t{0}, size_t{31}, size_t{33}}) {
        // encode_execution_witness_l2 asserts 32, so the short key is built by
        // hand: an outer list holding six empty fields and one short string.
        byte_string inner;
        inner += rlp::encode_string2(byte_string_view{}); // [0]
        for (int i = 0; i < 5; ++i) {
            inner += rlp::encode_list2(); // [1]..[5]
        }
        inner += rlp::encode_string2(byte_string(len, 0x11)); // [6]
        auto const w = rlp::encode_list2(inner);
        EXPECT_TRUE(parse_execution_witness_l2(w).has_error()) << "len " << len;
    }
}

TEST(EncodeExecutionWitnessL2, SixFieldPrefixIsUnchanged)
{
    byte_string const block_rlp{0x01, 0x02};
    byte_string const nodes{0xaa, 0xbb};
    std::vector<byte_string> const codes{byte_string{0x60, 0x00}};
    std::vector<byte_string> const headers{byte_string{0xde, 0xad}};

    auto const plain =
        encode_execution_witness(block_rlp, nodes, codes, headers);
    auto const l2 =
        encode_execution_witness_l2(block_rlp, nodes, codes, headers, SK);

    // Both are one encoder with one optional field, so the six fields must
    // agree. They do not share a prefix -- the outer length differs -- so the
    // check is on what the parser hands back.
    auto const a = parse_execution_witness(plain);
    auto const b = parse_execution_witness_l2(l2);
    ASSERT_FALSE(a.has_error());
    ASSERT_FALSE(b.has_error());
    EXPECT_EQ(a.value().block_rlp, b.value().base.block_rlp);
    EXPECT_EQ(a.value().encoded_nodes, b.value().base.encoded_nodes);
    EXPECT_EQ(a.value().encoded_codes, b.value().base.encoded_codes);
    EXPECT_EQ(a.value().encoded_headers, b.value().base.encoded_headers);
    EXPECT_EQ(b.value().sk, byte_string_view{SK});
}

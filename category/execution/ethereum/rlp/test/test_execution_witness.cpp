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

// A domain's witness is its own six fields, not the node's with two appended:
// a body rather than a block, L1 block hashes rather than ancestor headers,
// and no sender sets. Both shapes are six fields, so what tells them apart is
// field [4] -- a list of addresses for the node, a string for a domain.

namespace
{
    byte_string const SK(32, 0x42);
    byte_string const SALT(32, 0x5a);

    byte_string make_minimal_l2_witness()
    {
        return encode_execution_witness_l2({}, {}, {}, {}, SK, SALT);
    }
}

TEST(ParseExecutionWitnessL2, ValidMinimalWitness)
{
    auto const w = make_minimal_l2_witness();
    auto const result = parse_execution_witness_l2(w);
    ASSERT_FALSE(result.has_error());
    EXPECT_TRUE(result.value().domain_body.empty());
    EXPECT_TRUE(result.value().encoded_ancestor_hashes.empty());
    EXPECT_EQ(result.value().sk, byte_string_view{SK});
    EXPECT_EQ(result.value().salt_secret, byte_string_view{SALT});
}

// Each parser refuses the other's shape. Neither can be read as the other by
// accident: at [4] one finds a list where it wants a string, the other the
// reverse, and RLP marks the two differently.
TEST(ParseExecutionWitnessL2, RefusesTheNodeShape)
{
    EXPECT_TRUE(parse_execution_witness_l2(make_minimal_witness()).has_error());
}

TEST(ParseExecutionWitness, RefusesTheDomainShape)
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

// A secret of the wrong width is an envelope defect, not a cipher one, so it
// is caught here rather than left to the scalar-range check or to the
// commitment check in the guest.
TEST(ParseExecutionWitnessL2, RejectsWrongSecretLength)
{
    // Which of the two secrets is short, so neither check stands in for the
    // other -- [4] being validated would otherwise hide [5] not being.
    for (int which : {4, 5}) {
        for (size_t len : {size_t{0}, size_t{31}, size_t{33}}) {
            // encode_execution_witness_l2 asserts 32 on both, so the short one
            // is built by hand: a string, three lists, then the two secrets.
            byte_string inner;
            inner += rlp::encode_string2(byte_string_view{}); // [0]
            for (int i = 0; i < 3; ++i) {
                inner += rlp::encode_list2(); // [1]..[3]
            }
            inner += rlp::encode_string2(
                byte_string(which == 4 ? len : 32, 0x11)); // [4]
            inner += rlp::encode_string2(
                byte_string(which == 5 ? len : 32, 0x22)); // [5]
            auto const w = rlp::encode_list2(inner);
            EXPECT_TRUE(parse_execution_witness_l2(w).has_error())
                << "field " << which << " len " << len;
        }
    }
}

// The eight-field shape this branch carried before the split is now as wrong
// as any other. Worth a case of its own: a stale witness is a thing that
// exists rather than a hypothetical.
TEST(ParseExecutionWitnessL2, RejectsTheEightFieldShape)
{
    byte_string inner;
    inner += rlp::encode_string2(byte_string_view{}); // [0]
    for (int i = 0; i < 5; ++i) {
        inner += rlp::encode_list2(); // [1]..[5], sender sets included
    }
    inner += rlp::encode_string2(byte_string(32, 0x11)); // [6]
    inner += rlp::encode_string2(byte_string(32, 0x22)); // [7]
    auto const w = rlp::encode_list2(inner);
    EXPECT_TRUE(parse_execution_witness_l2(w).has_error());
}

// The three fields the two shapes still share must round-trip the same way,
// so that a change to one encoder cannot quietly diverge from the other.
TEST(EncodeExecutionWitnessL2, TheSharedFieldsAgree)
{
    byte_string const body{0x01, 0x02};
    byte_string const nodes{0xaa, 0xbb};
    std::vector<byte_string> const codes{byte_string{0x60, 0x00}};
    std::vector<byte_string> const hashes{byte_string(32, 0xde)};
    std::vector<byte_string> const headers{byte_string{0xde, 0xad}};

    auto const plain = encode_execution_witness(body, nodes, codes, headers);
    auto const l2 =
        encode_execution_witness_l2(body, nodes, codes, hashes, SK, SALT);

    auto const a = parse_execution_witness(plain);
    auto const b = parse_execution_witness_l2(l2);
    ASSERT_FALSE(a.has_error());
    ASSERT_FALSE(b.has_error());
    EXPECT_EQ(a.value().block_rlp, b.value().domain_body);
    EXPECT_EQ(a.value().encoded_nodes, b.value().encoded_nodes);
    EXPECT_EQ(a.value().encoded_codes, b.value().encoded_codes);
    EXPECT_EQ(b.value().sk, byte_string_view{SK});
}

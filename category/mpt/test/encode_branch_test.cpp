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
#include <category/mpt/compute.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <optional>
#include <span>

using namespace monad;
using namespace monad::mpt;

TEST(EncodeBranch, NoValueInlineChildren)
{
    // Branch with two sub-KECCAK256_SIZE child refs at slots 3 and 8 and no
    // value. encode_16_children memcpys inline child data verbatim; empty
    // slots and the missing value each emit 0x80. Expected layout:
    //   [child slot 0: 0x80, ..., slot 3: 0x11, ..., slot 8: 0x22, ...,
    //    slot 15: 0x80, value: 0x80]
    // Payload is 17 bytes; the RLP list header is 0xc0 + 17 = 0xd1.
    ChildData c0{};
    c0.len = 1;
    c0.data[0] = 0x11;
    c0.branch = 0x3;
    c0.ptr = make_node(
        0, {}, NibblesView{}, byte_string_view{}, byte_string_view{}, 0);

    ChildData c1{};
    c1.len = 1;
    c1.data[0] = 0x22;
    c1.branch = 0x8;
    c1.ptr = make_node(
        0, {}, NibblesView{}, byte_string_view{}, byte_string_view{}, 0);

    std::array<ChildData, 2> children{c0, c1};

    Node::SharedPtr const node = make_node(
        /*mask=*/static_cast<uint16_t>((1u << 0x3) | (1u << 0x8)),
        /*children=*/std::span<ChildData>{children},
        /*path=*/NibblesView{},
        /*value=*/std::nullopt,
        /*data=*/byte_string_view{},
        /*version=*/0);

    byte_string const encoded = encode_branch(*node);

    byte_string const expected = {
        0xd1,
        0x80,
        0x80,
        0x80,
        0x11,
        0x80,
        0x80,
        0x80,
        0x80,
        0x22,
        0x80,
        0x80,
        0x80,
        0x80,
        0x80,
        0x80,
        0x80,
        0x80};
    EXPECT_EQ(encoded, expected);
}

TEST(EncodeBranch, HashedChildAndValue)
{
    // Branch with a single KECCAK256_SIZE-sized child reference at slot 0
    // and a non-empty value. encode_16_children RLP-string-wraps the 32-byte
    // child (header 0xa0 = 0x80 + 32), the other 15 slots are 0x80, and the
    // value is RLP-string-wrapped by NoopProcessor.
    std::array<unsigned char, 32> child_hash{};
    child_hash.fill(0xaa);

    ChildData c0{};
    c0.len = 32;
    std::copy_n(child_hash.data(), 32, c0.data);
    c0.branch = 0x0;
    c0.ptr = make_node(
        0, {}, NibblesView{}, byte_string_view{}, byte_string_view{}, 0);

    std::array<ChildData, 1> children{c0};

    byte_string const value = {'h', 'e', 'l', 'l', 'o'};
    Node::SharedPtr const node = make_node(
        /*mask=*/static_cast<uint16_t>(1u << 0x0),
        /*children=*/std::span<ChildData>{children},
        /*path=*/NibblesView{},
        /*value=*/byte_string_view{value},
        /*data=*/byte_string_view{},
        /*version=*/0);

    byte_string const encoded = encode_branch(*node);

    // Payload: 33 (0xa0 + 32 hash bytes) + 15 (empty slots) + 6 (0x85 +
    // "hello") = 54 bytes. List header is 0xc0 + 54 = 0xf6.
    byte_string expected;
    expected.push_back(0xf6);
    expected.push_back(0xa0);
    expected.append(child_hash.begin(), child_hash.end());
    for (int i = 0; i < 15; ++i) {
        expected.push_back(0x80);
    }
    expected.push_back(0x85);
    expected.append(value.begin(), value.end());

    EXPECT_EQ(encoded, expected);
}

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

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::mpt;

TEST(EncodeTwoPieces, Leaf)
{
    // Path {1, 2, 3} as a terminating (leaf) compact encoding:
    //   prefix byte 0x31 = terminating (0x20) | odd-length (0x10) | first
    //   nibble 0x1; remaining nibbles {2, 3} pack into 0x23.
    // RLP-encoded compact path: 0x82 0x31 0x23 (string of length 2).
    // RLP-encoded value "hello": 0x85 'h' 'e' 'l' 'l' 'o'.
    // Wrapped in an RLP list of payload length 9: header 0xc9.
    Nibbles path{3};
    path.set(0, 0x1);
    path.set(1, 0x2);
    path.set(2, 0x3);

    byte_string const value = {'h', 'e', 'l', 'l', 'o'};
    auto const encoded = encode_two_pieces(
        NibblesView{path}, byte_string_view{value}, /*has_value=*/true);

    byte_string const expected = {
        0xc9, 0x82, 0x31, 0x23, 0x85, 'h', 'e', 'l', 'l', 'o'};
    EXPECT_EQ(encoded, expected);
}

TEST(EncodeTwoPieces, ExtensionShortChildRef)
{
    // Extension with a sub-KECCAK256_SIZE child reference: the second piece
    // is already RLP and is concatenated raw rather than re-encoded as an RLP
    // string. Path {0xa, 0xb} as an even-length extension compact-encodes to
    // [0x00, 0xab]; RLP-encoded that's 0x82 0x00 0xab. The 4-byte second
    // piece is appended verbatim. Payload length 7, list header 0xc7.
    Nibbles path{2};
    path.set(0, 0xa);
    path.set(1, 0xb);

    byte_string const second = {0xc3, 0x01, 0x02, 0x03};
    auto const encoded = encode_two_pieces(
        NibblesView{path}, byte_string_view{second}, /*has_value=*/false);

    byte_string const expected = {
        0xc7, 0x82, 0x00, 0xab, 0xc3, 0x01, 0x02, 0x03};
    EXPECT_EQ(encoded, expected);
}

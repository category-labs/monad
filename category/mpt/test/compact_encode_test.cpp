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

#include <category/core/rlp/decode_error.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

#include <initializer_list>
#include <random>
#include <string>
#include <vector>

using namespace monad::mpt;
using monad::rlp::DecodeError;

namespace
{
    // Build a Nibbles from an initializer list of nibble values [0, 15].
    Nibbles make_nibbles(std::initializer_list<unsigned char> values)
    {
        Nibbles n{values.size()};
        unsigned i = 0;
        for (auto const v : values) {
            n.set(i++, v);
        }
        return n;
    }

    void check_roundtrip(NibblesView const path, bool const is_leaf)
    {
        // Buffer size: one prefix byte + one byte per two nibbles (rounded up).
        std::vector<unsigned char> buf(path.nibble_size() / 2 + 1);
        auto const encoded = compact_encode(buf.data(), path, is_leaf);

        auto const decoded = compact_decode(encoded);
        ASSERT_TRUE(decoded.has_value());

        auto const &[nibbles, decoded_is_leaf] = decoded.value();
        EXPECT_EQ(decoded_is_leaf, is_leaf);
        EXPECT_EQ(NibblesView{nibbles}, path);
    }
} // namespace

TEST(CompactDecode, EmptyInput)
{
    auto const result = compact_decode({});
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), DecodeError::InputTooShort);
}

TEST(CompactDecode, InvalidHighBits)
{
    // Prefix bytes with bits 7–6 set are not valid compact encodings.
    unsigned char const b40[1] = {0x40};
    unsigned char const b80[1] = {0x80};
    unsigned char const bff[1] = {0xFF};
    auto const r40 = compact_decode({b40, 1});
    auto const r80 = compact_decode({b80, 1});
    auto const rff = compact_decode({bff, 1});
    ASSERT_TRUE(r40.has_error());
    ASSERT_TRUE(r80.has_error());
    ASSERT_TRUE(rff.has_error());
    EXPECT_EQ(r40.error(), DecodeError::TypeUnexpected);
    EXPECT_EQ(r80.error(), DecodeError::TypeUnexpected);
    EXPECT_EQ(rff.error(), DecodeError::TypeUnexpected);
}

TEST(CompactDecode, InvalidEvenPaddingNibble)
{
    // Even-length prefix (bit 4 clear) requires the low nibble to be 0x0.
    // 0x01 claims even extension but has a non-zero padding nibble.
    unsigned char const b01[1] = {0x01};
    unsigned char const b25[1] = {0x25};
    auto const r01 = compact_decode({b01, 1});
    // 0x25 claims even leaf but has a non-zero padding nibble.
    auto const r25 = compact_decode({b25, 1});
    ASSERT_TRUE(r01.has_error());
    ASSERT_TRUE(r25.has_error());
    EXPECT_EQ(r01.error(), DecodeError::TypeUnexpected);
    EXPECT_EQ(r25.error(), DecodeError::TypeUnexpected);
}

TEST(CompactDecode, NonTerminatingEmptyPath)
{
    // Prefix 0x00 with no following bytes → even extension, 0 nibbles.
    // This is structurally invalid (compact_encode asserts non-empty for
    // extensions), so compact_decode must reject it.
    unsigned char const b00[1] = {0x00};
    auto const result = compact_decode({b00, 1});
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), DecodeError::PathTooShort);
}

TEST(CompactDecode, PathOver255Nibbles)
{
    // Nibbles uses uint8_t for length; 129 bytes after a 0x20 leaf prefix
    // would decode to 256 nibbles, which compact_decode must reject.
    std::vector<unsigned char> buf(129, 0x00);
    buf[0] = 0x20; // even leaf
    auto const result =
        compact_decode({buf.data(), static_cast<unsigned>(buf.size())});
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), DecodeError::PathTooLong);
}

TEST(CompactRoundtrip, EvenLeaf)
{
    // Even-length path, terminating (prefix byte 0x20).
    auto const path = make_nibbles({0xA, 0xB, 0xC, 0xD});
    check_roundtrip(NibblesView{path}, /*is_leaf=*/true);
}

TEST(CompactRoundtrip, OddLeaf)
{
    // Odd-length path, terminating (prefix byte 0x3X, first nibble inline).
    auto const path = make_nibbles({0x1, 0x2, 0x3});
    check_roundtrip(NibblesView{path}, /*is_leaf=*/true);
}

TEST(CompactRoundtrip, EvenExtension)
{
    // Even-length path, non-terminating (prefix byte 0x00).
    auto const path = make_nibbles({0xE, 0xF, 0x0, 0x1});
    check_roundtrip(NibblesView{path}, /*is_leaf=*/false);
}

TEST(CompactRoundtrip, OddExtension)
{
    // Odd-length path, non-terminating (prefix byte 0x1X).
    auto const path = make_nibbles({0x7, 0x8, 0x9});
    check_roundtrip(NibblesView{path}, /*is_leaf=*/false);
}

TEST(CompactRoundtrip, EmptyPath)
{
    // An empty extension path is structurally invalid (compact_encode asserts
    // it), so only the leaf case is tested here.
    Nibbles const empty{0};
    check_roundtrip(NibblesView{empty}, /*is_leaf=*/true);
}

TEST(CompactRoundtrip, SingleNibble)
{
    auto const path = make_nibbles({0xF});
    check_roundtrip(NibblesView{path}, /*is_leaf=*/true);
    check_roundtrip(NibblesView{path}, /*is_leaf=*/false);
}

TEST(CompactRoundtrip, LongPath)
{
    // compact_encode/compact_decode have no length limit; test well beyond the
    // Ethereum-specific 64-nibble (33-byte) case.
    for (unsigned const len : {64u, 128u, 255u}) {
        Nibbles path{len};
        for (unsigned i = 0; i < len; ++i) {
            path.set(i, static_cast<unsigned char>(i & 0xF));
        }
        check_roundtrip(NibblesView{path}, /*is_leaf=*/true);
        check_roundtrip(NibblesView{path}, /*is_leaf=*/false);
    }
}

TEST(CompactRoundtrip, Random)
{
    std::mt19937_64 rng{0xc0ffee'dead'beef'13ULL};
    std::uniform_int_distribution<unsigned int> nibble_dist{0, 15};
    std::uniform_int_distribution<unsigned int> len_dist{0, 255};

    for (int i = 0; i < 500; ++i) {
        unsigned const len = len_dist(rng);
        bool const is_leaf =
            (len == 0) || (rng() & 1); // empty path must be leaf

        Nibbles path{len};
        for (unsigned j = 0; j < len; ++j) {
            path.set(j, static_cast<unsigned char>(nibble_dist(rng)));
        }

        SCOPED_TRACE(
            "iteration " + std::to_string(i) + ", len=" + std::to_string(len) +
            ", is_leaf=" + std::to_string(is_leaf));
        check_roundtrip(NibblesView{path}, is_leaf);
    }
}

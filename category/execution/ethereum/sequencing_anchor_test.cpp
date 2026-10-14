// Copyright (C) 2026 Category Labs, Inc.
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

// Rebuild the layout independently and test ordering/domain properties.
// Separate external vectors below pin the Keccak permutation itself.

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/execution/ethereum/sequencing_anchor.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <span>
#include <vector>

using namespace monad;

namespace
{
    constexpr uint64_t CHAIN = 0x0051000000004eafull;
    constexpr uint64_t NUMBER = 25'551'991ull;

    byte_string bytes_of(std::initializer_list<unsigned char> const b)
    {
        return byte_string{b.begin(), b.end()};
    }

    std::vector<byte_string_view> views_of(std::span<byte_string const> const v)
    {
        std::vector<byte_string_view> out;
        for (auto const &b : v) {
            out.emplace_back(b);
        }
        return out;
    }

    /// The anchor, rebuilt from the definition rather than from the function:
    /// keccak256(LABEL || chain_be64 || number_be64 || keccak256(ct_i)...).
    bytes32_t expected_anchor(
        uint64_t const chain, uint64_t const number,
        std::span<byte_string_view const> const ciphertexts)
    {
        byte_string buf;
        buf.append(
            reinterpret_cast<unsigned char const *>(SEQUENCING_ANCHOR_LABEL),
            sizeof(SEQUENCING_ANCHOR_LABEL) - 1);
        for (int i = 7; i >= 0; --i) {
            buf.push_back(static_cast<unsigned char>(chain >> (8 * i)));
        }
        for (int i = 7; i >= 0; --i) {
            buf.push_back(static_cast<unsigned char>(number >> (8 * i)));
        }
        for (auto const &ciphertext : ciphertexts) {
            bytes32_t const leaf = to_bytes(keccak256(ciphertext));
            buf.append(leaf.bytes, sizeof(leaf.bytes));
        }
        return to_bytes(keccak256(byte_string_view{buf}));
    }
}

TEST(SequencingAnchor, IsTheLabelledKeccakOverLeafHashes)
{
    std::vector<byte_string> const leaves{
        bytes_of({0x01}), bytes_of({0x02, 0x03}), bytes_of({0x04, 0x05, 0x06})};
    auto const views = views_of(leaves);

    EXPECT_EQ(
        sequencing_anchor(CHAIN, NUMBER, views),
        expected_anchor(CHAIN, NUMBER, views));
}

TEST(SequencingAnchor, EmptyBlockAnchorsToThePreambleAndNotToZero)
{
    std::vector<byte_string_view> const none;
    EXPECT_EQ(
        sequencing_anchor(CHAIN, NUMBER, none),
        expected_anchor(CHAIN, NUMBER, none));
    EXPECT_NE(sequencing_anchor(CHAIN, NUMBER, none), bytes32_t{});
}

TEST(SequencingAnchor, DomainAndHeightSeparateOtherwiseIdenticalBlocks)
{
    std::vector<byte_string> const leaves{bytes_of({0xaa, 0xbb})};
    auto const views = views_of(leaves);

    auto const here = sequencing_anchor(CHAIN, NUMBER, views);
    EXPECT_NE(here, sequencing_anchor(CHAIN + 1, NUMBER, views));
    EXPECT_NE(here, sequencing_anchor(CHAIN, NUMBER + 1, views));
}

TEST(SequencingAnchor, OrderIsBound)
{
    std::vector<byte_string> const forward{bytes_of({0x01}), bytes_of({0x02})};
    std::vector<byte_string> const reversed{bytes_of({0x02}), bytes_of({0x01})};

    EXPECT_NE(
        sequencing_anchor(CHAIN, NUMBER, views_of(forward)),
        sequencing_anchor(CHAIN, NUMBER, views_of(reversed)));
}

// The reason each leaf is hashed before being absorbed. A digest over the raw
// concatenation could not tell these apart, and the two are different sequenced
// sets: one block of two transactions against one block of two other ones.
TEST(SequencingAnchor, LeafBoundariesAreNotAmbiguous)
{
    std::vector<byte_string> const split_early{
        bytes_of({0xab}), bytes_of({0xcd, 0xef})};
    std::vector<byte_string> const split_late{
        bytes_of({0xab, 0xcd}), bytes_of({0xef})};

    EXPECT_NE(
        sequencing_anchor(CHAIN, NUMBER, views_of(split_early)),
        sequencing_anchor(CHAIN, NUMBER, views_of(split_late)));
}

// A leaf the cipher refuses is still part of what the L1 sequenced, so it
// counts. The anchor cannot know which leaves were rejected -- that is the
// point -- but it must distinguish a block that carried a rejected leaf from
// one that never carried it.
TEST(SequencingAnchor, ARejectedLeafStillCounts)
{
    std::vector<byte_string> const with{
        bytes_of({0x01}), bytes_of({0xff, 0xff})};
    std::vector<byte_string> const without{bytes_of({0x01})};

    EXPECT_NE(
        sequencing_anchor(CHAIN, NUMBER, views_of(with)),
        sequencing_anchor(CHAIN, NUMBER, views_of(without)));
}

// External vectors catch hash errors shared by both sides of the layout test,
// such as using SHA-3 padding instead of Keccak padding.
TEST(SequencingAnchor, MatchesVectorsFromAnOutsideImplementation)
{
    std::vector<byte_string_view> const none;
    EXPECT_EQ(
        sequencing_anchor(CHAIN, NUMBER, none),
        0x620833ca295d933c772e070bd9d52e313bbf628ec0dde37831e33efd7fa22e37_bytes32);

    std::vector<byte_string> const leaves{
        bytes_of({0x01}), bytes_of({0x02, 0x03}), bytes_of({0x04, 0x05, 0x06})};
    EXPECT_EQ(
        sequencing_anchor(CHAIN, NUMBER, views_of(leaves)),
        0xae88f7d7465128834f86fe6362b94bce69389d75c2369759ef66ec0d8c3b6e00_bytes32);
}

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

#include <category/crypto/keccak.h>

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>

extern "C" void
monad_zkvm_keccak256_fast(void const *in, size_t input_length, uint8_t out[32]);

namespace
{
    using Digest = std::array<uint8_t, 32>;

    Digest guest_digest(uint8_t const *const input, size_t const input_length)
    {
        Digest digest{};
        monad_zkvm_keccak256_fast(input, input_length, digest.data());
        return digest;
    }

    Digest
    reference_digest(uint8_t const *const input, size_t const input_length)
    {
        Digest digest{};
        monad_keccak256(input, input_length, digest.data());
        return digest;
    }
}

TEST(KeccakAccel, empty_input)
{
    EXPECT_EQ(guest_digest(nullptr, 0), reference_digest(nullptr, 0));
}

// Cover short inputs, every XOR-count boundary, padding and full blocks.
TEST(KeccakAccel, lengths_alignments_and_patterns)
{
    constexpr size_t max_input_length = 4 * 136;
    alignas(8) std::array<uint8_t, max_input_length + 7> buffer{};
    for (unsigned pattern = 0; pattern < 3; ++pattern) {
        for (size_t alignment_offset = 0; alignment_offset < 8;
             ++alignment_offset) {
            auto *const input = buffer.data() + alignment_offset;
            uint32_t random_state = 0x12345678;
            for (size_t i = 0; i < max_input_length; ++i) {
                random_state = random_state * 1664525u + 1013904223u;
                input[i] = pattern == 0 ? uint8_t{0}
                           : pattern == 1
                               ? uint8_t{0xff}
                               : static_cast<uint8_t>(random_state >> 24);
            }
            for (size_t input_length = 0; input_length <= max_input_length;
                 ++input_length) {
                ASSERT_EQ(
                    guest_digest(input, input_length),
                    reference_digest(input, input_length))
                    << "length=" << input_length
                    << ", alignment=" << alignment_offset
                    << ", pattern=" << pattern;
            }
        }
    }
}

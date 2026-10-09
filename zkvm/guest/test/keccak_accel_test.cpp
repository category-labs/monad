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

#include <ethash/keccak.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>

extern "C" void
monad_zkvm_keccak256_fast(void const *in, size_t input_length, uint8_t out[32]);

namespace
{
    bool
    matches_reference(uint8_t const *const input, size_t const input_length)
    {
        std::array<uint8_t, 32> actual{};
        monad_zkvm_keccak256_fast(input, input_length, actual.data());
        auto const expected = ethash_keccak256(input, input_length);
        return std::memcmp(actual.data(), expected.bytes, actual.size()) == 0;
    }
}

int main()
{
    if (!matches_reference(nullptr, 0)) {
        std::fprintf(stderr, "Keccak mismatch for empty input\n");
        return 1;
    }

    // Cover short inputs, every XOR-count boundary, padding and full blocks.
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
                if (!matches_reference(input, input_length)) {
                    std::fprintf(
                        stderr,
                        "Keccak mismatch: length=%zu, alignment=%zu, "
                        "pattern=%u\n",
                        input_length,
                        alignment_offset,
                        pattern);
                    return 1;
                }
            }
        }
    }
}

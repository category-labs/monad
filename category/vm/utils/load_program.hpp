// Copyright (C) 2025 Category Labs, Inc.
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

#pragma once

#include <charconv>
#include <cstdint>
#include <iterator>
#include <stdexcept>
#include <system_error>
#include <vector>

namespace monad::vm::utils
{

    /**
     * Parse a range of hexadecimal characters into a vector of bytes.
     */
    template <std::random_access_iterator It>
    std::vector<uint8_t> parse_hex_program(It begin, It end)
    {
        auto hex_size = std::distance(begin, end);
        auto program =
            std::vector<uint8_t>(static_cast<std::size_t>(hex_size / 2));

        auto output_it = program.begin();
        auto out_end = program.end();

        for (auto input_it = begin; input_it != end && output_it != out_end;
             input_it += 2, output_it++) {
            auto *begin_char = &*input_it;
            auto *end_char = begin_char + 2;

            auto result = std::from_chars(begin_char, end_char, *output_it, 16);

            // There's a subtle error case where the first character in the pair
            // we're examining is valid, but the second one isn't. In that case,
            // `from_chars` doesn't return an error code, but points the result
            // pointer somewhere other than where we expected the end of the
            // byte to be.
            if (result.ec != std::errc() || result.ptr != end_char) {
                throw std::invalid_argument(
                    "Malformed hex input when parsing program");
            }
        }

        return program;
    }

    /**
     * Parse a contiguous container of hexadecimal characters into a vector of
     * bytes.
     *
     * For example, parsing the string literal `"7F"` will produce a 1-element
     * output vector containing the single byte `u'\x7F'`. This function can be
     * used to parse contract hex dumps produced by the Solidity compiler into
     * the compiler's intermediate representations.
     *
     * Any characters outside the hexadecimal range `[0-9A-F]` will cause an
     * exception of type `std::invalid_argument` to be thrown.
     *
     * If the input range has an odd length (i.e. a trailing character), that
     * character will be silently ignored, even if it would otherwise have
     * caused a parse error.
     */
    template <typename Container>
    std::vector<uint8_t> parse_hex_program(Container const &c)
    {
        using std::begin;
        using std::end;
        return parse_hex_program(begin(c), end(c));
    }

}

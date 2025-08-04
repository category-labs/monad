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

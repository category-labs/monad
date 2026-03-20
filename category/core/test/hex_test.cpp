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

#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string_view>

using namespace monad;

using namespace std::literals;

// Defined here to avoid including category/execution/ethereum/core/address.hpp
// in this test, which would be a circular dependency between core/ and
// execution/.
struct Address
{
    uint8_t bytes[20];

    friend constexpr bool
    operator==(Address const &a, Address const &b) noexcept = default;
};

TEST(FromHexChar, decodes_digit_characters)
{
    static_assert(from_hex_char('0') == 0);
    static_assert(from_hex_char('1') == 1);
    static_assert(from_hex_char('2') == 2);
    static_assert(from_hex_char('3') == 3);
    static_assert(from_hex_char('4') == 4);
    static_assert(from_hex_char('5') == 5);
    static_assert(from_hex_char('6') == 6);
    static_assert(from_hex_char('7') == 7);
    static_assert(from_hex_char('8') == 8);
    static_assert(from_hex_char('9') == 9);
}

TEST(FromHexChar, decodes_lowercase_a_through_f)
{
    static_assert(from_hex_char('a') == 10);
    static_assert(from_hex_char('b') == 11);
    static_assert(from_hex_char('c') == 12);
    static_assert(from_hex_char('d') == 13);
    static_assert(from_hex_char('e') == 14);
    static_assert(from_hex_char('f') == 15);
}

TEST(FromHexChar, decodes_uppercase_A_through_F)
{
    static_assert(from_hex_char('A') == 10);
    static_assert(from_hex_char('B') == 11);
    static_assert(from_hex_char('C') == 12);
    static_assert(from_hex_char('D') == 13);
    static_assert(from_hex_char('E') == 14);
    static_assert(from_hex_char('F') == 15);
}

TEST(FromHexChar, returns_nullopt_for_non_hex_character)
{
    static_assert(from_hex_char('g') == std::nullopt);
    static_assert(from_hex_char('G') == std::nullopt);
    static_assert(from_hex_char('/') == std::nullopt);
    static_assert(from_hex_char(':') == std::nullopt);
    static_assert(from_hex_char('@') == std::nullopt);
    static_assert(from_hex_char('[') == std::nullopt);
    static_assert(from_hex_char('`') == std::nullopt);
    static_assert(from_hex_char('{') == std::nullopt);
    static_assert(from_hex_char('O') == std::nullopt);
    static_assert(from_hex_char('x') == std::nullopt);
}

TEST(FromHexChar, returns_nullopt_for_null_terminator)
{
    static_assert(from_hex_char('\0') == std::nullopt);
}

TEST(ParseHexByte, decodes_two_character_pair_and_advances_view)
{
    auto in = "1a2b"sv;
    uint8_t byte;
    EXPECT_TRUE(parse_hex_byte(in, byte));
    EXPECT_EQ(byte, 0x1a);
    EXPECT_EQ(in, "2b"sv);
}

TEST(ParseHexByte, fails_on_single_remaining_character)
{
    auto in = "1"sv;
    uint8_t byte;
    EXPECT_FALSE(parse_hex_byte(in, byte));
    EXPECT_EQ(in, "1"sv);
}

TEST(ParseHexByte, fails_on_empty_view)
{
    auto in = ""sv;
    uint8_t byte;
    EXPECT_FALSE(parse_hex_byte(in, byte));
    EXPECT_EQ(in, ""sv);
}

TEST(ParseHexByte, fails_when_first_nibble_is_invalid)
{
    auto in = "g1"sv;
    uint8_t byte;
    EXPECT_FALSE(parse_hex_byte(in, byte));
    EXPECT_EQ(in, "g1"sv);
}

TEST(ParseHexByte, fails_when_second_nibble_is_invalid)
{
    auto in = "1g"sv;
    uint8_t byte;
    EXPECT_FALSE(parse_hex_byte(in, byte));
    EXPECT_EQ(in, "1g"sv);
}

TEST(SkipOptionalHexPrefix, strips_lowercase_0x_prefix)
{
    auto in = "0x1a2b"sv;
    skip_optional_hex_prefix(in);
    EXPECT_EQ(in, "1a2b"sv);
}

TEST(SkipOptionalHexPrefix, leaves_input_without_prefix_unchanged)
{
    auto in = "1a2b"sv;
    skip_optional_hex_prefix(in);
    EXPECT_EQ(in, "1a2b"sv);
}

TEST(SkipOptionalHexPrefix, leaves_single_zero_unchanged)
{
    auto in = "0"sv;
    skip_optional_hex_prefix(in);
    EXPECT_EQ(in, "0"sv);
}

TEST(SkipOptionalHexPrefix, strips_prefix_in_invalid)
{
    auto in = "0x$$"sv;
    skip_optional_hex_prefix(in);
    EXPECT_EQ(in, "$$"sv);
}

TEST(SkipOptionalHexPrefix, leaves_empty_input_unchanged)
{
    auto in = ""sv;
    skip_optional_hex_prefix(in);
    EXPECT_EQ(in, ""sv);
}

TEST(FromHexFixed, decodes_full_length_address)
{
    auto const hex = "0123456789abcdef0123456789abcdef01234567"sv;
    auto const expected =
        Address{{0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23,
                 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67}};
    EXPECT_EQ(from_hex<Address>(hex).value(), expected);
}

TEST(FromHexFixed, decodes_full_length_bytes32)
{
    auto const hex =
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"sv;
    auto const expected = bytes32_t{
        {0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45,
         0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab,
         0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef}};
    EXPECT_EQ(from_hex<bytes32_t>(hex).value(), expected);
}

TEST(FromHexFixed, right_aligns_short_input)
{
    auto const hex = "89abcdef01234567"sv;
    auto const expected =
        Address{{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                 0x00, 0x00, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67}};
    EXPECT_EQ(from_hex<Address>(hex).value(), expected);
}

TEST(FromHexFixed, accepts_0x_prefix)
{
    auto const hex = "0x0123456789abcdef0123456789abcdef01234567"sv;
    auto const expected =
        Address{{0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23,
                 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67}};
    EXPECT_EQ(from_hex<Address>(hex).value(), expected);
}

TEST(FromHexFixed, returns_nullopt_for_odd_length_input)
{
    auto const hex = "123"sv;
    EXPECT_EQ(from_hex<Address>(hex), std::nullopt);
}

TEST(FromHexFixed, returns_nullopt_when_input_exceeds_type_size)
{
    auto const hex = "0123456789abcdef0123456789abcdef0123456789"sv;
    EXPECT_EQ(from_hex<Address>(hex), std::nullopt);
}

TEST(FromHexFixed, returns_nullopt_for_invalid_character)
{
    auto const hex = "0123456789abcdef0123456789abcdef0123456g"sv;
    EXPECT_EQ(from_hex<Address>(hex), std::nullopt);
}

TEST(FromHexFixed, decodes_all_zeros)
{
    auto const hex = "0000000000000000000000000000000000000000"sv;
    auto const expected = Address{};
    EXPECT_EQ(from_hex<Address>(hex).value(), expected);
}

TEST(FromHexFixed, decodes_all_ff)
{
    auto const hex = "ffffffffffffffffffffffffffffffffffffffff"sv;
    auto const expected =
        Address{{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff}};
    EXPECT_EQ(from_hex<Address>(hex).value(), expected);
}

TEST(FromHexFixed, decodes_empty_bytes32)
{
    auto const hex = ""sv;
    auto const expected = bytes32_t{};
    EXPECT_EQ(from_hex<bytes32_t>(hex).value(), expected);
}

TEST(FromHexDynamic, decodes_variable_length_bytes)
{
    auto const hex = "0123456789abcdef"sv;
    auto const expected =
        byte_string{0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef};
    EXPECT_EQ(from_hex(hex).value(), expected);
}

TEST(FromHexDynamic, accepts_0x_prefix)
{
    auto const hex = "0x0123456789abcdef"sv;
    auto const expected =
        byte_string{0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef};
    EXPECT_EQ(from_hex(hex).value(), expected);
}

TEST(FromHexDynamic, returns_empty_for_empty_input)
{
    auto const hex = ""sv;
    auto const expected = byte_string{};
    EXPECT_EQ(from_hex(hex).value(), expected);
}

TEST(FromHexDynamic, returns_empty_for_bare_0x_prefix)
{
    auto const hex = "0x"sv;
    auto const expected = byte_string{};
    EXPECT_EQ(from_hex(hex).value(), expected);
}

TEST(FromHexDynamic, returns_nullopt_for_odd_length_input)
{
    auto const hex = "123"sv;
    EXPECT_EQ(from_hex(hex), std::nullopt);
}

TEST(FromHexDynamic, returns_nullopt_for_invalid_character)
{
    auto const hex = "0123456789abcdeg"sv;
    EXPECT_EQ(from_hex(hex), std::nullopt);
}

TEST(ToHexChar, encodes_0_through_9)
{
    static_assert(to_hex_char(0) == '0');
    static_assert(to_hex_char(1) == '1');
    static_assert(to_hex_char(2) == '2');
    static_assert(to_hex_char(3) == '3');
    static_assert(to_hex_char(4) == '4');
    static_assert(to_hex_char(5) == '5');
    static_assert(to_hex_char(6) == '6');
    static_assert(to_hex_char(7) == '7');
    static_assert(to_hex_char(8) == '8');
    static_assert(to_hex_char(9) == '9');
}

TEST(ToHexChar, encodes_10_through_15_as_lowercase)
{
    static_assert(to_hex_char(10) == 'a');
    static_assert(to_hex_char(11) == 'b');
    static_assert(to_hex_char(12) == 'c');
    static_assert(to_hex_char(13) == 'd');
    static_assert(to_hex_char(14) == 'e');
    static_assert(to_hex_char(15) == 'f');
}

TEST(ToHexByte, encodes_zero_as_00)
{
    EXPECT_EQ(to_hex(0x0), "00");
}

TEST(ToHexByte, encodes_ff)
{
    EXPECT_EQ(to_hex(0xff), "ff");
}

TEST(ToHexByte, encodes_single_digit_value_with_leading_zero)
{
    EXPECT_EQ(to_hex(0xa), "0a");
    EXPECT_EQ(to_hex(0x5), "05");
}

TEST(ToHexBytes, encodes_empty_as_empty_string)
{
    EXPECT_EQ(to_hex(byte_string{}), "");
}

TEST(ToHexBytes, encodes_multi_byte_sequence)
{
    auto const bytes =
        byte_string{0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef};
    EXPECT_EQ(to_hex(bytes), "0123456789abcdef");
}

TEST(ToHexBytes, roundtrips_with_from_hex)
{
    auto const original = byte_string{
        0x00,
        0x01,
        0x02,
        0x03,
        0x04,
        0x05,
        0x06,
        0x07,
        0x08,
        0x09,
        0x0a,
        0x0b,
        0x0c,
        0x0d,
        0x0e,
        0x0f};
    auto const hex = to_hex(original);
    EXPECT_EQ(from_hex(hex).value(), original);
}

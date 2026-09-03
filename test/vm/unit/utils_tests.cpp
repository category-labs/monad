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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/utils/load_program.hpp>
#include <category/vm/utils/parser.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

using namespace monad::vm::compiler;
using namespace monad::vm::utils;

void test_case(std::string const &in, std::vector<uint8_t> const &out)
{
    ASSERT_EQ(parse_hex_program(in), out);
}

TEST(HexParsingTest, EmptyInput)
{
    test_case("", {});
}

TEST(HexParsingTest, SingleBytes)
{
    test_case("00", {u'\x00'});
    test_case("FF", {u'\xFF'});
    test_case("AA", {u'\xAA'});
    test_case("16", {u'\x16'});
    test_case("54", {u'\x54'});
    test_case("07", {u'\x07'});
    test_case("E0", {u'\xE0'});
}

TEST(HexParsingTest, MultipleBytes)
{
    test_case("00AABB1122", {u'\x00', u'\xAA', u'\xBB', u'\x11', u'\x22'});
}

TEST(HexParsingTest, TrailingCharacters)
{
    test_case("A", {});
    test_case("Y", {});
    test_case("AAB", {u'\xAA'});
    test_case("AAZ", {u'\xAA'});
    test_case("BBCCD", {u'\xBB', u'\xCC'});
}

TEST(HexParsingTest, ErrorHandling)
{
    EXPECT_THROW(parse_hex_program("GG"), std::invalid_argument);
    EXPECT_THROW(parse_hex_program("00AJ"), std::invalid_argument);
    EXPECT_THROW(parse_hex_program("0011223U445566"), std::invalid_argument);
}

TEST(ShowOpcodesTest, WellFormedPush)
{
    ASSERT_EQ(
        show_opcodes({0x61, 0x12, 0x34, 0x01, 0x00}),
        "[0x0] 0x61 PUSH2\n"
        "[0x1] 0x12\n"
        "[0x2] 0x34\n"
        "[0x3] 0x1 ADD\n"
        "[0x4] 0x0 STOP\n");

    // PUSH0 has no immediate region at all.
    ASSERT_EQ(
        show_opcodes({0x5F, 0x00}),
        "[0x0] 0x5f PUSH0\n"
        "[0x1] 0x0 STOP\n");
}

TEST(ShowOpcodesTest, TruncatedPushImmediate)
{
    // A trailing push whose immediate region runs off the end of the input
    // must not read past the buffer; the shortfall is reported instead.
    ASSERT_EQ(
        show_opcodes({0x7F}),
        "[0x0] 0x7f PUSH32\n"
        "// truncated PUSH32: 32 of 32 immediate bytes missing "
        "(zero-padded when executed)\n");

    ASSERT_EQ(
        show_opcodes({0x63, 0xDE, 0xAD}),
        "[0x0] 0x63 PUSH4\n"
        "[0x1] 0xde\n"
        "[0x2] 0xad\n"
        "// truncated PUSH4: 2 of 4 immediate bytes missing "
        "(zero-padded when executed)\n");
}

TEST(ShowOpcodesTest, TruncatedPushAtNonZeroOffset)
{
    // Keep the truncated push off offset 0, so that the position-dependent
    // term of the remaining-byte count is exercised too: a bound of
    // `size() - 1` rather than `size() - i - 1` still overruns here.
    ASSERT_EQ(
        show_opcodes({0x00, 0x63, 0xDE}),
        "[0x0] 0x0 STOP\n"
        "[0x1] 0x63 PUSH4\n"
        "[0x2] 0xde\n"
        "// truncated PUSH4: 3 of 4 immediate bytes missing "
        "(zero-padded when executed)\n");
}

TEST(ShowOpcodesTest, EveryPushTruncationLength)
{
    // Exhaust every PUSHN against every possible immediate length, so a
    // sanitizer build catches any out-of-bounds read. The leading STOP keeps
    // the push off offset 0.
    for (uint8_t op = PUSH1; op <= PUSH32; ++op) {
        size_t const n = static_cast<size_t>(op - PUSH0);
        for (size_t have = 0; have <= n; ++have) {
            std::vector<uint8_t> code(have + 2, uint8_t{0xAA});
            code[0] = STOP;
            code[1] = op;
            auto const out = show_opcodes(code);
            EXPECT_EQ(out.contains("truncated"), have < n)
                << "PUSH" << n << " with " << have << " immediate bytes";
        }
    }
}

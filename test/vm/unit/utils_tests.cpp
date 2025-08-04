#include <category/vm/utils/load_program.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

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

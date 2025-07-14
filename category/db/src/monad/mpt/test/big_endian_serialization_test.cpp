#include "gtest/gtest.h"

#include <category/core/hex_literal.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/util.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <cstdint>
#include <stdexcept>

using namespace monad::mpt;
using namespace monad::literals;

TEST(serialize_to_big_endian, test)
{
    uint64_t const n = 0x1122334455667788;
    EXPECT_EQ(serialize_as_big_endian<8>(n), 0x1122334455667788_hex);
    EXPECT_EQ(serialize_as_big_endian<6>(n), 0x334455667788_hex);
    EXPECT_EQ(serialize_as_big_endian<2>(n), 0x7788_hex);

    uint32_t const n2 = 0x11223344;
    EXPECT_EQ(serialize_as_big_endian<4>(n2), 0x11223344_hex);
    EXPECT_EQ(serialize_as_big_endian<2>(n2), 0x3344_hex);
}

TEST(deserialize_from_big_endian_nibbles, test)
{
    Nibbles const a{0x00112233_hex};
    EXPECT_EQ(deserialize_from_big_endian<uint32_t>(a), 0x112233);

    Nibbles const b{0x112233_hex};
    EXPECT_EQ(deserialize_from_big_endian<uint32_t>(b), 0x112233);

    Nibbles const c{0xaabbccdd00112233_hex};
    EXPECT_THROW(deserialize_from_big_endian<uint8_t>(c), std::runtime_error);
    EXPECT_THROW(deserialize_from_big_endian<uint16_t>(c), std::runtime_error);
    EXPECT_THROW(deserialize_from_big_endian<uint32_t>(c), std::runtime_error);
    EXPECT_EQ(deserialize_from_big_endian<uint64_t>(c), 0xaabbccdd00112233);
}

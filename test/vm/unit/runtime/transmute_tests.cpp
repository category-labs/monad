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

#include "fixture.hpp"

#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

namespace
{
    evmc::bytes32 get_test_bytes32()
    {
        evmc::bytes32 b;
        for (std::uint8_t i = 0; i < 32; ++i) {
            b.bytes[31 - i] = i + 1;
        }
        return b;
    }

    evmc::address get_test_address()
    {
        evmc::address b;
        for (std::uint8_t i = 0; i < 20; ++i) {
            b.bytes[19 - i] = i + 1;
        }
        return b;
    }

    uint256_t get_test_uint256()
    {
        uint256_t u;
        uint8_t *b = u.as_bytes();
        for (std::uint8_t i = 0; i < 32; ++i) {
            b[i] = i + 1;
        }
        return u;
    }
};

TEST_F(RuntimeTest, TransmuteBytes32)
{
    evmc::bytes32 const b = get_test_bytes32();
    uint256_t const u = get_test_uint256();
    ASSERT_EQ(bytes32_from_uint256(u), b);
    ASSERT_EQ(u, uint256_from_bytes32(b));
}

TEST_F(RuntimeTest, TransmuteAddress)
{
    evmc::address const a = get_test_address();
    uint256_t u = get_test_uint256();
    ASSERT_EQ(address_from_uint256(u), a);
    uint8_t *b = u.as_bytes();
    for (auto i = 20; i < 32; ++i) {
        b[i] = 0;
    }
    ASSERT_EQ(u, uint256_from_address(a));
}

TEST_F(RuntimeTest, LoadBounded)
{
    uint8_t src_buffer[32];
    for (uint8_t i = 0; i < 32; ++i) {
        src_buffer[i] = i + 1;
    }
    for (int64_t n = -5; n <= 37; ++n) {
        uint256_t expected_le;
        if (n > 0) {
            std::memcpy(
                expected_le.as_bytes(),
                src_buffer,
                static_cast<size_t>(std::min(n, int64_t{32})));
        }

        auto x = monad_vm_runtime_load_bounded_le(
            src_buffer, std::min(n, int64_t{32}));
        uint256_t le1{x};
        ASSERT_EQ(le1, expected_le);

        uint256_t le2 = uint256_load_bounded_le(src_buffer, n);
        ASSERT_EQ(le2, expected_le);

        uint256_t be = uint256_load_bounded_be(src_buffer, n);
        ASSERT_EQ(be, expected_le.to_be());
    }
}

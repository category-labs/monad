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
#include <category/vm/interpreter/intercode.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <vector>

using namespace monad::vm::interpreter;

using enum monad::vm::compiler::EvmOpCode;

template <typename... Args>
auto make_intercode(Args... args)
{
    return Intercode{std::array<std::uint8_t, sizeof...(args)>{
        static_cast<std::uint8_t>(args)...}};
}

TEST(Intercode, CodeSizeEmpty)
{
    auto const code = make_intercode();
    ASSERT_EQ(code.size(), 0);
}

TEST(Intercode, CodeSizeNonEmpty)
{
    auto const code = make_intercode(PUSH1, 0x01, PUSH0, ADD);
    ASSERT_EQ(code.size(), 4);
}

TEST(Intercode, Code)
{
    auto const ops = std::vector<std::uint8_t>{
        PUSH4,
        0x01,
        0x02,
        0x03,
        0x04,
        JUMP,
        SUB,
        RETURN,
        SELFDESTRUCT,
    };

    auto const code = Intercode(ops);

    for (auto i = 0u; i < ops.size(); ++i) {
        ASSERT_EQ(ops[i], code.code()[i]);
    }
}

TEST(Intercode, Jumpdests)
{
    auto const code = make_intercode(
        JUMPDEST, ADD, SUB, PUSH3, 0x5B, JUMPDEST, JUMPDEST, JUMPDEST);

    ASSERT_TRUE(code.is_jumpdest(0));
    ASSERT_FALSE(code.is_jumpdest(1));
    ASSERT_FALSE(code.is_jumpdest(2));
    ASSERT_FALSE(code.is_jumpdest(3));
    ASSERT_FALSE(code.is_jumpdest(4));
    ASSERT_FALSE(code.is_jumpdest(5));
    ASSERT_FALSE(code.is_jumpdest(6));
    ASSERT_TRUE(code.is_jumpdest(7));
    ASSERT_FALSE(code.is_jumpdest(8));
    ASSERT_FALSE(code.is_jumpdest(3894));
}

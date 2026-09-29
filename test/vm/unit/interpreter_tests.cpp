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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>

#include <test/vm/utils/test_context.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
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

namespace
{
    class InterpreterStack : public testing::Test
    {
    protected:
        static constexpr size_t stack_capacity = 1024;

        // Slot 0 is the empty-stack marker. The extra slot after the 1024
        // values detects writes beyond the interpreter's stack capacity.
        alignas(32) std::array<monad::uint256_t, stack_capacity + 2> stack_{};
        monad::vm::test::TestContext ctx_;

        void SetUp() override
        {
            stack_.front() = monad::uint256_t{0xdead};
            stack_.back() = monad::uint256_t{0xbeef};
            ctx_->gas_remaining = 1'000'000;
        }

        void
        run(std::vector<uint8_t> const &bytecode,
            monad::vm::runtime::StatusCode const expected_status)
        {
            Intercode const code{bytecode};
            execute<monad::EvmTraits<MONAD_ETH_PRAGUE>>(
                *ctx_, code, stack_.data());

            EXPECT_EQ(ctx_->result.status, expected_status);
            EXPECT_EQ(stack_.front(), monad::uint256_t{0xdead});
            EXPECT_EQ(stack_.back(), monad::uint256_t{0xbeef});
        }

        static std::vector<uint8_t> full_stack_code()
        {
            std::vector<uint8_t> code;
            for (size_t i = 1; i <= stack_capacity; ++i) {
                code.insert(
                    code.end(),
                    {PUSH2,
                     static_cast<uint8_t>(i >> 8),
                     static_cast<uint8_t>(i)});
            }
            return code;
        }
    };
}

TEST_F(InterpreterStack, Empty)
{
    run({}, monad::vm::runtime::StatusCode::Success);
}

TEST_F(InterpreterStack, PopEmpty)
{
    run({POP}, monad::vm::runtime::StatusCode::Error);
}

TEST_F(InterpreterStack, PushPopPush)
{
    run({PUSH1, 1, POP, PUSH1, 2}, monad::vm::runtime::StatusCode::Success);
    EXPECT_EQ(stack_[1], monad::uint256_t{2});
}

TEST_F(InterpreterStack, Full)
{
    run(full_stack_code(), monad::vm::runtime::StatusCode::Success);
    for (size_t i = 1; i <= stack_capacity; ++i) {
        EXPECT_EQ(stack_[i], monad::uint256_t{i}) << "slot " << i;
    }
}

TEST_F(InterpreterStack, DupOverflow)
{
    auto code = full_stack_code();
    code.push_back(DUP1);
    run(code, monad::vm::runtime::StatusCode::Error);
    EXPECT_EQ(stack_[stack_capacity], monad::uint256_t{stack_capacity});
}

TEST_F(InterpreterStack, PushOverflow)
{
    auto code = full_stack_code();
    code.push_back(PUSH0);
    run(code, monad::vm::runtime::StatusCode::Error);
    EXPECT_EQ(stack_[stack_capacity], monad::uint256_t{stack_capacity});
}

TEST_F(InterpreterStack, PopBackToEmpty)
{
    auto code = full_stack_code();
    code.insert(code.end(), stack_capacity, POP);
    code.insert(code.end(), {PUSH1, 42});
    run(code, monad::vm::runtime::StatusCode::Success);
    EXPECT_EQ(stack_[1], monad::uint256_t{42});
}

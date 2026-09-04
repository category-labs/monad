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

#include <category/core/assert.h>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/types.hpp>

#include <evmc/evmc.h>

#include <cstddef>
#include <cstdint>

namespace monad::vm::interpreter
{
    using enum runtime::StatusCode;

    template <uint8_t Instr, Traits traits>
    [[gnu::always_inline]] inline void check_requirements(
        runtime::Context &ctx, Intercode const &,
        uint256_t const *const stack_bottom, uint256_t *const stack_top,
        int64_t &gas_remaining)
    {
        static constexpr auto info = compiler::opcode_table<traits>[Instr];

        if constexpr (info.min_gas > 0) {
            gas_remaining -= info.min_gas;

            if (MONAD_UNLIKELY(gas_remaining < 0)) {
                ctx.exit(OutOfGas);
            }
        }

        if constexpr (info.min_stack == 0 && info.stack_increase == 0) {
            return;
        }

        auto const stack_size = stack_top - stack_bottom;
        MONAD_DEBUG_ASSERT(stack_size <= 1024);

        if constexpr (info.min_stack > 0) {
            if (MONAD_UNLIKELY(stack_size < info.min_stack)) {
                ctx.exit(Error);
            }
        }

        if constexpr (info.stack_increase > 0) {
            static constexpr auto delta = info.stack_increase - info.min_stack;
            static constexpr auto max_safe_size = 1024 - delta;

            // We only need to emit the overflow check if this instruction could
            // actually cause an overflow; if the instruction could only leave
            // the stack with >1024 elements if it _began_ with >1024, then we
            // assume that the input stack was valid and elide the check.
            if constexpr (max_safe_size < 1024) {
                if (MONAD_UNLIKELY(stack_size > max_safe_size)) {
                    ctx.exit(Error);
                }
            }
        }
    }

    struct Eip8024Operands
    {
        ptrdiff_t n;
        ptrdiff_t m; // meaningful only for EXCHANGE
    };

    // Dynamic analog of check_requirements for the EIP-8024 opcodes: validates
    // the immediate, charges gas, and checks the operand-dependent stack depth.
    template <uint8_t Instr, Traits traits>
    [[gnu::always_inline]] inline Eip8024Operands check_requirements_eip8024(
        runtime::Context &ctx, uint256_t const *const stack_bottom,
        uint256_t const *const stack_top, int64_t &gas_remaining,
        uint8_t const imm)
    {
        static constexpr auto info = compiler::opcode_table<traits>[Instr];
        static constexpr bool is_exchange = Instr == compiler::EXCHANGE;

        // Validate the immediate before charging gas: a disallowed encoding is
        // invalid regardless of the gas available, so charging first would
        // report OutOfGas for a malformed instruction. Matches `invalid` and
        // decode_eip8024, which turns a disallowed immediate into
        // Terminator::InvalidInstruction at analysis time.
        if (MONAD_UNLIKELY(!compiler::eip8024_immediate_valid(Instr, imm))) {
            ctx.exit(Error);
        }

        gas_remaining -= info.min_gas;
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            ctx.exit(OutOfGas);
        }

        auto const ops = [imm]() -> Eip8024Operands {
            if constexpr (is_exchange) {
                auto const [n_val, m_val] = compiler::eip8024_decode_pair(imm);
                return {n_val, m_val};
            }
            else {
                return {compiler::eip8024_decode_single(imm), 0};
            }
        }();

        // The deepest slot touched: EXCHANGE reaches m + 1, DUPN reaches n and
        // SWAPN reaches n + 1.
        ptrdiff_t const min_stack =
            is_exchange ? ops.m + 1
                        : (Instr == compiler::DUPN ? ops.n : ops.n + 1);

        auto const stack_size = stack_top - stack_bottom;
        MONAD_DEBUG_ASSERT(stack_size <= 1024);
        if (MONAD_UNLIKELY(stack_size < min_stack)) {
            ctx.exit(Error);
        }

        // Only DUPN grows the stack; net-zero opcodes cannot overflow a valid
        // stack, so the check is elided (mirrors check_requirements).
        static constexpr auto delta = info.stack_increase - info.min_stack;
        if constexpr (delta > 0) {
            static constexpr auto max_safe_size = 1024 - delta;
            if (MONAD_UNLIKELY(stack_size > max_safe_size)) {
                ctx.exit(Error);
            }
        }

        return ops;
    }

    [[gnu::always_inline]] inline void
    push(uint256_t *const stack_top, uint256_t const &x)
    {
        *(stack_top + 1) = x;
    }

    [[gnu::always_inline]] inline uint256_t &pop(uint256_t *&stack_top)
    {
        return *stack_top--;
    }

    [[gnu::always_inline]] inline auto pop_for_overwrite(uint256_t *&stack_top)
    {
        auto const &a = pop(stack_top);
        return std::tie(a, *stack_top);
    }

    [[gnu::always_inline]] inline auto top_two(uint256_t *const stack_top)
    {
        auto const &a = *stack_top;
        return std::tie(a, *(stack_top - 1));
    }
}

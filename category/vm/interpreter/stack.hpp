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

#include <category/vm/core/assert.h>
#include <category/vm/interpreter/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.h>

#include <cstdint>

namespace monad::vm::interpreter
{
    using enum runtime::StatusCode;

    template <std::uint8_t Instr, evmc_revision Rev>
    [[gnu::always_inline]] inline void check_requirements(
        runtime::Context &ctx, Intercode const &,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t &gas_remaining)
    {
        static constexpr auto info = compiler::opcode_table<Rev>[Instr];

        if constexpr (info.min_gas > 0) {
            gas_remaining -= info.min_gas;

            if (MONAD_VM_UNLIKELY(gas_remaining < 0)) {
                ctx.exit(OutOfGas);
            }
        }

        if constexpr (info.min_stack == 0 && info.stack_increase == 0) {
            return;
        }

        auto const stack_size = stack_top - stack_bottom;
        MONAD_VM_DEBUG_ASSERT(stack_size <= 1024);

        if constexpr (info.min_stack > 0) {
            if (MONAD_VM_UNLIKELY(stack_size < info.min_stack)) {
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
                if (MONAD_VM_UNLIKELY(stack_size > max_safe_size)) {
                    ctx.exit(Error);
                }
            }
        }
    }

    [[gnu::always_inline]] inline void
    push(runtime::uint256_t *stack_top, runtime::uint256_t const &x)
    {
        *(stack_top + 1) = x;
    }

    [[gnu::always_inline]] inline runtime::uint256_t &
    pop(runtime::uint256_t *&stack_top)
    {
        return *stack_top--;
    }

    [[gnu::always_inline]] inline auto
    pop_for_overwrite(runtime::uint256_t *&stack_top)
    {
        auto const &a = pop(stack_top);
        return std::tie(a, *stack_top);
    }

    [[gnu::always_inline]] inline auto
    top_two(runtime::uint256_t *const stack_top)
    {
        auto const &a = *stack_top;
        return std::tie(a, *(stack_top - 1));
    }
}

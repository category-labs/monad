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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/interpreter/handler_policy.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/stack_top.hpp>
#include <category/vm/runtime/types.hpp>

#include <array>
#include <cstdint>

// Bias stack_lower_bound from the array's beginning. With StackTop's one-past
// pointer, a bias of one makes both one- and two-operand checks compare
// directly against stack_lower_bound (>= and > respectively).
#if defined(MONAD_ZKVM_ZISK)
    #define MONAD_VM_STACK_LOWER_BOUND_BIAS 1
#else
    #define MONAD_VM_STACK_LOWER_BOUND_BIAS 0
#endif

// ZisK passes the stack limit instead of the code analysis to avoid loading
// it from ctx on each overflow check. Code metadata is read through FrameCode.
// Other targets keep passing the analysis and load the limit from ctx.
#if defined(MONAD_ZKVM_ZISK)
    #define MONAD_VM_DISPATCH_STATE_TYPE uint256_t const *
    #define MONAD_VM_DISPATCH_STATE_PARAM uint256_t const *const stack_limit
    #define MONAD_VM_DISPATCH_STATE_ARG stack_limit
    #define MONAD_VM_CODE_VIEW (::monad::vm::interpreter::FrameCode{ctx})
    #define MONAD_VM_STACK_LIMIT stack_limit
#else
    #define MONAD_VM_DISPATCH_STATE_TYPE Intercode const &
    #define MONAD_VM_DISPATCH_STATE_PARAM Intercode const &analysis
    #define MONAD_VM_DISPATCH_STATE_ARG analysis
    #define MONAD_VM_CODE_VIEW analysis
    #define MONAD_VM_STACK_LIMIT ctx.stack_limit
#endif

namespace monad::vm::interpreter
{
    // Use void const * to pass either a slot base or a pointer table without
    // making InstrEval recursive.
    using InstrEval = void MONAD_VM_POINTER_CALL (*)(
        runtime::Context &, MONAD_VM_DISPATCH_STATE_TYPE, uint256_t const *,
        StackTop, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    using InstrTable = std::array<InstrEval, 256>;

#if defined(MONAD_ZKVM_ZISK)
    // View of the running code metadata saved by execute().
    struct FrameCode
    {
        runtime::Context const &ctx;

        [[gnu::always_inline]] uint8_t const *code() const noexcept
        {
            return ctx.code_base;
        }

        [[gnu::always_inline]] size_t size() const noexcept
        {
            return ctx.code_bound;
        }

        // PUSH2 destinations fit in the bitmap even beyond the code end.
        [[gnu::always_inline]] bool
        is_jumpdest16(size_t const pc) const noexcept
        {
            return Intercode::JumpdestMap::test(ctx.jumpdest_words, pc);
        }

        [[gnu::always_inline]] bool is_jumpdest(size_t const pc) const noexcept
        {
            return pc < ctx.code_bound &&
                   Intercode::JumpdestMap::test(ctx.jumpdest_words, pc);
        }
    };
#endif
}

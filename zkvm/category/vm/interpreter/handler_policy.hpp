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

#pragma once

#if !defined(MONAD_ZKVM_ZISK)
    #include_next <category/vm/interpreter/handler_policy.hpp>
#else
    #include <category/vm/interpreter/intercode.hpp>
    #include <category/vm/runtime/types.hpp>

    #include <cstddef>
    #include <cstdint>

/**
 * On ZisK a revision's handlers are laid out in slots, one per opcode
 * (execute.cpp), and the dispatch computes a handler's address from its opcode
 * instead of loading it from a table. A handler is compiled into its slot and
 * nowhere else; a twin a handler tail-calls stays a function of its own
 * (MONAD_VM_TWIN_CALL), and a handler pointer carries no attribute
 * (MONAD_VM_POINTER_CALL).
 */
    #define MONAD_VM_INSTRUCTION_CALL __attribute__((always_inline)) inline
    #define MONAD_VM_INLINE_INSTRUCTION_CALL MONAD_VM_INSTRUCTION_CALL
    #define MONAD_VM_TWIN_CALL
    #define MONAD_VM_POINTER_CALL

// Bias stack_lower_bound from the array's beginning. With StackTop's one-past
// pointer, a bias of one makes both one- and two-operand checks compare
// directly against stack_lower_bound (>= and > respectively).
    #define MONAD_VM_STACK_LOWER_BOUND_BIAS 1

// ZisK passes the stack limit instead of the code analysis to avoid loading
// it from ctx on each overflow check. Code metadata is read through FrameCode.
    #define MONAD_VM_DISPATCH_STATE_TYPE uint256_t const *
    #define MONAD_VM_DISPATCH_STATE_PARAM uint256_t const *stack_limit
    #define MONAD_VM_DISPATCH_STATE_ARG stack_limit
    #define MONAD_VM_CODE_VIEW (::monad::vm::interpreter::FrameCode{ctx})
    #define MONAD_VM_STACK_LIMIT stack_limit

// On ZisK, pass the table base in a seventh register argument to avoid
// reloading it at each dispatch: the slots' base where the revision has them
// (dispatch_table, instruction_table.hpp), the table's otherwise.
    #define MONAD_VM_TBL_TYPE , void const *
    #define MONAD_VM_TBL_PARAM , void const *table_base
    #define MONAD_VM_TBL_ARG , table_base
    #define MONAD_VM_TABLE_REF (dispatch_table<traits>(table_base))

namespace monad::vm::interpreter
{
    // View of the running code metadata saved by execute().
    struct FrameCode
    {
        runtime::Context const &ctx;

        // Recover the code start; code() + dst + 1 folds to landing_base + dst.
        [[gnu::always_inline]] uint8_t const *code() const noexcept
        {
            return ctx.landing_base - 1;
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
}
#endif

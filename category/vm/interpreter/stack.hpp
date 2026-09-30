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
#include <category/vm/interpreter/stack_top.hpp>
#include <category/vm/interpreter/types.hpp>

#include <evmc/evmc.h>

#include <cstddef>
#include <cstdint>

#if defined(MONAD_ZKVM_ZISK) && !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
    #define MONAD_VM_SHOULD_CHECK_GAS(Instr, DYNAMIC)                          \
        ::monad::vm::interpreter::should_check_gas((Instr), (DYNAMIC))
#else
    #define MONAD_VM_SHOULD_CHECK_GAS(Instr, DYNAMIC) true
#endif

// Shared gas and stack checks; EXIT(status) selects how to leave on failure.
#define MONAD_VM_CHECK_REQUIREMENTS(Instr, EXIT)                               \
    MONAD_VM_CHECK_REQUIREMENTS_AT(Instr, 0, EXIT)

// SHIFT is the net stack change from earlier fused opcodes; 0 checks the
// stack at handler entry.
#define MONAD_VM_CHECK_REQUIREMENTS_AT(Instr, SHIFT, EXIT)                     \
    MONAD_VM_CHECK_REQUIREMENTS_AT_EXITS(Instr, SHIFT, EXIT, EXIT, EXIT)

// The same checks, with the gas test leaving through GAS_EXIT(OutOfGas) and
// the overflow test through OVERFLOW_EXIT(Error).
#define MONAD_VM_CHECK_REQUIREMENTS_AT_EXITS(                                  \
    Instr, SHIFT, EXIT, GAS_EXIT, OVERFLOW_EXIT)                               \
    do {                                                                       \
        static_assert(!compiler::has_operand_dependent_stack_effect(Instr));   \
        static constexpr auto info = compiler::opcode_table<traits>[Instr];    \
                                                                               \
        if constexpr (info.min_gas > 0) {                                      \
            gas_remaining -= info.min_gas;                                     \
                                                                               \
            if constexpr (MONAD_VM_SHOULD_CHECK_GAS(                           \
                              Instr, info.dynamic_gas)) {                      \
                if (MONAD_UNLIKELY(gas_remaining < 0)) {                       \
                    GAS_EXIT(OutOfGas);                                        \
                }                                                              \
            }                                                                  \
        }                                                                      \
                                                                               \
        if constexpr (info.min_stack == 0 && info.stack_increase == 0) {       \
            break;                                                             \
        }                                                                      \
                                                                               \
        /* Compare against pointer bounds: addition costs less than            \
         * subtracting pointers on ZisK. */                                    \
        uint256_t const *const stack_at = stack_top.next_slot() + (SHIFT);     \
        MONAD_DEBUG_ASSERT(                                                    \
            stack_at -                                                         \
                (stack_lower_bound - MONAD_VM_STACK_LOWER_BOUND_BIAS) <=       \
            1024);                                                             \
                                                                               \
        if (MONAD_UNLIKELY(                                                    \
                !::monad::vm::interpreter::stack_holds<info.min_stack>(        \
                    stack_top + (SHIFT), stack_lower_bound))) {                \
            EXIT(Error);                                                       \
        }                                                                      \
                                                                               \
        if constexpr (info.stack_increase > 0) {                               \
            static constexpr auto delta =                                      \
                info.stack_increase - info.min_stack;                          \
            /* Reuse the cached limit to avoid rebuilding it or subtracting    \
             * pointers. For growing opcodes, delta == 1, so the adjustment    \
             * limit - 1024 is zero. */                                        \
            static constexpr auto limit = 1025 - delta;                        \
                                                                               \
            /* We only need to emit the overflow check if this instruction     \
             * could actually cause an overflow; if the instruction could only \
             * leave the stack with >1024 elements if it _began_ with >1024,   \
             * then we assume that the input stack was valid and elide the     \
             * check. */                                                       \
            if constexpr (limit <= 1024) {                                     \
                if (MONAD_UNLIKELY(                                            \
                        stack_at >= MONAD_VM_STACK_LIMIT + (limit - 1024))) {  \
                    OVERFLOW_EXIT(Error);                                      \
                }                                                              \
            }                                                                  \
        }                                                                      \
    }                                                                          \
    while (false)

namespace monad::vm::interpreter
{
    using enum runtime::StatusCode;

#if defined(MONAD_ZKVM_ZISK)
    // Keep gas checks before observable effects and jumps. Other opcodes
    // still charge gas, but may defer exhaustion to the next checkpoint.
    // Host reads also need a checkpoint: even a discarded read may require
    // a witness entry. STOP, RETURN and REVERT check before ending the frame.
    consteval bool
    should_check_gas(uint8_t const op, bool const dynamic_gas) noexcept
    {
        using enum compiler::EvmOpCode;
        // Existing memory is frame-local; growth checks gas before resizing.
        if (op == MLOAD || op == MSTORE || op == MSTORE8) {
            return false;
        }
        return dynamic_gas || op == JUMP || op == JUMPI || op == GAS ||
               op == TSTORE || op == SELFDESTRUCT || op == BLOCKHASH ||
               op == SELFBALANCE || op == TLOAD;
    }
#endif

#if defined(MONAD_ZKVM_ZISK)
    // Separate entry points for the same errors; keep them out of line.
    [[noreturn, gnu::noinline, gnu::cold]] inline void
    exit_out_of_gas(runtime::Context &ctx) noexcept
    {
        ctx.exit(OutOfGas);
    }

    [[noreturn, gnu::noinline, gnu::cold]] inline void
    exit_stack_overflow(runtime::Context &ctx) noexcept
    {
        ctx.exit(Error);
    }
#endif

    // Shared operand-count check for individual opcodes and fused sequences.
    template <int32_t Required>
    [[gnu::always_inline]] inline bool
    stack_holds(StackTop const top, uint256_t const *const stack_lower_bound)
    {
        auto const *const stack_top = top.next_slot();
        if constexpr (Required == 0) {
            return true;
        }
        else if constexpr (Required == MONAD_VM_STACK_LOWER_BOUND_BIAS) {
            return stack_top >= stack_lower_bound;
        }
        else if constexpr (Required == MONAD_VM_STACK_LOWER_BOUND_BIAS + 1) {
            return stack_top > stack_lower_bound;
        }
        else {
            return stack_top >=
                   stack_lower_bound +
                       (Required - MONAD_VM_STACK_LOWER_BOUND_BIAS);
        }
    }

    template <uint8_t Instr, Traits traits, typename Analysis>
    [[gnu::always_inline]] inline void check_requirements(
        runtime::Context &ctx, Analysis const &,
        uint256_t const *const stack_lower_bound, StackTop const stack_top,
        int64_t &gas_remaining)
    {
#if defined(MONAD_ZKVM_ZISK)
        // The handlers hold the limit in their second argument; this caller
        // has the analysis there.
        [[maybe_unused]] uint256_t const *const stack_limit = ctx.stack_limit;
#endif
        MONAD_VM_CHECK_REQUIREMENTS(Instr, ctx.exit);
    }

    struct Eip8024Operands
    {
        ptrdiff_t n;
        ptrdiff_t m; // meaningful only for EXCHANGE
    };

    template <uint8_t Instr, Traits traits>
    [[gnu::always_inline]] inline Eip8024Operands check_requirements_eip8024(
        runtime::Context &ctx, uint256_t const *const stack_lower_bound,
        StackTop const stack_top, int64_t &gas_remaining, uint8_t const imm)
    {
        static constexpr auto info = compiler::opcode_table<traits>[Instr];

        // Checked before gas, so it fails as INVALID (matches compiler).
        if (MONAD_UNLIKELY(!compiler::eip8024_immediate_valid(Instr, imm))) {
            ctx.exit(Error);
        }

        gas_remaining -= info.min_gas;
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            ctx.exit(OutOfGas);
        }

        auto const operands = compiler::eip8024_operands(Instr, imm);
        ptrdiff_t const min_stack =
            compiler::eip8024_stack_effect(Instr, operands).min_stack;

        auto const stack_size =
            stack_top.next_slot() -
            (stack_lower_bound - MONAD_VM_STACK_LOWER_BOUND_BIAS);
        MONAD_DEBUG_ASSERT(stack_size <= 1024);
        if (MONAD_UNLIKELY(stack_size < min_stack)) {
            ctx.exit(Error);
        }

        static constexpr auto delta = info.stack_increase - info.min_stack;
        if constexpr (delta > 0) {
            static constexpr auto max_safe_size = 1024 - delta;
            if (MONAD_UNLIKELY(stack_size > max_safe_size)) {
                ctx.exit(Error);
            }
        }

        return {operands.first, operands.second};
    }

    [[gnu::always_inline]] inline void
    push(StackTop const stack_top, uint256_t const &x)
    {
        *stack_top.next_slot() = x;
    }

    [[gnu::always_inline]] inline uint256_t &pop(StackTop &stack_top)
    {
        return *stack_top--;
    }

    [[gnu::always_inline]] inline auto pop_for_overwrite(StackTop &stack_top)
    {
        auto const &a = pop(stack_top);
        return std::tie(a, *stack_top);
    }

    [[gnu::always_inline]] inline auto top_two(StackTop const stack_top)
    {
        auto const &a = *stack_top;
        return std::tie(a, stack_top[-1]);
    }
}

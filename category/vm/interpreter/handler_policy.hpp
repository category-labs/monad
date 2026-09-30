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

// Host settings of the interpreter handlers. Guest builds override them through
// their shadow header.

/**
 * This attribute changes the calling convention of the tail-called instruction
 * dispatch functions so that their pinned arguments are passed in different
 * registers to the usual SysV ABI. Doing so means that we perform far less
 * shuffling of arguments when making calls into the runtime: the non-tail
 * runtime function calls get to use the regular SysV registers, and must
 * preserve the registers used for argument threading.
 *
 * See https://blog.reverberate.org/2025/02/10/tail-call-updates.html for a good
 * reference to this technique.
 *
 * Restricted to Clang: gcc-15 does not support preserve_none, and g++-16 (which
 * does) miscompiles it together with the musttail dispatch below at -Og,
 * corrupting gas accounting (wrong gas_used / state root in ethereum_test). It
 * is only a marginal register-allocation optimisation, so gating it to Clang
 * costs nothing on GCC.
 */
#if defined(__has_attribute) && defined(__clang__)
    #if __has_attribute(preserve_none)
        #define MONAD_VM_INSTRUCTION_CALL __attribute__((preserve_none))
    #else
        #define MONAD_VM_INSTRUCTION_CALL
    #endif
#else
    #define MONAD_VM_INSTRUCTION_CALL
#endif

/**
 * The combination of `preserve_none` and Clang's address sanitizer breaks
 * things, so we disable the calling convention in that scenario. The attribute
 * is only a marginal optimisation that changes register allocation slightly,
 * and so it's OK to disable in this specific scenario.
 *
 * See: https://github.com/llvm/llvm-project/issues/95928
 */
#if defined(__clang__)
    #if defined(__has_feature)
        #if __has_feature(address_sanitizer)
            #undef MONAD_VM_INSTRUCTION_CALL
            #define MONAD_VM_INSTRUCTION_CALL
        #endif
    #endif
#endif

// Handlers, the twins they tail-call and handler pointers share
// MONAD_VM_INSTRUCTION_CALL.
#define MONAD_VM_INLINE_INSTRUCTION_CALL MONAD_VM_INSTRUCTION_CALL inline
#define MONAD_VM_TWIN_CALL MONAD_VM_INSTRUCTION_CALL
#define MONAD_VM_POINTER_CALL MONAD_VM_INSTRUCTION_CALL

// stack_lower_bound points at the stack's first element.
#define MONAD_VM_STACK_LOWER_BOUND_BIAS 0

// Handlers receive the code analysis and load the stack limit from ctx.
#define MONAD_VM_DISPATCH_STATE_TYPE Intercode const &
#define MONAD_VM_DISPATCH_STATE_PARAM Intercode const &analysis
#define MONAD_VM_DISPATCH_STATE_ARG analysis
#define MONAD_VM_CODE_VIEW analysis
#define MONAD_VM_STACK_LIMIT ctx.stack_limit

// All dispatching handlers must use MONAD_VM_TBL_PARAM and MONAD_VM_TBL_ARG,
// which pass no table base here: handlers read the table directly.
#define MONAD_VM_TBL_TYPE
#define MONAD_VM_TBL_PARAM
#define MONAD_VM_TBL_ARG
#define MONAD_VM_TABLE_REF instruction_table<traits>

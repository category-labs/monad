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

#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <array>
#include <cstdint>

/**
 * This attribute changes the calling convention of the tail-called instruction
 * dispatch functions so that their pinned arguments are passed in different
 * registers to the usual SysV ABI. Doing so means that we perform far less
 * shuffling of arguments when making calls into the runtime: the non-tail
 * runtime function calls get to use the regular SysV registers, and must
 * preserve the registers used for argument threading.
 *
 * See https://blog.reverberate.org/2025/02/10/tail-call-updates.html for a good
 * reference to this technique. It is not supported by GCC as of version 15.
 */
#if defined(__has_attribute)
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

namespace monad::vm::interpreter
{
    using InstrEval = void MONAD_VM_INSTRUCTION_CALL (*)(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    using InstrEvalInline = void (*)(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    using InstrTable = std::array<InstrEval, 256>;
}

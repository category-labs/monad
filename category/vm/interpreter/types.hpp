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
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>

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

/*
 * The seventh argument is behind a flag, and it has to be one: without it the baseline this lever is
 * measured against cannot be rebuilt from the same tree, and the A/B is reproducible only against
 * the parent commit. Flag off is the pre-lever guest, byte for byte -- checked, not assumed.
 *
 * Measured on the canonical 200: steps -2.771 % median, COST -1.186 % median, every block improving,
 * 200 of 200 post-state roots. GCC otherwise re-materialises the table base at every dispatch as
 * `auipc` plus an `ld`, 3,129,627 steps a block doing no EVM work. RISC-V passes eight arguments in
 * registers, so the seventh is free at the call.
 */
#if defined(MONAD_VM_TABLE_ARG)
    #define MONAD_VM_TBL_TYPE , void const *
    #define MONAD_VM_TBL_PARAM , void const *itbl
    #define MONAD_VM_TBL_ARG , itbl
    #define MONAD_VM_TABLE_REF (static_cast<InstrEval const *>(itbl))
#else
    #define MONAD_VM_TBL_TYPE
    #define MONAD_VM_TBL_PARAM
    #define MONAD_VM_TBL_ARG
    #define MONAD_VM_TABLE_REF instruction_table<traits>
#endif

namespace monad::vm::interpreter
{
    // The seventh argument is the instruction table's own base, carried through
    // the tail-call chain in a register instead of being re-materialised at
    // every dispatch. Typed `void const *` because the table's type is written
    // in terms of this one; the dispatch sites cast it back.
    //
    // Costed before it was written: JUMPDEST is the floor handler -- gas, then
    // dispatch, nothing else -- and two of its ten instructions are the
    // `auipc`/`ld` pair that loads the table pointer out of the GOT.
    using InstrEval = void MONAD_VM_INSTRUCTION_CALL (*)(
        runtime::Context &, Intercode const &, uint256_t const *, uint256_t *,
        int64_t, uint8_t const * MONAD_VM_TBL_TYPE);

    using InstrTable = std::array<InstrEval, 256>;
}

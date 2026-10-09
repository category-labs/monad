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

#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

namespace monad::vm::interpreter
{
    template <Traits traits>
    void execute(runtime::Context &, Intercode const &, uint8_t *stack_ptr);

#if defined(MONAD_ZKVM_ZISK)
    // What execute sets in the context before the first handler: for a code
    // compiled ahead of time (aot/), which may give its frame to the
    // interpreter at a block's offset.
    inline void prepare(
        runtime::Context &ctx, Intercode const &analysis, uint8_t *stack_ptr)
    {
        ctx.stack_limit = reinterpret_cast<uint256_t *>(stack_ptr) + 1023;
        ctx.add256_params.cin = 0;
        ctx.sub256_params.cin = 1;
        ctx.landing_base = analysis.code() + 1;
        ctx.code_bound = analysis.size();
        ctx.jumpdest_words = analysis.jumpdest_words();
    }

    // The interpreter from the code's offset pc, with the stack whose empty
    // top is bottom, its top and the gas a compiled block left.
    template <Traits traits>
    void resume(
        runtime::Context &, uint256_t const *bottom, uint256_t *stack_top,
        int64_t gas_remaining, size_t pc);
#endif
}

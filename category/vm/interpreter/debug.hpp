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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>

#include <format>
#include <iostream>

namespace monad::vm::interpreter
{
#ifdef MONAD_VM_INTERPRETER_DEBUG
    constexpr auto debug_enabled = true;
#else
    constexpr auto debug_enabled = false;
#endif

    /**
     * Debug trace printing compatible with the JSON format emitted by evmone.
     */
    [[gnu::always_inline]]
    inline void trace(
        Intercode const &analysis, std::int64_t gas_remaining,
        std::uint8_t const *instr_ptr)
    {
        std::cerr << std::format(
            "offset: 0x{:02x}  opcode: 0x{:x}  gas_left: {}\n",
            instr_ptr - analysis.code(),
            *instr_ptr,
            gas_remaining);
    }
}

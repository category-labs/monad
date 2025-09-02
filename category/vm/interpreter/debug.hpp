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
    template <Traits traits>
    void trace(
        std::uint8_t const instr, runtime::Context const &ctx,
        Intercode const &analysis, runtime::uint256_t const *stack_bottom,
        runtime::uint256_t const *stack_top, std::int64_t gas_remaining,
        std::uint8_t const *instr_ptr)
    {
        auto const &info = compiler::opcode_table<traits>[instr];
        auto const stack_size = stack_top - stack_bottom;

        std::cerr << std::format(
            "{{\"pc\":{},\"op\":{},\"gas\":\"0x{:x}\",\"gasCost\":\"0x{"
            ":x}\",\"memSize\":{},\"stack\":[",
            instr_ptr - analysis.code(),
            instr,
            gas_remaining,
            info.dynamic_gas ? 0 : info.min_gas,
            ctx.memory.size);

        auto const *comma = "";
        for (auto i = stack_size - 1; i >= 0; --i) {
            std::cerr << std::format(
                "{}\"0x{}\"", comma, (stack_top - i)->to_string(16));
            comma = ",";
        }

        std::cerr << std::format(
            "],\"depth\":{},\"refund\":{},\"opName\":\"{}\"}}\n",
            ctx.env.depth,
            ctx.gas_refund,
            info.name);
    }
}

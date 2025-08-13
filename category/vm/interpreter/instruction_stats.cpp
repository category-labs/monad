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

#ifdef MONAD_VM_INTERPRETER_STATS

    #include <category/vm/core/assert.h>
    #include <category/vm/evm/opcodes.hpp>
    #include <category/vm/interpreter/instruction_stats.hpp>
    #include <category/vm/utils/scope_exit.hpp>

    #include <evmc/evmc.h>

    #include <array>
    #include <bits/chrono.h>
    #include <chrono>
    #include <cstddef>
    #include <cstdint>
    #include <format>
    #include <iostream>
    #include <optional>

namespace monad::vm::interpreter::stats
{
    namespace
    {
        using namespace std::chrono_literals;

        struct OpcodeData
        {
            std::size_t count = 0;
            std::chrono::high_resolution_clock::time_point last_start;
            std::chrono::nanoseconds cumulative_time = 0ns;
        };

        std::optional<std::uint8_t> current_op = std::nullopt;
        std::array<OpcodeData, 256> data_table = {};

        void print_stats()
        {
            std::cerr << "opcode,name,count,time\n";

            for (auto i = 0u; i < data_table.size(); ++i) {
                auto const &info =
                    compiler::opcode_table<EVMC_LATEST_STABLE_REVISION>[i];
                auto const &stats = data_table[i];

                if (stats.count > 0) {
                    std::cerr << std::format(
                        "{},{},{},{}\n",
                        i,
                        info.name,
                        stats.count,
                        stats.cumulative_time.count());
                }
            }
        }

        auto const print_on_exit = utils::scope_exit(print_stats);
    }

    void begin(std::uint8_t const opcode)
    {
        auto &entry = data_table[opcode];
        current_op = opcode;
        entry.last_start = std::chrono::high_resolution_clock::now();
    }

    void end()
    {
        auto const end = std::chrono::high_resolution_clock::now();

        MONAD_VM_DEBUG_ASSERT(current_op.has_value());
        auto const opcode = *current_op;
        current_op = std::nullopt;

        auto &entry = data_table[opcode];
        entry.cumulative_time += (end - entry.last_start);
        entry.count++;
        entry.last_start = {};
    }
}

#endif

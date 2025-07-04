#ifdef MONAD_VM_INTERPRETER_STATS

    #include <monad/vm/core/assert.h>
    #include <monad/vm/evm/opcodes.hpp>
    #include <monad/vm/interpreter/instruction_stats.hpp>
    #include <monad/vm/utils/scope_exit.hpp>

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

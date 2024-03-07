#pragma once

#include <monad/core/assert.h>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/trait.hpp>

MONAD_EVM_NAMESPACE_BEGIN

template <Revision rev, Opcode op>
    requires(op >= Opcode::PUSH1 && op <= Opcode::PUSH32)
struct Trait<rev, op>
{
    static constexpr size_t N =
        std::to_underlying(op) - std::to_underlying(Opcode::PUSH0);
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = N + 1;
    static constexpr bool exist = rev >= Revision::Frontier;
    static constexpr uint64_t baseline_cost = very_low_cost;

    static void impl(StackPointer sp, ExecutionState const &state)
    {
        constexpr auto nfull_words = N / sizeof(uint64_t);
        constexpr auto npartial_bytes = N % sizeof(uint64_t);

        uint256_t value = 0;

        MONAD_ASSERT(N <= (state.analysis.code.size() - state.mstate.pc + 1));
        auto const *data = &state.analysis.code.at(state.mstate.pc + 1);
        if constexpr (npartial_bytes) {
            if constexpr (npartial_bytes == 1) {
                value[nfull_words] = data[0];
            }
            else if constexpr (npartial_bytes == 2) {
                value[nfull_words] = intx::be::unsafe::load<uint16_t>(data);
            }
            else if constexpr (npartial_bytes == 3) {
                value[nfull_words] =
                    intx::be::unsafe::load<uint32_t>(data) >> 8;
            }
            else if constexpr (npartial_bytes == 4) {
                value[nfull_words] = intx::be::unsafe::load<uint32_t>(data);
            }
            else {
                static_assert(npartial_bytes > 4 && npartial_bytes < 8);
                value[nfull_words] = intx::be::unsafe::load<uint64_t>(data) >>
                                     (8 * (sizeof(uint64_t) - npartial_bytes));
            }
            data += npartial_bytes;
        }

        for (size_t i = 0; i < nfull_words; ++i) {
            value[nfull_words - 1 - i] = intx::be::unsafe::load<uint64_t>(data);
            data += sizeof(uint64_t);
        }

        MONAD_ASSERT(
            (state.mstate.pc + N + 1) ==
            static_cast<size_t>(data - state.analysis.code.data()));
        sp.push(value);
    }
};

MONAD_EVM_NAMESPACE_END

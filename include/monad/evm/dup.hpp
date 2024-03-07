#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/trait.hpp>

#include <utility>

MONAD_EVM_NAMESPACE_BEGIN

template <Revision rev, Opcode op>
    requires(op >= Opcode::DUP1 && op <= Opcode::DUP16)
struct Trait<rev, op>
{
    static constexpr size_t N =
        std::to_underlying(op) - std::to_underlying(Opcode::DUP1) + 1;
    static constexpr size_t stack_height_required = N;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;
    static constexpr uint64_t baseline_cost = very_low_cost;

    static void impl(StackPointer sp)
    {
        sp.push(sp.at(N - 1));
    }
};

MONAD_EVM_NAMESPACE_END

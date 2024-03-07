#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/trait.hpp>

MONAD_EVM_NAMESPACE_BEGIN

template <>
struct Trait<Opcode::STOP>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 0;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static Status impl(StackPointer, ExecutionState const &)
    {
        return Status::Success;
    }

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return zero_cost;
    }
};

template <>
struct Trait<Opcode::ADD>
{
    static constexpr size_t stack_height_required = 2;
    static constexpr int stack_height_change = -1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static Status impl(StackPointer sp, ExecutionState const &)
    {
        auto const &a = sp.pop();
        auto const &b = sp.pop();
        sp.push(a + b);
        return Status::Success;
    }

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return very_low_cost;
    }
};

template <>
struct Trait<Opcode::SUB>
{
    static constexpr size_t stack_height_required = 2;
    static constexpr int stack_height_change = -1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static Status impl(StackPointer sp, ExecutionState const &)
    {
        auto const &a = sp.pop();
        auto const &b = sp.pop();
        sp.push(a - b);
        return Status::Success;
    }

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return very_low_cost;
    }
};

MONAD_EVM_NAMESPACE_END

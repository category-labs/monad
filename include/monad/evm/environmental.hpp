#pragma once

#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/trait.hpp>

MONAD_EVM_NAMESPACE_BEGIN

template <Revision rev>
struct Trait<rev, Opcode::ADDRESS>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;

    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        sp.push(intx::be::load<uint256_t>(state.env.address));
        return Status::Success;
    }

    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <Revision rev>
struct Trait<rev, Opcode::ORIGIN>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;

    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        sp.push(intx::be::load<uint256_t>(state.env.origin));
        return Status::Success;
    }

    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <Revision rev>
struct Trait<rev, Opcode::CALLER>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;

    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        sp.push(intx::be::load<uint256_t>(state.env.sender));
        return Status::Success;
    }

    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <Revision rev>
struct Trait<rev, Opcode::CALLVALUE>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;

    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        sp.push(intx::be::load<uint256_t>(to_bytes(state.env.value)));
        return Status::Success;
    }

    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <Revision rev>
struct Trait<rev, Opcode::CALLDATALOAD>
{
    static constexpr size_t stack_height_required = 1;
    static constexpr int stack_height_change = 0;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;

    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        auto const &i = sp.pop();

        if (i >= state.env.input_data.size()) {
            sp.push(0);
        }
        else {
            MONAD_ASSERT(i <= std::numeric_limits<size_t>::max());
            auto const sv = state.env.input_data.substr(
                static_cast<size_t>(i), sizeof(bytes32_t));
            bytes32_t bytes;
            std::copy_n(sv.data(), sv.size(), bytes.bytes);
            // YP Appendix H: When interpreting 256-bit binary values as
            // integers, the representation is big-endian.
            sp.push(intx::be::load<uint256_t>(bytes));
        }

        return Status::Success;
    }

    static constexpr uint64_t baseline_cost()
    {
        return very_low_cost;
    }
};

template <Revision rev>
struct Trait<rev, Opcode::CALLDATASIZE>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;

    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        sp.push(state.env.input_data.size());
        return Status::Success;
    }

    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <Revision rev>
struct Trait<rev, Opcode::CODESIZE>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;

    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        sp.push(state.env.code.size());
        return Status::Success;
    }

    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <Revision rev>
struct Trait<rev, Opcode::GASPRICE>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;

    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        sp.push(intx::be::load<uint256_t>(to_bytes(state.env.gas_price)));
        return Status::Success;
    }

    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

MONAD_EVM_NAMESPACE_END

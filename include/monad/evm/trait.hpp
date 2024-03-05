#pragma once

#include <monad/evm/arithmetic.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/environmental.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/push.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_memory_storage_flow.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/system.hpp>

#include <utility>

MONAD_EVM_NAMESPACE_BEGIN

template <Opcode op>
struct Trait
{
    static_assert(false, "Trait for opcode unimplemented");
};

template <>
struct Trait<Opcode::STOP>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 0;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = [](auto, auto) { return Status::Success; };

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
    static constexpr auto impl = add;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return very_low_cost;
    }
};

template <>
struct Trait<Opcode::ADDRESS>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = address;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <>
struct Trait<Opcode::ORIGIN>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = origin;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <>
struct Trait<Opcode::CALLER>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = caller;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <>
struct Trait<Opcode::CALLVALUE>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = callvalue;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <>
struct Trait<Opcode::CALLDATALOAD>
{
    static constexpr size_t stack_height_required = 1;
    static constexpr int stack_height_change = 0;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = calldataload;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return very_low_cost;
    }
};

template <>
struct Trait<Opcode::CALLDATASIZE>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = calldatasize;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <>
struct Trait<Opcode::CODESIZE>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = codesize;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <>
struct Trait<Opcode::GASPRICE>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = gasprice;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <Opcode op>
    requires(op >= Opcode::PUSH1 && op <= Opcode::PUSH32)
struct Trait<op>
{
    static constexpr size_t N =
        std::to_underlying(op) - std::to_underlying(Opcode::PUSH0);
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = N + 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = pushn<N>;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return very_low_cost;
    }
};

template <>
struct Trait<Opcode::SSTORE>
{
    static constexpr size_t stack_height_required = 2;
    static constexpr int stack_height_change = -2;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision rev>
    static constexpr auto impl = sstore<rev>;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return zero_cost;
    }
};

template <>
struct Trait<Opcode::RETURN>
{
    static constexpr size_t stack_height_required = 2;
    static constexpr int stack_height_change = -2;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static constexpr auto impl = halt<Status::Success>;

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return zero_cost;
    }
};

template <>
struct Trait<Opcode::CALLCODE>
{
    static constexpr size_t stack_height_required = 7;
    static constexpr int stack_height_change = -6;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision rev>
    static constexpr uint64_t baseline_cost()
    {
        if constexpr (rev < Revision::TangerineWhistle) {
            return 40;
        }
        else if constexpr (rev < Revision::Berlin) {
            return 700;
        }
        else {
            return warm_access_cost<Revision::Berlin>();
        }
    }
};

template <>
struct Trait<Opcode::CALL>
{
    static constexpr size_t stack_height_required = 7;
    static constexpr int stack_height_change = -6;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision rev>
    static constexpr uint64_t baseline_cost()
    {
        if constexpr (rev < Revision::TangerineWhistle) {
            return 40;
        }
        else if constexpr (rev < Revision::Berlin) {
            return 700;
        }
        else {
            return warm_access_cost<Revision::Berlin>();
        }
    }
};

template <>
struct Trait<Opcode::SELFDESTRUCT>
{
    static constexpr size_t stack_height_required = 1;
    static constexpr int stack_height_change = -1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision rev>
    static constexpr auto impl = selfdestruct<rev>;

    template <Revision rev>
    static constexpr uint64_t baseline_cost()
    {
        if constexpr (rev < Revision::TangerineWhistle) {
            return 0;
        }
        else {
            // EIP-150
            return selfdestruct_cost;
        }
    }
};

MONAD_EVM_NAMESPACE_END

#pragma once

#include <monad/core/assert.h>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/trait.hpp>
#include <monad/evm/words.hpp>

#include <ethash/keccak.hpp>

MONAD_EVM_NAMESPACE_BEGIN

template <Revision rev>
struct Trait<rev, Opcode::KECCAK256>
{
    static constexpr size_t stack_height_required = 2;
    static constexpr int stack_height_change = -1;
    static constexpr size_t pc_increment = 1;
    static constexpr bool exist = rev >= Revision::Frontier;
    static constexpr uint64_t baseline_cost = keccak256_cost;

    static Status impl(StackPointer sp, ExecutionState &state)
    {
        auto const &offset = sp.pop();
        auto const &size = sp.pop();

        if (auto const status = state.mstate.memory.grow_if_needed(
                state.mstate.gas_left, offset, size);
            status != Status::Success) {
            return status;
        }

        MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());
        MONAD_ASSERT(size <= std::numeric_limits<size_t>::max());

        // H.1
        auto const cost =
            round_up_bytes_to_words(static_cast<size_t>(size)) * 6;
        if (state.mstate.gas_left < cost) {
            return Status::OutOfGas;
        }
        state.mstate.gas_left -= cost;

        auto const data = state.mstate.memory.substr(
            static_cast<size_t>(offset), static_cast<size_t>(size));
        sp.push(intx::be::load<uint256_t>(
            ethash::keccak256(data.data(), data.size())));
        return Status::Success;
    }
};

MONAD_EVM_NAMESPACE_END

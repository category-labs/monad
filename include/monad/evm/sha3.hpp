#pragma once

#include <monad/core/assert.h>
#include <monad/evm/config.hpp>
#include <monad/evm/machine_state.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/words.hpp>

#include <ethash/keccak.hpp>

MONAD_EVM_NAMESPACE_BEGIN

inline Result<uint64_t>
keccak256(StackPointer sp, MachineState &mstate) noexcept
{
    auto const &offset = sp.pop();
    auto const &size = sp.pop();

    BOOST_OUTCOME_TRY(
        auto cost, mstate.memory.grow_if_needed(mstate.gas_left, offset, size));

    MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());
    MONAD_ASSERT(size <= std::numeric_limits<size_t>::max());

    // H.1
    cost += round_up_bytes_to_words(static_cast<size_t>(size)) * 6;
    if (cost > mstate.gas_left) {
        return Status::OutOfGas;
    }

    auto const data = mstate.memory.substr(
        static_cast<size_t>(offset), static_cast<size_t>(size));
    sp.push(
        intx::be::load<uint256_t>(ethash::keccak256(data.data(), data.size())));
    return cost;
}

MONAD_EVM_NAMESPACE_END

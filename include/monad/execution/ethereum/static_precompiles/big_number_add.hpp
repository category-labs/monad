#pragma once

#include <monad/execution/ethereum/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TState>
    struct BigNumberAdd
    {
        static evmc_result execute(const evmc_message &m) noexcept;
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END
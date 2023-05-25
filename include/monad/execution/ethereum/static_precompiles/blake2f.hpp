#pragma once

#include <monad/execution/ethereum/config.hpp>
#include <monad/core/concepts.hpp>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TState>
    struct Blake2F
    {
        static evmc_result execute(const evmc_message &m) noexcept;
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END
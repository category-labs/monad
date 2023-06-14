#pragma once

#include <monad/execution/ethereum/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct BigNumberMultiply
    {
        static evmc::Result execute(const evmc_message &m) noexcept;
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END
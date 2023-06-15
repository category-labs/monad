#pragma once

#include <monad/execution/ethereum/config.hpp>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct BNAdd
    {
        static evmc::Result execute(const evmc_message &message) noexcept
        {
            (void)message;
            return evmc::Result{evmc_result{}};
        }
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END
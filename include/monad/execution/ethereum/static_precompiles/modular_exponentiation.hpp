#pragma once

#include <monad/core/concepts.hpp>
#include <monad/execution/ethereum/config.hpp>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct ModularExponentiation
    {
        static evmc::Result execute(const evmc_message &m) noexcept;
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END
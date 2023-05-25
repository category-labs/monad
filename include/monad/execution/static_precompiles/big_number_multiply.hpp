#pragma once

#include <monad/execution/config.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TState, concepts::fork_traits<TState> TTraits>
    struct BigNumberMultiply
    {
        static evmc_result execute(const evmc_message &m) noexcept;
    };
}

MONAD_EXECUTION_NAMESPACE_END
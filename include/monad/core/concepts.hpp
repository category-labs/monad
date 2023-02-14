#pragma once

#include <monad/config.hpp>
#include <monad/core/transaction.hpp>

MONAD_NAMESPACE_BEGIN

namespace concepts
{
    // clang-format off
    template <class T>
    concept fork_traits = requires(T, Transaction const &t)
    {
        { T::intrinsic_gas(t) } -> std::convertible_to<uint64_t>;
        { T::block_number } -> std::convertible_to<uint64_t>;
    };
    // clang-format on
}

MONAD_NAMESPACE_END

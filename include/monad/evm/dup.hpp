#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/stack_pointer.hpp>

MONAD_EVM_NAMESPACE_BEGIN

template <size_t N>
inline void dup(StackPointer sp) noexcept
{
    static_assert(N >= 1 && N <= 16);
    sp.push(sp.at(N - 1));
}

MONAD_EVM_NAMESPACE_END

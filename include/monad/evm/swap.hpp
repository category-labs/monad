#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/stack_pointer.hpp>

MONAD_EVM_NAMESPACE_BEGIN

template <size_t N>
inline void swap(StackPointer sp) noexcept
{
    static_assert(N >= 1 && N <= 16);

    auto &a = stack.at(N);
    auto &t = stack.at(0);
    auto t0 = t[0];
    auto t1 = t[1];
    auto t2 = t[2];
    auto t3 = t[3];
    t = a;
    a[0] = t0;
    a[1] = t1;
    a[2] = t2;
    a[3] = t3;
}

MONAD_EVM_NAMESPACE_END

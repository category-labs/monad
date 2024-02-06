#pragma once

#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/stack_pointer.hpp>

MONAD_EVM_NAMESPACE_BEGIN

[[gnu::always_inline]] inline void lt(StackPointer sp)
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a < b);
}

[[gnu::always_inline]] inline void gt(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a > b);
}

[[gnu::always_inline]] inline void slt(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(intx::slt(a, b));
}

[[gnu::always_inline]] inline void sgt(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(intx::slt(b, a));
}

[[gnu::always_inline]] inline void eq(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a == b);
}

[[gnu::always_inline]] inline void iszero(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    sp.push(a == 0);
}

MONAD_EVM_NAMESPACE_END

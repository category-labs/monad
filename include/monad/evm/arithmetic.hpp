#pragma once

#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/stack_pointer.hpp>

MONAD_EVM_NAMESPACE_BEGIN

[[gnu::always_inline]] inline void add(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a + b);
}

[[gnu::always_inline]] inline void mul(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a * b);
}

[[gnu::always_inline]] inline void sub(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a - b);
}

[[gnu::always_inline]] inline void div(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(b != 0 ? a / b : 0);
}

[[gnu::always_inline]] inline void sdiv(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(b != 0 ? intx::sdivrem(a, b).quot : 0);
}

[[gnu::always_inline]] inline void mod(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(b != 0 ? a % b : 0);
}

[[gnu::always_inline]] inline void smod(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(b != 0 ? intx::sdivrem(a, b).rem : 0);
}

[[gnu::always_inline]] inline void addmod(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    auto const &n = sp.pop();
    sp.push(n != 0 ? intx::addmod(a, b, n) : 0);
}

[[gnu::always_inline]] inline void mulmod(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    auto const &n = sp.pop();
    sp.push(n != 0 ? intx::mulmod(a, b, n) : 0);
}

MONAD_EVM_NAMESPACE_END

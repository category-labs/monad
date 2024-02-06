#pragma once

#include <monad/core/intx.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/stack_pointer.hpp>

MONAD_EVM_NAMESPACE_BEGIN

[[gnu::always_inline]] inline void and (StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a & b);
}

[[gnu::always_inline]] inline void or (StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a | b);
}

[[gnu::always_inline]] inline void xor (StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a ^ b);
}

[[gnu::always_inline]] inline void not(StackPointer sp) noexcept
{
    auto const &a = sp.pop();
    sp.push(~a);
}

[[gnu::always_inline]] inline void byte(StackPointer sp) noexcept
{
    auto const &i = sp.pop();
    auto const &x = sp.pop();

    if (i >= 32) {
        sp.push(0);
        return;
    }

    auto const index = 31 - static_cast<unsigned>(i[0] % 32);
    auto const word = x[index / 8];
    auto const byte_index = index % 8;
    sp.push((word >> (byte_index * 8)) & 0xff);
}

[[gnu::always_inline]] inline void shl(StackPointer sp) noexcept
{
    auto const &shift = sp.pop();
    auto const &value = sp.pop();
    sp.push(value << shift);
}

[[gnu::always_inline]] inline void shr(StackPointer sp) noexcept
{
    auto const &shift = sp.pop();
    auto const &value = sp.pop();
    sp.push(value >> shift);
}

[[gnu::always_inline]] inline void sar(StackPointer sp) noexcept
{
    auto const &shift = stack.pop();
    auto const &value = stack.pop();

    bool const is_neg = static_cast<int64_t>(value[3]) < 0;
    auto const sign_mask = is_neg ? ~uint256_t{} : uint256_t{};

    auto const mask_shift = (shift < 256) ? (256 - shift[0]) : 0;
    sp.push((value >> shift) | (sign_mask << mask_shift));
}

MONAD_EVM_NAMESPACE_END

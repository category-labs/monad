#pragma once

#include <monad/core/int.hpp>
#include <monad/core/result.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/machine_state.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>

#include <type_traits>

MONAD_EVM_NAMESPACE_BEGIN

struct ExecutionState;

[[gnu::always_inline]] inline Status
add(StackPointer sp, ExecutionState const &) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a + b);
    return Status::Success;
}

//[[gnu::always_inline]] inline void mul(StackPointer sp) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &b = sp.pop();
//    sp.push(a * b);
//}
//
//[[gnu::always_inline]] inline void sub(StackPointer sp) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &b = sp.pop();
//    sp.push(a - b);
//}
//
//[[gnu::always_inline]] inline void div(StackPointer sp) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &b = sp.pop();
//    sp.push(b != 0 ? a / b : 0);
//}
//
//[[gnu::always_inline]] inline void sdiv(StackPointer sp) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &b = sp.pop();
//    sp.push(b != 0 ? intx::sdivrem(a, b).quot : 0);
//}
//
//[[gnu::always_inline]] inline void mod(StackPointer sp) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &b = sp.pop();
//    sp.push(b != 0 ? a % b : 0);
//}
//
//[[gnu::always_inline]] inline void smod(StackPointer sp) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &b = sp.pop();
//    sp.push(b != 0 ? intx::sdivrem(a, b).rem : 0);
//}
//
//[[gnu::always_inline]] inline void addmod(StackPointer sp) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &b = sp.pop();
//    auto const &n = sp.pop();
//    sp.push(n != 0 ? intx::addmod(a, b, n) : 0);
//}
//
//[[gnu::always_inline]] inline void mulmod(StackPointer sp) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &b = sp.pop();
//    auto const &n = sp.pop();
//    sp.push(n != 0 ? intx::mulmod(a, b, n) : 0);
//}
//
// template <Revision rev>
//[[gnu::always_inline]] Result<uint64_t>
// exp(StackPointer sp, MachineState const &mstate) noexcept
//{
//    auto const &a = sp.pop();
//    auto const &exponent = sp.pop();
//
//    constexpr auto exponent_cost = rev >= Revision::SpuriousDragon ? 50 : 10;
//    auto const additional_cost =
//        intx::count_significant_bytes(exponent) * exponent_cost;
//    if (mstate.gas_left < additional_cost) {
//        return Status::OutOfGas;
//    }
//
//    sp.push(intx::exp(a, exponent));
//
//    return additional_cost;
//}
//
//[[gnu::always_inline]] inline void signextend(StackPointer sp) noexcept
//{
//    auto const &b = sp.pop();
//    auto x = sp.pop();
//
//    // TODO: assert that b can never be greater?
//    if (b >= sizeof(uint256_t)) {
//        return;
//    }
//
//    using Word = uint256_t::word_type;
//    using SWord = std::make_signed_t<Word>;
//    static_assert(sizeof(Word) == 8);
//
//    auto const e = static_cast<Word>(b);
//    auto const sign_word_index = e / sizeof(Word);
//    auto &sign_word = x[sign_word_index];
//
//    auto const sign_byte_index = e % sizeof(Word);
//    auto const sign_byte_offset = sign_byte_index * 8;
//    auto const sign_byte = sign_word >> sign_byte_offset;
//
//    auto const sext_byte =
//        static_cast<Word>(SWord{static_cast<int8_t>(sign_byte)});
//    auto const sext = sext_byte << sign_byte_offset;
//
//    auto const sign_mask = ~Word{0} << sign_byte_offset;
//    auto const value = sign_word & ~sign_mask;
//    sign_word = sext | value;
//
//    auto const sign_ex = static_cast<Word>(static_cast<SWord>(sext_byte) >>
//    8);
//
//    for (size_t i = 3; i > sign_word_index; --i) {
//        x[i] = sign_ex;
//    }
//
//    sp.push(x);
//}

MONAD_EVM_NAMESPACE_END

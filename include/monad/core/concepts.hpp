#pragma once

#include <monad/config.hpp>
#include <monad/core/transaction.hpp>

MONAD_NAMESPACE_BEGIN

namespace concepts
{
    // clang-format off
    template <class T, class TState>
    concept fork_traits = requires(TState &s, Transaction const &t,
                                   address_t const &a, evmc_result &r)
    {
        { T::intrinsic_gas(t) } -> std::convertible_to<uint64_t>;
        { T::starting_nonce() } -> std::convertible_to<uint64_t>;
        { T::block_number } -> std::convertible_to<uint64_t>;
        { T::get_selfdestruct_refund(s) } -> std::convertible_to<uint64_t>;
        { T::max_refund_quotient() } -> std::convertible_to<int>;
        { T::destruct_touched_dead(s) } -> std::convertible_to<void>;
        { T::store_contract_code(s, a, r) } -> std::convertible_to<bool>;
    };
    // clang-format on
}

MONAD_NAMESPACE_END

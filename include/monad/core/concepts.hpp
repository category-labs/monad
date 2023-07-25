#pragma once

#include <monad/config.hpp>
#include <monad/core/transaction.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

namespace concepts
{
    // clang-format off
    template <class T, class TState>
    concept fork_traits = requires(TState &s, Transaction const &t,
                                   address_t const &a, byte_string const & code,
                                   int64_t gas, evmc::Result r)
    {
        typename T::next_fork_t;
        typename T::static_precompiles_t;
        { T::rev } -> std::convertible_to<evmc_revision>;
        { T::intrinsic_gas(t) } -> std::convertible_to<uint64_t>;
        { T::starting_nonce() } -> std::convertible_to<uint64_t>;
        { T::last_block_number } -> std::convertible_to<uint64_t>;
        { T::get_selfdestruct_refund(s) } -> std::convertible_to<uint64_t>;
        { T::max_refund_quotient() } -> std::convertible_to<int>;
        { T::destruct_touched_dead(s) } -> std::convertible_to<void>;
        { T::store_contract_code(s, a, code, gas) } -> std::convertible_to<evmc_result>;
        { T::finalize_contract_storage(s, a, std::move(r)) }
            -> std::convertible_to<evmc::Result>;
    };
    // clang-format on
}

MONAD_NAMESPACE_END

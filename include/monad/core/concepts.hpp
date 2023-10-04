#pragma once

#include <monad/config.hpp>

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>

#include <evmc/evmc.hpp>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace concepts
{
    // clang-format off
    template <class T, class TState>
    concept fork_traits = requires(TState &s, Transaction const &t,
                                   address_t const &a, byte_string const & code,
                                   uint64_t gas_used, evmc::Result r, uint256_t const& base_fee_per_gas, 
                                   Block const& b, block_num_t const block_number, 
                                   std::optional<std::vector<Withdrawal>> const& w, evmc_tx_context& context)
    {
        typename T::next_fork_t;
        { T::rev } -> std::convertible_to<evmc_revision>;
        { T::intrinsic_gas(t) } -> std::convertible_to<uint64_t>;
        { T::starting_nonce() } -> std::convertible_to<uint64_t>;
        { T::last_block_number } -> std::convertible_to<uint64_t>;
        { T::n_precompiles } -> std::convertible_to<uint64_t>;
        { T::max_refund_quotient() } -> std::convertible_to<int>;
        { T::destruct_touched_dead(s) } -> std::convertible_to<void>;
        { T::deploy_contract_code(s, a, std::move(r)) }
            -> std::convertible_to<evmc::Result>;
        { T::calculate_txn_award(t, base_fee_per_gas, gas_used) } -> std::convertible_to<uint256_t>;
        { T::gas_price(t, base_fee_per_gas) } -> std::convertible_to<uint256_t>;
        { T::warm_coinbase(s, a) } -> std::convertible_to<void>;
        { T::access_list_valid(t.access_list) } -> std::convertible_to<bool>;
        { T::account_exists(s, a) } -> std::convertible_to<bool>;

        // TODO: These 3 functions would require more template params for the TTraits concept
        //       Comment back once decided what the new concept should be like
        // { T::transfer_balance_dao(s, block_number) } -> std::convertible_to<void>;
        // { T::process_withdrawal(s, w) } -> std::convertible_to<void>;
        // { T::apply_block_award(s, b) } -> std::convertible_to<void>;

        { T::populate_chain_id(context) } -> std::convertible_to<void>;
    };
    // clang-format on
}

MONAD_NAMESPACE_END

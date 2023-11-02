#pragma once

#include <monad/config.hpp>

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/evmc_host.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validation.hpp>

#include <monad/rlp/encode_helpers.hpp>

#include <monad/state2/state.hpp>

#include <intx/intx.hpp>

#include <algorithm>

MONAD_NAMESPACE_BEGIN

template <class Traits>
struct TransactionProcessor
{
    // YP Sec 6.2 "irrevocable_change"
    void irrevocable_change(
        State &state, Transaction const &txn,
        uint256_t const &base_fee_per_gas) const
    {
        if (txn.to) { // EVM will increment if new contract
            auto const nonce = state.get_nonce(*txn.from);
            state.set_nonce(*txn.from, nonce + 1);
        }
        MONAD_DEBUG_ASSERT(txn.from.has_value());

        auto const upfront_cost =
            txn.gas_limit * gas_price<Traits>(txn, base_fee_per_gas);
        state.subtract_from_balance(txn.from.value(), upfront_cost);
    }

    // YP Eqn 72
    [[nodiscard]] uint64_t g_star(
        Transaction const &txn, uint64_t const gas_remaining,
        uint64_t const refund) const
    {
        // https://eips.ethereum.org/EIPS/eip-3529
        constexpr auto max_refund_quotient = Traits::rev >= EVMC_LONDON ? 5 : 2;
        auto const refund_allowance =
            (txn.gas_limit - gas_remaining) / max_refund_quotient;

        return gas_remaining + std::min(refund_allowance, refund);
    }

    [[nodiscard]] auto refund_gas(
        State &state, Transaction const &txn, uint256_t const &base_fee_per_gas,
        uint64_t const gas_leftover, uint64_t const refund) const
    {
        // refund and priority, Eqn. 73-76
        auto const gas_remaining = g_star(txn, gas_leftover, refund);
        auto const gas_cost = gas_price<Traits>(txn, base_fee_per_gas);

        MONAD_DEBUG_ASSERT(txn.from.has_value());
        state.add_to_balance(txn.from.value(), gas_cost * gas_remaining);

        return gas_remaining;
    }

    Receipt execute(
        State &state, EvmcHost<Traits> &host, Transaction const &txn,
        uint256_t const &base_fee_per_gas, address_t const &beneficiary) const
    {
        irrevocable_change(state, txn, base_fee_per_gas);

        // EIP-3651
        if constexpr (Traits::rev >= EVMC_SHANGHAI) {
            state.warm_coinbase(beneficiary);
        }

        state.access_account(*txn.from);
        for (auto const &ae : txn.access_list) {
            state.access_account(ae.a);
            for (auto const &keys : ae.keys) {
                state.access_storage(ae.a, keys);
            }
        }
        if (txn.to) {
            state.access_account(*txn.to);
        }

        auto m = EvmcHost<Traits>::make_msg_from_txn(txn);
        auto result = host.call(m);

        MONAD_DEBUG_ASSERT(result.gas_left >= 0);
        MONAD_DEBUG_ASSERT(result.gas_refund >= 0);
        MONAD_DEBUG_ASSERT(
            txn.gas_limit >= static_cast<uint64_t>(result.gas_left));
        auto const gas_remaining = refund_gas(
            state,
            txn,
            base_fee_per_gas,
            static_cast<uint64_t>(result.gas_left),
            static_cast<uint64_t>(result.gas_refund));
        auto const gas_used = txn.gas_limit - gas_remaining;
        auto const reward =
            calculate_txn_award<Traits>(txn, base_fee_per_gas, gas_used);
        state.add_to_balance(beneficiary, reward);

        // finalize state, Eqn. 77-79
        state.destruct_suicides();
        if constexpr (Traits::rev >= EVMC_SPURIOUS_DRAGON) {
            state.destruct_touched_dead();
        }

        Receipt receipt{
            .status = result.status_code == EVMC_SUCCESS ? 1u : 0u,
            .gas_used = gas_used,
            .type = txn.type};
        for (auto &log : state.logs()) {
            receipt.add_log(std::move(log));
        }

        return receipt;
    }
};

MONAD_NAMESPACE_END

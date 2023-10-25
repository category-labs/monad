#pragma once

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

#include <monad/rlp/encode_helpers.hpp>

#include <intx/intx.hpp>

#include <algorithm>

MONAD_EXECUTION_NAMESPACE_BEGIN

enum class TransactionStatus
{
    SUCCESS,
    INSUFFICIENT_BALANCE,
    INTRINSIC_GAS_GREATER_THAN_LIMIT,
    BAD_NONCE,
    SENDER_NOT_EOA,
    TYPE_NOT_SUPPORTED,
    MAX_FEE_LESS_THAN_BASE,
    PRIORITY_FEE_GREATER_THAN_MAX,
    NONCE_EXCEEDS_MAX,
    INIT_CODE_LIMIT_EXCEEDED,
    GAS_LIMIT_REACHED,
    WRONG_CHAIN_ID,
    MISSING_SENDER,
};

template <class TState, class TTraits>
struct TransactionProcessor
{
    // YP Sec 6.2 "irrevocable_change"
    void irrevocable_change(
        TState &s, Transaction const &t,
        uint256_t const &base_fee_per_gas) const
    {
        if (t.to) { // EVM will increment if new contract
            auto const nonce = s.get_nonce(*t.from);
            s.set_nonce(*t.from, nonce + 1);
        }
        MONAD_DEBUG_ASSERT(t.from.has_value());

        auto const upfront_cost =
            t.gas_limit * TTraits::gas_price(t, base_fee_per_gas);
        s.subtract_from_balance(t.from.value(), upfront_cost);
    }

    // YP Eqn 72
    [[nodiscard]] uint64_t g_star(
        Transaction const &t, uint64_t const gas_remaining,
        uint64_t const refund) const
    {
        auto const refund_allowance =
            (t.gas_limit - gas_remaining) / TTraits::max_refund_quotient();

        return gas_remaining + std::min(refund_allowance, refund);
    }

    [[nodiscard]] auto refund_gas(
        TState &s, Transaction const &t, uint256_t const &base_fee_per_gas,
        uint64_t const gas_leftover, uint64_t const refund) const
    {
        // refund and priority, Eqn. 73-76
        auto const gas_remaining = g_star(t, gas_leftover, refund);
        auto const gas_cost = TTraits::gas_price(t, base_fee_per_gas);

        MONAD_DEBUG_ASSERT(t.from.has_value());
        s.add_to_balance(t.from.value(), gas_cost * gas_remaining);

        return gas_remaining;
    }

    template <class TEvmHost>
    Receipt execute(
        TState &s, TEvmHost &h, Transaction const &t,
        uint256_t const &base_fee_per_gas, address_t const &beneficiary) const
    {
        irrevocable_change(s, t, base_fee_per_gas);

        TTraits::warm_coinbase(s, beneficiary);
        s.access_account(*t.from);
        for (auto const &ae : t.access_list) {
            s.access_account(ae.a);
            for (auto const &keys : ae.keys) {
                s.access_storage(ae.a, keys);
            }
        }
        if (t.to) {
            s.access_account(*t.to);
        }

        auto m = TEvmHost::make_msg_from_txn(t);
        auto result = h.call(m);

        MONAD_DEBUG_ASSERT(result.gas_left >= 0);
        MONAD_DEBUG_ASSERT(result.gas_refund >= 0);
        MONAD_DEBUG_ASSERT(
            t.gas_limit >= static_cast<uint64_t>(result.gas_left));

        auto const gas_remaining = refund_gas(
            s,
            t,
            base_fee_per_gas,
            static_cast<uint64_t>(result.gas_left),
            static_cast<uint64_t>(result.gas_refund));
        auto const gas_used = t.gas_limit - gas_remaining;
        auto const reward =
            TTraits::calculate_txn_award(t, base_fee_per_gas, gas_used);
        s.add_to_balance(beneficiary, reward);

        // finalize state, Eqn. 77-79
        s.destruct_suicides();
        TTraits::destruct_touched_dead(s);

        return Receipt{
            .status = result.status_code == EVMC_SUCCESS ? 1u : 0u,
            .gas_used = gas_used,
            .type = t.type,
            .logs = std::move(s.logs())};
    }

    TransactionStatus validate(TState &state, Transaction const &t)
    {
        // This is only verfiable after recover_sender, so it belongs to
        // validate
        if (MONAD_UNLIKELY(!t.from.has_value())) {
            return TransactionStatus::MISSING_SENDER;
        }

        // σ[S(T)]c = KEC(()), EIP-3607
        if (MONAD_UNLIKELY(state.get_code_hash(*t.from) != NULL_HASH)) {
            return TransactionStatus::SENDER_NOT_EOA;
        }

        // Tn = σ[S(T)]n
        if (MONAD_UNLIKELY(state.get_nonce(t.from.value()) != t.nonce)) {
            return TransactionStatus::BAD_NONCE;
        }

        // v0 <= σ[S(T)]b
        else if (MONAD_UNLIKELY(
                     intx::be::load<uint256_t>(state.get_balance(*t.from)) <
                     (t.value +
                      intx::umul(uint256_t(t.gas_limit), t.max_fee_per_gas)))) {
            return TransactionStatus::INSUFFICIENT_BALANCE;
        }
        // Note: Tg <= B_Hl - l(B_R)u can only be checked before retirement

        return TransactionStatus::SUCCESS;
    }

    TransactionStatus static_validate(
        Transaction const &t, std::optional<uint256_t> const &base_fee_per_gas)
    {
        if (MONAD_UNLIKELY(!TTraits::chain_id_valid(t))) {
            return TransactionStatus::WRONG_CHAIN_ID;
        }

        if (MONAD_UNLIKELY(!TTraits::transaction_type_valid(t.type))) {
            return TransactionStatus::TYPE_NOT_SUPPORTED;
        }

        if (MONAD_UNLIKELY(
                base_fee_per_gas.has_value() &&
                t.max_fee_per_gas < base_fee_per_gas.value())) {
            return TransactionStatus::MAX_FEE_LESS_THAN_BASE;
        }

        if (MONAD_UNLIKELY(t.max_priority_fee_per_gas > t.max_fee_per_gas)) {
            return TransactionStatus::PRIORITY_FEE_GREATER_THAN_MAX;
        }

        if (MONAD_UNLIKELY(!TTraits::init_code_valid(t))) {
            return TransactionStatus::INIT_CODE_LIMIT_EXCEEDED;
        }

        // Yellow paper, Eq. 62
        // g0 <= Tg
        if (MONAD_UNLIKELY(TTraits::intrinsic_gas(t) > t.gas_limit)) {
            return TransactionStatus::INTRINSIC_GAS_GREATER_THAN_LIMIT;
        }

        // eip-2681
        if (MONAD_UNLIKELY(t.nonce >= std::numeric_limits<uint64_t>::max())) {
            return TransactionStatus::NONCE_EXCEEDS_MAX;
        }

        return TransactionStatus::SUCCESS;
    }
};

MONAD_EXECUTION_NAMESPACE_END

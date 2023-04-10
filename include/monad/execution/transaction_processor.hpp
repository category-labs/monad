#pragma once

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

#include <intx/intx.hpp>

#include <algorithm>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TState, concepts::fork_traits<TState> TTraits>
struct TransactionProcessor
{
    uint128_t upfront_cost_{};

    enum class Status
    {
        SUCCESS,
        LATER_NONCE,
        INSUFFICIENT_BALANCE,
        INVALID_GAS_LIMIT,
        BAD_NONCE,
        DEPLOYED_CODE,
    };

    // YP Sec 6.2 "irrevocable_change"
    void irrevocable_change(TState &s, Transaction const &t) const
    {
        if (t.to) { // EVM will increment if new contract
            auto const nonce = s.get_nonce(*t.from);
            s.set_nonce(*t.from, nonce + 1);
        }
        auto const balance = intx::be::load<uint256_t>(s.get_balance(*t.from));
        s.set_balance(*t.from, balance - upfront_cost_);
    }

    // YP Eqn 72
    uint64_t
    g_star(TState &s, Transaction const &t, uint64_t gas_remaining) const
    {
        auto refund = s.get_refund();
        refund += TTraits::get_selfdestruct_refund(s);

        const auto refund_allowance =
            (t.gas_limit - gas_remaining) / TTraits::max_refund_quotient();

        return gas_remaining + std::min(refund_allowance, refund);
    }

    [[nodiscard]] auto award_fee_and_refund(
        TState &s, BlockHeader const &b, Transaction const &t,
        uint64_t const gas_leftover) const
    {
        // refund and priority, Eqn. 73-76
        auto const gas_remaining = g_star(s, t, gas_leftover);
        auto const per_gas_cost =
            t.per_gas_cost(b.base_fee_per_gas.value_or(0));
        auto const bene_balance =
            intx::be::load<uint256_t>(s.get_balance(b.beneficiary));

        s.set_balance(
            b.beneficiary,
            bene_balance + (per_gas_cost * (t.gas_limit - gas_remaining)));
        const auto sender_balance =
            intx::be::load<uint256_t>(s.get_balance(*t.from));

        s.set_balance(*t.from, sender_balance + (per_gas_cost * gas_remaining));
        return gas_remaining;
    }

    template <class TEvmHost>
    Receipt execute(
        TState &s, TEvmHost &h, BlockHeader const &b,
        Transaction const &t) const
    {
        irrevocable_change(s, t);

        s.access_account(*t.from);
        for (const auto &ae : t.access_list) {
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

		MONAD_ASSERT(result.gas_left >= 0);
        auto const gas_remaining = award_fee_and_refund(
            s, b, t, static_cast<uint64_t>(result.gas_left));

        // finalize state, Eqn. 77-79
        s.destruct_suicides();
        TTraits::destruct_touched_dead(s);

        auto receipt = h.make_receipt_from_result(result, t, gas_remaining);
        return receipt;
    }

    Status validate(
        TState const &state, Transaction const &t, uint64_t base_fee_per_gas)
    {
        upfront_cost_ =
            intx::umul(t.gas_limit, t.per_gas_cost(base_fee_per_gas));

        // Yellow paper, Eq. 62
        // g0 <= Tg
        if (TTraits::intrinsic_gas(t) > t.gas_limit) {
            return Status::INVALID_GAS_LIMIT;
        }

        // σ[S(T)]c = KEC(()), EIP-3607
        if (state.get_code_hash(*t.from) != NULL_HASH) {
            return Status::DEPLOYED_CODE;
        }
        // Tn = σ[S(T)]n
        else if (state.get_nonce(*t.from) > t.nonce) {
            return Status::BAD_NONCE;
        }
        // Tn = σ[S(T)]n
        else if (state.get_nonce(*t.from) < t.nonce) {
            return Status::LATER_NONCE;
        }

        // v0 <= σ[S(T)]b
        else if (uint256_t i =
                     intx::be::load<uint256_t>(state.get_balance(*t.from));
                 i < (t.amount + upfront_cost_)) {
            return Status::INSUFFICIENT_BALANCE;
        }
        // Note: Tg <= B_Hl - l(B_R)u can only be checked before retirement

        return Status::SUCCESS;
    }

    void static_validate(Transaction const &t)
    {
        // Yellow paper, Eq. 62 S(T) != ∅
        MONAD_ASSERT(t.from.has_value());
    }
};

MONAD_EXECUTION_NAMESPACE_END

#pragma once

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/concepts.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

#include <intx/intx.hpp>

#include <optional>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <concepts::fork_traits TTraits>
struct Processor
{
    std::optional<Account> _from_start{};
    uint64_t _upfront_gas{};

    // Block _block{};
    enum class Status
    {
        SUCCESS,
        INSUFFICIENT_BALANCE,
        INVALID_GAS_LIMIT,
        BAD_NONCE,
        DEPLOYED_CODE,
    };

    template <class TAccount>
    Status validate(TAccount &state, Transaction const &t)
    {
        uint128_t gas = intx::umul(t.gas_limit, t.gas_price);
        MONAD_ASSERT(gas < std::numeric_limits<uint64_t>::max());
        _upfront_gas = static_cast<uint64_t>(gas);

        // Yellow paper, Eq. 62
        // g0 <= Tg
        if (TTraits::intrinsic_gas(t) > t.gas_limit) {
            return Status::INVALID_GAS_LIMIT;
        }

        _from_start = state.fetch(*t.from);
        if (!_from_start) {
            _from_start = state.wait_for_data();
        }

        // σ[S(T)]c = KEC(()), EIP-3607
        if (_from_start->code_hash != NULL_HASH) {
            return Status::DEPLOYED_CODE;
        }
        // Tn = σ[S(T)]n
        else if (_from_start->nonce != t.nonce) {
            return Status::BAD_NONCE;
        }
        // v0 <= σ[S(T)]b
        else if (_from_start->balance < (t.amount + gas)) {
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

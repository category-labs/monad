#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <cstdint>
#include <limits>
#include <optional>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

template <evmc_revision rev>
Result<void> static_validate_transaction(
    Transaction const &txn, std::optional<uint256_t> const &base_fee_per_gas)
{
    // EIP-155
    if (MONAD_LIKELY(txn.sc.chain_id.has_value())) {
        if constexpr (rev < EVMC_SPURIOUS_DRAGON) {
            return TransactionError::TypeNotSupported;
        }
        if (MONAD_UNLIKELY(txn.sc.chain_id.value() != 1)) {
            return TransactionError::WrongChainId;
        }
    }

    // EIP-2930 & EIP-2718
    if constexpr (rev < EVMC_BERLIN) {
        if (MONAD_UNLIKELY(txn.type != TransactionType::eip155)) {
            return TransactionError::TypeNotSupported;
        }
    }
    // EIP-1559
    else if constexpr (rev < EVMC_LONDON) {
        if (MONAD_UNLIKELY(
                txn.type != TransactionType::eip155 &&
                txn.type != TransactionType::eip2930)) {
            return TransactionError::TypeNotSupported;
        }
    }
    else if (MONAD_UNLIKELY(
                 txn.type != TransactionType::eip155 &&
                 txn.type != TransactionType::eip2930 &&
                 txn.type != TransactionType::eip1559)) {
        return TransactionError::TypeNotSupported;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(txn.max_fee_per_gas < base_fee_per_gas.value_or(0))) {
        return TransactionError::MaxFeeLessThanBase;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(txn.max_priority_fee_per_gas > txn.max_fee_per_gas)) {
        return TransactionError::PriorityFeeGreaterThanMax;
    }

    // EIP-3860
    if constexpr (rev >= EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(
                !txn.to.has_value() && txn.data.size() > 2 * 0x6000)) {
            return TransactionError::InitCodeLimitExceeded;
        }
    }

    // YP eq. 62
    if (MONAD_UNLIKELY(intrinsic_gas<rev>(txn) > txn.gas_limit)) {
        return TransactionError::IntrinsicGasGreaterThanLimit;
    }

    // EIP-2681
    if (MONAD_UNLIKELY(txn.nonce >= std::numeric_limits<uint64_t>::max())) {
        return TransactionError::NonceExceedsMax;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(
            max_gas_cost(txn.gas_limit, txn.max_fee_per_gas) >
            std::numeric_limits<uint256_t>::max())) {
        return TransactionError::GasLimitOverflow;
    }

    return success();
}

EXPLICIT_EVMC_REVISION(static_validate_transaction);

Result<void> validate_transaction(State &state, Transaction const &txn)
{
    // This is only verfiable after recover_sender, so it belongs to
    // validate
    // YP eq. 62
    if (MONAD_UNLIKELY(!txn.from.has_value())) {
        return TransactionError::MissingSender;
    }

    // YP eq. 62 & EIP-3607
    if (MONAD_UNLIKELY(state.get_code_hash(*txn.from) != NULL_HASH)) {
        return TransactionError::SenderNotEoa;
    }

    // YP eq. 62
    if (MONAD_UNLIKELY(state.get_nonce(txn.from.value()) != txn.nonce)) {
        return TransactionError::BadNonce;
    }

    // YP eq. 62
    if (MONAD_UNLIKELY(
            intx::be::load<uint256_t>(state.get_balance(*txn.from)) <
            (txn.value + max_gas_cost(txn.gas_limit, txn.max_fee_per_gas)))) {
        return TransactionError::InsufficientBalance;
    }

    // Note: Tg <= B_Hl - l(B_R)u can only be checked before retirement
    // (It requires knowing the parent block)

    return success();
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::TransactionError>::mapping> const &
quick_status_code_from_enum<monad::TransactionError>::value_mappings()
{
    using monad::TransactionError;

    static std::initializer_list<mapping> const v = {
        {TransactionError::Success, "success", {errc::success}},
        {TransactionError::InsufficientBalance, "insufficient balance", {}},
        {TransactionError::IntrinsicGasGreaterThanLimit,
         "intrinsic gas greater than limit",
         {}},
        {TransactionError::BadNonce, "bad nonce", {}},
        {TransactionError::SenderNotEoa, "sender not eoa", {}},
        {TransactionError::TypeNotSupported, "type not supported", {}},
        {TransactionError::MaxFeeLessThanBase, "max fee less than base", {}},
        {TransactionError::PriorityFeeGreaterThanMax,
         "priority fee greater than max",
         {}},
        {TransactionError::NonceExceedsMax, "nonce exceeds max", {}},
        {TransactionError::InitCodeLimitExceeded,
         "init code limit exceeded",
         {}},
        {TransactionError::GasLimitReached, "gas limit reached", {}},
        {TransactionError::WrongChainId, "wrong chain id", {}},
        {TransactionError::MissingSender, "missing sender", {}},
        {TransactionError::GasLimitOverflow, "gas limit overflow", {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

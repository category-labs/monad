#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/execution/validation_status.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <cstdint>
#include <limits>
#include <optional>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
ValidationStatus static_validate_transaction(
    Transaction const &txn, std::optional<uint256_t> const &base_fee_per_gas)
{
    // EIP-155
    if (MONAD_LIKELY(txn.sc.chain_id.has_value())) {
        if constexpr (rev < EVMC_SPURIOUS_DRAGON) {
            return ValidationStatus::TYPE_NOT_SUPPORTED;
        }
        if (MONAD_UNLIKELY(txn.sc.chain_id.value() != 1)) {
            return ValidationStatus::WRONG_CHAIN_ID;
        }
    }

    // EIP-2930 & EIP-2718
    if constexpr (rev < EVMC_BERLIN) {
        if (MONAD_UNLIKELY(txn.type != TransactionType::eip155)) {
            return ValidationStatus::TYPE_NOT_SUPPORTED;
        }
    }
    // EIP-1559
    else if constexpr (rev < EVMC_LONDON) {
        if (MONAD_UNLIKELY(
                txn.type != TransactionType::eip155 &&
                txn.type != TransactionType::eip2930)) {
            return ValidationStatus::TYPE_NOT_SUPPORTED;
        }
    }
    else if (MONAD_UNLIKELY(
                 txn.type != TransactionType::eip155 &&
                 txn.type != TransactionType::eip2930 &&
                 txn.type != TransactionType::eip1559)) {
        return ValidationStatus::TYPE_NOT_SUPPORTED;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(txn.max_fee_per_gas < base_fee_per_gas.value_or(0))) {
        return ValidationStatus::MAX_FEE_LESS_THAN_BASE;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(txn.max_priority_fee_per_gas > txn.max_fee_per_gas)) {
        return ValidationStatus::PRIORITY_FEE_GREATER_THAN_MAX;
    }

    // EIP-3860
    if constexpr (rev >= EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(
                !txn.to.has_value() && txn.data.size() > 2 * 0x6000)) {
            return ValidationStatus::INIT_CODE_LIMIT_EXCEEDED;
        }
    }

    // YP eq. 62
    if (MONAD_UNLIKELY(intrinsic_gas<rev>(txn) > txn.gas_limit)) {
        return ValidationStatus::INTRINSIC_GAS_GREATER_THAN_LIMIT;
    }

    // EIP-2681
    if (MONAD_UNLIKELY(txn.nonce >= std::numeric_limits<uint64_t>::max())) {
        return ValidationStatus::NONCE_EXCEEDS_MAX;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(
            max_gas_cost(txn.gas_limit, txn.max_fee_per_gas) >
            std::numeric_limits<uint256_t>::max())) {
        return ValidationStatus::GAS_LIMIT_OVERFLOW;
    }

    return ValidationStatus::SUCCESS;
}

EXPLICIT_EVMC_REVISION(static_validate_transaction);

ValidationStatus validate_transaction(State &state, Transaction const &txn)
{
    // This is only verfiable after recover_sender, so it belongs to
    // validate
    // YP eq. 62
    if (MONAD_UNLIKELY(!txn.from.has_value())) {
        return ValidationStatus::MISSING_SENDER;
    }

    // YP eq. 62 & EIP-3607
    if (MONAD_UNLIKELY(state.get_code_hash(*txn.from) != NULL_HASH)) {
        return ValidationStatus::SENDER_NOT_EOA;
    }

    // YP eq. 62
    if (MONAD_UNLIKELY(state.get_nonce(txn.from.value()) != txn.nonce)) {
        return ValidationStatus::BAD_NONCE;
    }

    // YP eq. 62
    if (MONAD_UNLIKELY(
            intx::be::load<uint256_t>(state.get_balance(*txn.from)) <
            (txn.value + max_gas_cost(txn.gas_limit, txn.max_fee_per_gas)))) {
        return ValidationStatus::INSUFFICIENT_BALANCE;
    }

    // Note: Tg <= B_Hl - l(B_R)u can only be checked before retirement
    // (It requires knowing the parent block)

    return ValidationStatus::SUCCESS;
}

MONAD_NAMESPACE_END

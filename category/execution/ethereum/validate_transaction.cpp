// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/explicit_evmc_revision.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <boost/outcome/config.hpp>
// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif
#include <boost/outcome/success_failure.hpp>

#include <silkpre/secp256k1n.hpp>

#include <cstdint>
#include <initializer_list>
#include <limits>
#include <optional>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

template <evmc_revision rev>
Result<void> static_validate_transaction(
    Transaction const &tx, std::optional<uint256_t> const &base_fee_per_gas,
    uint256_t const &chain_id, size_t const max_code_size)
{
    // EIP-155
    if (MONAD_LIKELY(tx.sc.chain_id.has_value())) {
        if constexpr (rev < EVMC_SPURIOUS_DRAGON) {
            return TransactionError::TypeNotSupported;
        }
        if (MONAD_UNLIKELY(tx.sc.chain_id.value() != chain_id)) {
            return TransactionError::WrongChainId;
        }
    }

    // EIP-2930 & EIP-2718
    if constexpr (rev < EVMC_BERLIN) {
        if (MONAD_UNLIKELY(tx.type != TransactionType::legacy)) {
            return TransactionError::TypeNotSupported;
        }
    }
    // EIP-1559
    else if constexpr (rev < EVMC_LONDON) {
        if (MONAD_UNLIKELY(
                tx.type != TransactionType::legacy &&
                tx.type != TransactionType::eip2930)) {
            return TransactionError::TypeNotSupported;
        }
    }
    else if (MONAD_UNLIKELY(
                 tx.type != TransactionType::legacy &&
                 tx.type != TransactionType::eip2930 &&
                 tx.type != TransactionType::eip1559)) {
        return TransactionError::TypeNotSupported;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(tx.max_fee_per_gas < base_fee_per_gas.value_or(0))) {
        return TransactionError::MaxFeeLessThanBase;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(tx.max_priority_fee_per_gas > tx.max_fee_per_gas)) {
        return TransactionError::PriorityFeeGreaterThanMax;
    }

    // EIP-3860
    if constexpr (rev >= EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(
                !tx.to.has_value() && tx.data.size() > 2 * max_code_size)) {
            return TransactionError::InitCodeLimitExceeded;
        }
    }

    // YP eq. 62
    if (MONAD_UNLIKELY(intrinsic_gas<rev>(tx) > tx.gas_limit)) {
        return TransactionError::IntrinsicGasGreaterThanLimit;
    }

    // EIP-7623
    if constexpr (rev >= EVMC_PRAGUE) {
        if (MONAD_UNLIKELY(floor_data_gas(tx) > tx.gas_limit)) {
            return TransactionError::IntrinsicGasGreaterThanLimit;
        }
    }

    // EIP-2681
    if (MONAD_UNLIKELY(tx.nonce >= std::numeric_limits<uint64_t>::max())) {
        return TransactionError::NonceExceedsMax;
    }

    // EIP-1559
    if (MONAD_UNLIKELY(
            max_gas_cost(tx.gas_limit, tx.max_fee_per_gas) >
            std::numeric_limits<uint256_t>::max())) {
        return TransactionError::GasLimitOverflow;
    }

    // EIP-2
    if (MONAD_UNLIKELY(!silkpre::is_valid_signature(
            tx.sc.r, tx.sc.s, rev >= EVMC_HOMESTEAD))) {
        return TransactionError::InvalidSignature;
    }

    return success();
}

EXPLICIT_EVMC_REVISION(static_validate_transaction);

Result<void> validate_transaction(
    Transaction const &tx, std::optional<Account> const &sender_account)
{
    // YP (70)
    uint512_t const v0 =
        tx.value + max_gas_cost(tx.gas_limit, tx.max_fee_per_gas);

    if (MONAD_UNLIKELY(!sender_account.has_value())) {
        // YP (71)
        if (tx.nonce) {
            return TransactionError::BadNonce;
        }
        // YP (71)
        if (v0) {
            return TransactionError::InsufficientBalance;
        }
        return success();
    }

    // YP (71)
    if (MONAD_UNLIKELY(sender_account->code_hash != NULL_HASH)) {
        return TransactionError::SenderNotEoa;
    }

    // YP (71)
    if (MONAD_UNLIKELY(sender_account->nonce != tx.nonce)) {
        return TransactionError::BadNonce;
    }

    // YP (71)
    if (MONAD_UNLIKELY(sender_account->balance < v0)) {
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
        {TransactionError::GasLimitOverflow, "gas limit overflow", {}},
        {TransactionError::InvalidSignature, "invalid signature", {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

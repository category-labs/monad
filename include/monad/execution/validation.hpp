#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validation_status.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
constexpr ValidationStatus static_validate_txn(
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

    return ValidationStatus::SUCCESS;
}

constexpr ValidationStatus validate_txn(State &state, Transaction const &txn)
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
            (txn.value +
             intx::umul(uint256_t(txn.gas_limit), txn.max_fee_per_gas)))) {
        return ValidationStatus::INSUFFICIENT_BALANCE;
    }

    // Note: Tg <= B_Hl - l(B_R)u can only be checked before retirement
    // (It requires knowing the parent block)

    return ValidationStatus::SUCCESS;
}

template <evmc_revision rev>
constexpr ValidationStatus static_validate_header(BlockHeader const &header)
{
    // YP eq. 56
    if (MONAD_UNLIKELY(header.gas_used > header.gas_limit)) {
        return ValidationStatus::GAS_ABOVE_LIMIT;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(header.gas_limit < 5000)) {
        return ValidationStatus::INVALID_GAS_LIMIT;
    }

    // EIP-1985
    if (MONAD_UNLIKELY(
            header.gas_limit > std::numeric_limits<int64_t>::max())) {
        return ValidationStatus::INVALID_GAS_LIMIT;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(header.extra_data.length() > 32)) {
        return ValidationStatus::EXTRA_DATA_TOO_LONG;
    }

    // TODO: Does DAO necessarily need to be in Homestead?
    // EIP-779
    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(
                header.number >= dao::dao_block_number &&
                header.number <= dao::dao_block_number + 9 &&
                header.extra_data != dao::extra_data)) {
            return ValidationStatus::WRONG_DAO_EXTRA_DATA;
        }
    }

    // Validate Field Existence
    // EIP-1559
    if constexpr (rev < EVMC_LONDON) {
        if (MONAD_UNLIKELY(header.base_fee_per_gas.has_value())) {
            return ValidationStatus::FIELD_BEFORE_FORK;
        }
    }
    else if (MONAD_UNLIKELY(!header.base_fee_per_gas.has_value())) {
        return ValidationStatus::MISSING_FIELD;
    }

    // EIP-4895
    if constexpr (rev < EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(header.withdrawals_root.has_value())) {
            return ValidationStatus::FIELD_BEFORE_FORK;
        }
    }
    else if (MONAD_UNLIKELY(!header.withdrawals_root.has_value())) {
        return ValidationStatus::MISSING_FIELD;
    }

    // EIP-3675
    if constexpr (rev >= EVMC_PARIS) {
        if (MONAD_UNLIKELY(header.difficulty != 0)) {
            return ValidationStatus::POW_BLOCK_AFTER_MERGE;
        }

        constexpr byte_string_fixed<8> empty_nonce{
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
        if (MONAD_UNLIKELY(header.nonce != empty_nonce)) {
            return ValidationStatus::INVALID_NONCE;
        }

        if (MONAD_UNLIKELY(header.ommers_hash != NULL_LIST_HASH)) {
            return ValidationStatus::WRONG_OMMERS_HASH;
        }
    }

    return ValidationStatus::SUCCESS;
}

template <evmc_revision rev>
constexpr ValidationStatus static_validate_ommers(Block const &block)
{
    // TODO: What we really need is probably a generic ommer hash computation
    // function Instead of just checking this special case
    if (MONAD_UNLIKELY(
            block.ommers.empty() &&
            block.header.ommers_hash != NULL_LIST_HASH)) {
        return ValidationStatus::WRONG_OMMERS_HASH;
    }

    // EIP-3675
    if constexpr (rev >= EVMC_PARIS) {
        if (MONAD_UNLIKELY(!block.ommers.empty())) {
            return ValidationStatus::TOO_MANY_OMMERS;
        }
        return ValidationStatus::SUCCESS;
    }

    // YP eq. 167
    if (MONAD_UNLIKELY(block.ommers.size() > 2)) {
        return ValidationStatus::TOO_MANY_OMMERS;
    }

    // Verified in go-ethereum
    if (MONAD_UNLIKELY(
            block.ommers.size() == 2 && block.ommers[0] == block.ommers[1])) {
        return ValidationStatus::DUPLICATE_OMMERS;
    }

    // YP eq. 167
    for (auto const &ommer : block.ommers) {
        if (auto const status = static_validate_header<rev>(ommer);
            status != ValidationStatus::SUCCESS) {
            return ValidationStatus::INVALID_OMMER_HEADER;
        }
    }

    return ValidationStatus::SUCCESS;
}

template <evmc_revision rev>
constexpr ValidationStatus static_validate_body(Block const &block)
{
    // TODO: Should we put computationally heavy validate_root(txn,
    // withdraw) here?

    // EIP-4895
    if constexpr (rev < EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(block.withdrawals.has_value())) {
            return ValidationStatus::FIELD_BEFORE_FORK;
        }
    }
    else {
        if (MONAD_UNLIKELY(!block.withdrawals.has_value())) {
            return ValidationStatus::MISSING_FIELD;
        }
    }

    if (auto const status = static_validate_ommers<rev>(block);
        status != ValidationStatus::SUCCESS) {
        return status;
    }

    for (auto const &txn : block.transactions) {
        if (auto const status =
                static_validate_txn<rev>(txn, block.header.base_fee_per_gas);
            status != ValidationStatus::SUCCESS) {
            return status;
        }
    }

    return ValidationStatus::SUCCESS;
}

template <evmc_revision rev>
constexpr ValidationStatus static_validate_block(Block const &block)
{
    if (auto const header_status = static_validate_header<rev>(block.header);
        header_status != ValidationStatus::SUCCESS) {
        return header_status;
    }

    if (auto const body_status = static_validate_body<rev>(block);
        body_status != ValidationStatus::SUCCESS) {
        return body_status;
    }

    return ValidationStatus::SUCCESS;
}

MONAD_NAMESPACE_END

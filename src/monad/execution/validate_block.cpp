#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/execution/validation_status.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <limits>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
ValidationStatus static_validate_header(BlockHeader const &header)
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

EXPLICIT_EVMC_REVISION(static_validate_header);

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
        if (auto const status = static_validate_transaction<rev>(
                txn, block.header.base_fee_per_gas);
            status != ValidationStatus::SUCCESS) {
            return status;
        }
    }

    return ValidationStatus::SUCCESS;
}

template <evmc_revision rev>
ValidationStatus static_validate_block(Block const &block)
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

EXPLICIT_EVMC_REVISION(static_validate_block);

MONAD_NAMESPACE_END

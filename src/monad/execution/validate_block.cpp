#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/validate_transaction.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <limits>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

template <evmc_revision rev>
BlockResult static_validate_header(BlockHeader const &header)
{
    // YP eq. 56
    if (MONAD_UNLIKELY(header.gas_used > header.gas_limit)) {
        return BlockError::GasAboveLimit;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(header.gas_limit < 5000)) {
        return BlockError::InvalidGasLimit;
    }

    // EIP-1985
    if (MONAD_UNLIKELY(
            header.gas_limit > std::numeric_limits<int64_t>::max())) {
        return BlockError::InvalidGasLimit;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(header.extra_data.length() > 32)) {
        return BlockError::ExtraDataTooLong;
    }

    // TODO: Does DAO necessarily need to be in Homestead?
    // EIP-779
    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(
                header.number >= dao::dao_block_number &&
                header.number <= dao::dao_block_number + 9 &&
                header.extra_data != dao::extra_data)) {
            return BlockError::WrongDaoExtraData;
        }
    }

    // Validate Field Existence
    // EIP-1559
    if constexpr (rev < EVMC_LONDON) {
        if (MONAD_UNLIKELY(header.base_fee_per_gas.has_value())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else if (MONAD_UNLIKELY(!header.base_fee_per_gas.has_value())) {
        return BlockError::MissingField;
    }

    // EIP-4895
    if constexpr (rev < EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(header.withdrawals_root.has_value())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else if (MONAD_UNLIKELY(!header.withdrawals_root.has_value())) {
        return BlockError::MissingField;
    }

    // EIP-3675
    if constexpr (rev >= EVMC_PARIS) {
        if (MONAD_UNLIKELY(header.difficulty != 0)) {
            return BlockError::PowBlockAfterMerge;
        }

        constexpr byte_string_fixed<8> empty_nonce{
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
        if (MONAD_UNLIKELY(header.nonce != empty_nonce)) {
            return BlockError::InvalidNonce;
        }

        if (MONAD_UNLIKELY(header.ommers_hash != NULL_LIST_HASH)) {
            return BlockError::WrongOmmersHash;
        }
    }

    return success();
}

EXPLICIT_EVMC_REVISION(static_validate_header);

template <evmc_revision rev>
constexpr BlockResult static_validate_ommers(Block const &block)
{
    // TODO: What we really need is probably a generic ommer hash computation
    // function Instead of just checking this special case
    if (MONAD_UNLIKELY(
            block.ommers.empty() &&
            block.header.ommers_hash != NULL_LIST_HASH)) {
        return BlockError::WrongOmmersHash;
    }

    // EIP-3675
    if constexpr (rev >= EVMC_PARIS) {
        if (MONAD_UNLIKELY(!block.ommers.empty())) {
            return BlockError::TooManyOmmers;
        }
    }

    // YP eq. 167
    if (MONAD_UNLIKELY(block.ommers.size() > 2)) {
        return BlockError::TooManyOmmers;
    }

    // Verified in go-ethereum
    if (MONAD_UNLIKELY(
            block.ommers.size() == 2 && block.ommers[0] == block.ommers[1])) {
        return BlockError::DuplicateOmmers;
    }

    // YP eq. 167
    for (auto const &ommer : block.ommers) {
        BOOST_OUTCOME_TRY(static_validate_header<rev>(ommer));
    }

    return success();
}

template <evmc_revision rev>
constexpr BlockResult static_validate_body(Block const &block)
{
    // TODO: Should we put computationally heavy validate_root(txn,
    // withdraw) here?

    // EIP-4895
    if constexpr (rev < EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(block.withdrawals.has_value())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else {
        if (MONAD_UNLIKELY(!block.withdrawals.has_value())) {
            return BlockError::MissingField;
        }
    }

    BOOST_OUTCOME_TRY(static_validate_ommers<rev>(block));

    // TODO remove
    for (auto const &txn : block.transactions) {
        if (auto const status = static_validate_transaction<rev>(
                txn, block.header.base_fee_per_gas);
            status != ValidationStatus::SUCCESS) {
            return BlockError::InvalidNonce;
        }
    }

    return success();
}

template <evmc_revision rev>
BlockResult static_validate_block(Block const &block)
{
    BOOST_OUTCOME_TRY(static_validate_header<rev>(block.header));

    BOOST_OUTCOME_TRY(static_validate_body<rev>(block));

    return success();
}

EXPLICIT_EVMC_REVISION(static_validate_block);

MONAD_NAMESPACE_END

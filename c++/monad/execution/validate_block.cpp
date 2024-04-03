#include <monad/execution/validate_block.hpp>

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>

#include <evmc/evmc.h>

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
#include <boost/outcome/try.hpp>

#include <cstdint>
#include <initializer_list>
#include <limits>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

template <evmc_revision rev>
Result<void> static_validate_header(BlockHeader const &header)
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
constexpr Result<void> static_validate_ommers(Block const &block)
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
constexpr Result<void> static_validate_body(Block const &block)
{
    // EIP-4895
    if constexpr (rev < EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(
                block.withdrawals.has_value() &&
                !block.withdrawals.value().empty())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else {
        if (MONAD_UNLIKELY(!block.withdrawals.has_value())) {
            return BlockError::MissingField;
        }
    }

    BOOST_OUTCOME_TRY(static_validate_ommers<rev>(block));

    return success();
}

template <evmc_revision rev>
Result<void> static_validate_block(Block const &block)
{
    BOOST_OUTCOME_TRY(static_validate_header<rev>(block.header));

    BOOST_OUTCOME_TRY(static_validate_body<rev>(block));

    return success();
}

EXPLICIT_EVMC_REVISION(static_validate_block);

Result<void> static_validate_block(evmc_revision const rev, Block const &block)
{
    switch (rev) {
    case EVMC_SHANGHAI:
        return static_validate_block<EVMC_SHANGHAI>(block);
    case EVMC_PARIS:
        return static_validate_block<EVMC_PARIS>(block);
    case EVMC_LONDON:
        return static_validate_block<EVMC_LONDON>(block);
    case EVMC_BERLIN:
        return static_validate_block<EVMC_BERLIN>(block);
    case EVMC_ISTANBUL:
        return static_validate_block<EVMC_ISTANBUL>(block);
    case EVMC_PETERSBURG:
    case EVMC_CONSTANTINOPLE:
        return static_validate_block<EVMC_PETERSBURG>(block);
    case EVMC_BYZANTIUM:
        return static_validate_block<EVMC_BYZANTIUM>(block);
    case EVMC_SPURIOUS_DRAGON:
        return static_validate_block<EVMC_SPURIOUS_DRAGON>(block);
    case EVMC_TANGERINE_WHISTLE:
        return static_validate_block<EVMC_TANGERINE_WHISTLE>(block);
    case EVMC_HOMESTEAD:
        return static_validate_block<EVMC_HOMESTEAD>(block);
    case EVMC_FRONTIER:
        return static_validate_block<EVMC_FRONTIER>(block);
    default:
        break;
    }
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::BlockError>::mapping> const &
quick_status_code_from_enum<monad::BlockError>::value_mappings()
{
    using monad::BlockError;

    static std::initializer_list<mapping> const v = {
        {BlockError::Success, "success", {errc::success}},
        {BlockError::GasAboveLimit, "gas above limit", {}},
        {BlockError::InvalidGasLimit, "invalid gas limit", {}},
        {BlockError::ExtraDataTooLong, "extra data too long", {}},
        {BlockError::WrongOmmersHash, "wrong ommers hash", {}},
        {BlockError::FieldBeforeFork, "field before fork", {}},
        {BlockError::MissingField, "missing field", {}},
        {BlockError::PowBlockAfterMerge, "pow block after merge", {}},
        {BlockError::InvalidNonce, "invalid nonce", {}},
        {BlockError::TooManyOmmers, "too many ommers", {}},
        {BlockError::DuplicateOmmers, "duplicate ommers", {}},
        {BlockError::InvalidOmmerHeader, "invalid ommer header", {}},
        {BlockError::WrongDaoExtraData, "wrong dao extra data", {}},
        {BlockError::WrongLogsBloom, "wrong logs bloom", {}},
        {BlockError::InvalidGasUsed, "invalid gas used", {}},
        {BlockError::WrongStateRoot, "wrong state root", {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

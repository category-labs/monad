#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#include <boost/outcome/experimental/status_result.hpp>

MONAD_NAMESPACE_BEGIN

enum class BlockError
{
    Success = 0,
    GasAboveLimit,
    InvalidGasLimit,
    ExtraDataTooLong,
    WrongOmmersHash,
    FieldBeforeFork,
    MissingField,
    PowBlockAfterMerge,
    InvalidNonce,
    TooManyOmmers,
    DuplicateOmmers,
    InvalidOmmerHeader,
    WrongDaoExtraData,
    WrongLogsBloom,
    InvalidGasUsed
};

using BlockResult =
    BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<void>;

struct Block;
struct BlockHeader;

template <evmc_revision rev>
BlockResult static_validate_header(BlockHeader const &);

template <evmc_revision rev>
BlockResult static_validate_block(Block const &);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::BlockError>
    : quick_status_code_from_enum_defaults<monad::BlockError>
{
    static constexpr auto const domain_name = "Block Error";
    static constexpr auto const domain_uuid =
        "6eb636da00ddd479646eeb39b8168c814cb4";

    static std::initializer_list<mapping> const &value_mappings()
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
            {BlockError::InvalidGasUsed, "invalid gas used", {}}};
        return v;
    }
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

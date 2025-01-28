#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>
#include <vector>

MONAD_NAMESPACE_BEGIN

enum class BlockError
{
    Success = 0,
    GasAboveLimit,
    InvalidGasLimit,
    ExtraDataTooLong,
    WrongOmmersHash,
    WrongParentHash,
    FieldBeforeFork,
    MissingField,
    PowBlockAfterMerge,
    InvalidNonce,
    TooManyOmmers,
    DuplicateOmmers,
    InvalidOmmerHeader,
    WrongDaoExtraData,
    WrongLogsBloom,
    InvalidGasUsed,
    WrongMerkleRoot
};

struct Block;
struct BlockHeader;

Receipt::Bloom &bloom_combine(Receipt::Bloom &, Receipt::Bloom const &);

bytes32_t compute_ommers_hash(std::vector<BlockHeader> const &);

template <evmc_revision rev>
Result<void> static_validate_header(BlockHeader const &);

template <evmc_revision rev>
Result<void> static_validate_block(Block const &);

Result<void> static_validate_block(evmc_revision, Block const &);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::BlockError>
    : quick_status_code_from_enum_defaults<monad::BlockError>
{
    static constexpr auto const domain_name = "Block Error";
    static constexpr auto const domain_uuid =
        "6eb636da00ddd479646eeb39b8168c814cb4";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

#pragma once

#include <monad/config.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>

#include <initializer_list>
#include <optional>

MONAD_NAMESPACE_BEGIN

enum class TransactionError
{
    Success = 0,
    InsufficientBalance,
    IntrinsicGasGreaterThanLimit,
    BadNonce,
    SenderNotEoa,
    TypeNotSupported,
    MaxFeeLessThanBase,
    PriorityFeeGreaterThanMax,
    NonceExceedsMax,
    InitCodeLimitExceeded,
    GasLimitReached,
    WrongChainId,
    MissingSender,
    GasLimitOverflow
};

class State;
struct Transaction;

template <evmc_revision rev>
Result<void> static_validate_transaction(
    Transaction const &, std::optional<uint256_t> const &base_fee_per_gas);

Result<void> validate_transaction(State &, Transaction const &);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::TransactionError>
    : quick_status_code_from_enum_defaults<monad::TransactionError>
{
    static constexpr auto const domain_name = "Transaction Error";
    static constexpr auto const domain_uuid =
        "2f22309f9d7d3e03fbb1eb1ff328da12d290";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

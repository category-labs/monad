#pragma once

#include <monad/config.hpp>
#include <monad/core/int.hpp>
#include <monad/execution/validation_status.hpp>

#include <evmc/evmc.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

class State;
struct Transaction;

template <evmc_revision rev>
ValidationStatus static_validate_transaction(
    Transaction const &, std::optional<uint256_t> const &base_fee_per_gas);

ValidationStatus validate_transaction(State &, Transaction const &);

MONAD_NAMESPACE_END

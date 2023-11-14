#pragma once

#include <monad/config.hpp>
#include <monad/core/int.hpp>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct Transaction;

template <evmc_revision rev>
uint64_t g_data(Transaction const &) noexcept;

template <evmc_revision rev>
uint64_t intrinsic_gas(Transaction const &) noexcept;

template <evmc_revision rev>
uint256_t
gas_price(Transaction const &, uint256_t const &base_fee_per_gas) noexcept;

template <evmc_revision rev>
uint256_t calculate_txn_award(
    Transaction const &, uint256_t const &base_fee_per_gas,
    uint64_t gas_used) noexcept;

MONAD_NAMESPACE_END

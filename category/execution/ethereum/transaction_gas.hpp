#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct Transaction;

template <evmc_revision rev>
uint64_t g_data(Transaction const &) noexcept;

template <evmc_revision rev>
uint64_t intrinsic_gas(Transaction const &) noexcept;

uint64_t floor_data_gas(Transaction const &) noexcept;

template <evmc_revision rev>
uint256_t
gas_price(Transaction const &, uint256_t const &base_fee_per_gas) noexcept;

template <evmc_revision rev>
uint256_t calculate_txn_award(
    Transaction const &, uint256_t const &base_fee_per_gas,
    uint64_t gas_used) noexcept;

inline intx::uint512
max_gas_cost(uint64_t const gas_limit, uint256_t max_fee_per_gas) noexcept
{
    return intx::umul(uint256_t{gas_limit}, max_fee_per_gas);
}

MONAD_NAMESPACE_END

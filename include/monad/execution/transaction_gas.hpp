#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/transaction.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
[[nodiscard]] uint64_t g_data(Transaction const &) noexcept;

template <evmc_revision rev>
[[nodiscard]] uint64_t intrinsic_gas(Transaction const &);

// Txn reward related functions
[[nodiscard]] inline constexpr uint256_t
priority_fee_per_gas(Transaction const &txn, uint256_t const &base_fee_per_gas)
{
    MONAD_DEBUG_ASSERT(txn.max_fee_per_gas >= base_fee_per_gas);
    if (txn.type == TransactionType::eip1559) {
        return std::min(
            txn.max_priority_fee_per_gas,
            txn.max_fee_per_gas - base_fee_per_gas);
    }
    // per EIP-1559: "Legacy Ethereum transactions will still work and
    // be included in blocks, but they will not benefit directly from
    // the new pricing system. This is due to the fact that upgrading
    // from legacy transactions to new transactions results in the
    // legacy transaction’s gas_price entirely being consumed either
    // by the base_fee_per_gas and the priority_fee_per_gas."
    return txn.max_fee_per_gas - base_fee_per_gas;
}

template <evmc_revision rev>
constexpr uint256_t
gas_price(Transaction const &txn, uint256_t const &base_fee_per_gas)
{
    if constexpr (rev < EVMC_LONDON) {
        return txn.max_fee_per_gas;
    }
    // EIP-1559
    return priority_fee_per_gas(txn, base_fee_per_gas) + base_fee_per_gas;
}

template <evmc_revision rev>
constexpr uint256_t calculate_txn_award(
    Transaction const &txn, uint256_t const &base_fee_per_gas,
    uint64_t const gas_used)
{
    if constexpr (rev < EVMC_LONDON) {
        return gas_used * gas_price<rev>(txn, base_fee_per_gas);
    }
    return gas_used * priority_fee_per_gas(txn, base_fee_per_gas);
}

MONAD_NAMESPACE_END

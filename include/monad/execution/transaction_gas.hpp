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

// Intrinsic gas related functions
[[nodiscard]] inline constexpr auto
g_txn_create(Transaction const &txn) noexcept
{
    if (!txn.to.has_value()) {
        return 32'000u;
    }
    return 0u;
}

// https://eips.ethereum.org/EIPS/eip-2930
[[nodiscard]] inline constexpr auto
g_access_and_storage(Transaction const &txn) noexcept
{
    uint64_t g = txn.access_list.size() * 2'400u;
    for (auto &i : txn.access_list) {
        g += i.keys.size() * 1'900u;
    }
    return g;
}

[[nodiscard]] inline constexpr uint64_t
g_extra_cost_init(Transaction const &txn) noexcept
{
    if (!txn.to.has_value()) {
        return ((txn.data.length() + 31u) / 32u) * 2u;
    }
    return 0u;
}

// YP, Eqn. 60, first summation
template <evmc_revision rev>
[[nodiscard]] constexpr uint64_t g_data(Transaction const &txn) noexcept
{
    auto const zeros = std::count_if(
        std::cbegin(txn.data), std::cend(txn.data), [](unsigned char c) {
            return c == 0x00;
        });
    auto const nonzeros = txn.data.size() - static_cast<uint64_t>(zeros);
    if constexpr (rev < EVMC_ISTANBUL) {
        // https://eips.ethereum.org/EIPS/eip-2028
        return static_cast<uint64_t>(zeros) * 4u + nonzeros * 68u;
    }
    return static_cast<uint64_t>(zeros) * 4u + nonzeros * 16u;
}

template <evmc_revision rev>
[[nodiscard]] constexpr uint64_t intrinsic_gas(Transaction const &txn)
{
    if constexpr (rev < EVMC_HOMESTEAD) {
        // YP, section 6.2, Eqn. 60
        return 21'000 + g_data<rev>(txn);
    }
    else if constexpr (rev < EVMC_BERLIN) {
        return 21'000 + g_data<rev>(txn) + g_txn_create(txn);
    }
    else if constexpr (rev < EVMC_SHANGHAI) {
        return 21'000 + g_data<rev>(txn) + g_txn_create(txn) +
               g_access_and_storage(txn);
    }
    else {
        // EIP-3860
        return 21'000 + g_data<rev>(txn) + g_txn_create(txn) +
               g_access_and_storage(txn) + g_extra_cost_init(txn);
    }
}

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
    // per eip-1559: "Legacy Ethereum transactions will still work and
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
    // https://eips.ethereum.org/EIPS/eip-1559
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

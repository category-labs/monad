#pragma once

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

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
template <class TTraits>
[[nodiscard]] constexpr uint64_t g_data(Transaction const &txn) noexcept
{
    auto const zeros = std::count_if(
        std::cbegin(txn.data), std::cend(txn.data), [](unsigned char c) {
            return c == 0x00;
        });
    auto const nonzeros = txn.data.size() - static_cast<uint64_t>(zeros);
    if constexpr (TTraits::rev < EVMC_ISTANBUL) {
        // https://eips.ethereum.org/EIPS/eip-2028
        return static_cast<uint64_t>(zeros) * 4u + nonzeros * 68u;
    }
    return static_cast<uint64_t>(zeros) * 4u + nonzeros * 16u;
}

template <class TTraits>
[[nodiscard]] constexpr uint64_t intrinsic_gas(Transaction const &txn)
{
    if constexpr (TTraits::rev < EVMC_HOMESTEAD) {
        // YP, section 6.2, Eqn. 60
        return 21'000 + g_data<TTraits>(txn);
    }
    else if constexpr (TTraits::rev < EVMC_BERLIN) {
        return 21'000 + g_data<TTraits>(txn) + g_txn_create(txn);
    }
    else if constexpr (TTraits::rev < EVMC_SHANGHAI) {
        return 21'000 + g_data<TTraits>(txn) + g_txn_create(txn) +
               g_access_and_storage(txn);
    }
    else {
        // EIP-3860
        return 21'000 + g_data<TTraits>(txn) + g_txn_create(txn) +
               g_access_and_storage(txn) + g_extra_cost_init(txn);
    }
}

MONAD_EXECUTION_NAMESPACE_END

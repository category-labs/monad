#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>

#include <evmc/evmc.h>

#include <algorithm>
#include <cstdint>
#include <iterator>

MONAD_NAMESPACE_BEGIN

// Intrinsic gas related functions
[[nodiscard]] inline constexpr auto g_txn_create(Transaction const &tx) noexcept
{
    if (!tx.to.has_value()) {
        return 32'000u;
    }
    return 0u;
}

// EIP-2930
[[nodiscard]] inline constexpr auto
g_access_and_storage(Transaction const &tx) noexcept
{
    uint64_t g = tx.access_list.size() * 2'400u;
    for (auto &i : tx.access_list) {
        g += i.keys.size() * 1'900u;
    }
    return g;
}

[[nodiscard]] inline constexpr uint64_t
g_extra_cost_init(Transaction const &tx) noexcept
{
    if (!tx.to.has_value()) {
        return ((tx.data.length() + 31u) / 32u) * 2u;
    }
    return 0u;
}

// YP, Eqn. 60, first summation
template <evmc_revision rev>
[[nodiscard]] uint64_t g_data(Transaction const &tx) noexcept
{
    auto const zeros = std::count_if(
        std::cbegin(tx.data), std::cend(tx.data), [](unsigned char c) {
            return c == 0x00;
        });
    auto const nonzeros = tx.data.size() - static_cast<uint64_t>(zeros);
    if constexpr (rev < EVMC_ISTANBUL) {
        // EIP-2028
        return static_cast<uint64_t>(zeros) * 4u + nonzeros * 68u;
    }
    return static_cast<uint64_t>(zeros) * 4u + nonzeros * 16u;
}

EXPLICIT_EVMC_REVISION(g_data);

template <evmc_revision rev>
[[nodiscard]] uint64_t intrinsic_gas(Transaction const &tx)
{
    if constexpr (rev < EVMC_HOMESTEAD) {
        // YP, section 6.2, Eqn. 60
        return 21'000 + g_data<rev>(tx);
    }
    else if constexpr (rev < EVMC_BERLIN) {
        return 21'000 + g_data<rev>(tx) + g_txn_create(tx);
    }
    else if constexpr (rev < EVMC_SHANGHAI) {
        return 21'000 + g_data<rev>(tx) + g_txn_create(tx) +
               g_access_and_storage(tx);
    }
    else {
        // EIP-3860
        return 21'000 + g_data<rev>(tx) + g_txn_create(tx) +
               g_access_and_storage(tx) + g_extra_cost_init(tx);
    }
}

EXPLICIT_EVMC_REVISION(intrinsic_gas);

MONAD_NAMESPACE_END

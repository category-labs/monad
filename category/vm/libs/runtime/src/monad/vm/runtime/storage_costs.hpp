#pragma once

#include <monad/vm/evm/opcodes.hpp>

#include <evmc/evmc.hpp>

#include <array>
#include <cstdint>

namespace monad::vm::runtime
{
    struct StoreCost
    {
        std::int64_t gas_cost;
        std::int64_t gas_refund;
    };

    template <evmc_revision Rev>
    struct StorageCostTable
    {
        static_assert(Rev >= EVMC_FRONTIER && Rev <= EVMC_PRAGUE);
        static constexpr std::array<StoreCost, 9> costs{};
    };

    template <evmc_revision Rev>
    static consteval std::int64_t minimum_store_gas()
    {
        constexpr auto costs = StorageCostTable<Rev>::costs;
        constexpr auto min_gas =
            std::min_element(costs.begin(), costs.end(), [](auto ca, auto cb) {
                return ca.gas_cost < cb.gas_cost;
            })->gas_cost;
        static_assert(
            compiler::opcode_table<Rev>[compiler::SSTORE].min_gas == min_gas);
        return min_gas;
    }

    template <evmc_revision Rev>
    constexpr StoreCost store_cost(evmc_storage_status status)
    {
        return StorageCostTable<Rev>::costs[status];
    }

    template <>
    struct StorageCostTable<EVMC_FRONTIER>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EVMC_HOMESTEAD>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EVMC_TANGERINE_WHISTLE>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EVMC_SPURIOUS_DRAGON>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EVMC_BYZANTIUM>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EVMC_CONSTANTINOPLE>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 200, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 200, .gas_refund = -15000},
            StoreCost{.gas_cost = 200, .gas_refund = 15000},
            StoreCost{.gas_cost = 200, .gas_refund = -10200},
            StoreCost{.gas_cost = 200, .gas_refund = 19800},
            StoreCost{.gas_cost = 200, .gas_refund = 4800},
        };
    };

    template <>
    struct StorageCostTable<EVMC_PETERSBURG>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EVMC_ISTANBUL>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 800, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 800, .gas_refund = -15000},
            StoreCost{.gas_cost = 800, .gas_refund = 15000},
            StoreCost{.gas_cost = 800, .gas_refund = -10800},
            StoreCost{.gas_cost = 800, .gas_refund = 19200},
            StoreCost{.gas_cost = 800, .gas_refund = 4200},
        };
    };

    template <>
    struct StorageCostTable<EVMC_BERLIN>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 15000},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -15000},
            StoreCost{.gas_cost = 100, .gas_refund = 15000},
            StoreCost{.gas_cost = 100, .gas_refund = -12200},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EVMC_LONDON>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EVMC_PARIS>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EVMC_SHANGHAI>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EVMC_CANCUN>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EVMC_PRAGUE>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };
}

#pragma once

#include <monad/config.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/transaction.hpp>

#include <algorithm>

MONAD_NAMESPACE_BEGIN

// https://ethereum.org/en/history/
namespace fork_traits
{
    struct frontier
    {
        static constexpr auto block_number = 0u;

        // YP, Eqn. 60, first summation
        [[nodiscard]] static constexpr inline auto
        g_data(Transaction const &t) noexcept
        {
            const unsigned zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            const auto nonzeros = t.data.size() - zeros;
            return zeros * 4 + nonzeros * 68;
        }

        // YP, section 6.2, Eqn. 60
        [[nodiscard]] static constexpr inline unsigned
        intrinsic_gas(Transaction const &t) noexcept
        {
            return 21'000 + g_data(t);
        }

        [[nodiscard]] static constexpr inline auto starting_nonce() noexcept
        {
            return 0;
        }

        template <class TState>
        [[nodiscard]] static constexpr inline uint64_t
        get_selfdestruct_refund(TState const &s) noexcept
        {
            return s.total_selfdestructs() * 24'000;
        }

        [[nodiscard]] static constexpr inline uint64_t
        max_refund_quotient() noexcept
        {
            return 2u;
        }

        template <class TState>
        static constexpr inline void destruct_touched_dead(TState &) noexcept
        {
        }

        template <class TState>
        static constexpr inline bool enough_gas_to_store_code(
            TState &s, address_t const &a, evmc_result &r) noexcept
        {
            int const deploy_cost = r.output_size * 200;
            if (r.gas_left >= deploy_cost) {
                s.set_code(a, {r.output_data, r.output_size});
                r.gas_left -= deploy_cost;
                r.create_address = a;
                return true;
            }
            return false;
        }
        template <class TState>
        [[nodiscard]] static constexpr inline bool store_contract_code(
            TState &s, address_t const &a, evmc_result &r) noexcept
        {
            if (r.status_code == EVMC_SUCCESS) {
                enough_gas_to_store_code(s, a, r);
            }
            else {
                r.gas_left = 0;
            }
            return true;
        }
    };

    struct homestead : public frontier
    {
        // https://eips.ethereum.org/EIPS/eip-2
        static constexpr auto block_number = 1'150'000u;

        [[nodiscard]] static constexpr inline auto
        g_txcreate(Transaction const &t) noexcept
        {
            if (!t.to.has_value()) {
                return 32'000u;
            }
            return 0u;
        }

        [[nodiscard]] static constexpr inline auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t);
        }

        template <class TState>
        [[nodiscard]] static constexpr inline bool store_contract_code(
            TState &s, address_t const &a, evmc_result &r) noexcept
        {
            if (r.status_code == EVMC_SUCCESS) {
                if (!enough_gas_to_store_code(s, a, r)) {
                    r.status_code = EVMC_OUT_OF_GAS;
                    r.gas_left = 0;
                    return false;
                }
            }
            else {
                r.gas_left = 0;
                return false;
            }
            return true;
        }
    };

    // dao - 1'920'000
    // tangerine_whistle - 2'463'000

    struct spurious_dragon : homestead
    {
        static constexpr auto block_number = 2'675'000u;

        // https://eips.ethereum.org/EIPS/eip-161
        [[nodiscard]] static constexpr inline auto starting_nonce() noexcept
        {
            return 1;
        }

        template <class TState>
        static constexpr inline void destruct_touched_dead(TState &s) noexcept
        {
            s.destruct_touched_dead();
        }

        static constexpr inline bool contract_too_big(evmc_result &r) noexcept
        {
            // EIP-170
            if (r.output_size > 0x6000) {
                r.status_code = EVMC_OUT_OF_GAS;
                r.gas_left = 0;
                return true;
            }

            return false;
        }

        template <class TState>
        [[nodiscard]] static constexpr inline bool store_contract_code(
            TState &s, address_t const &a, evmc_result &r) noexcept
        {
            if (contract_too_big(r)) {
                return false;
            }

            return homestead::store_contract_code(s, a, r);
        }
    };

    struct byzantium : spurious_dragon
    {
        static constexpr auto block_number = 4'370'000;

        template <class TState>
        [[nodiscard]] static constexpr inline bool store_contract_code(
            TState &s, address_t const &a, evmc_result &r) noexcept
        {
            if (contract_too_big(r)) {
                return false;
            }

            if (r.status_code == EVMC_SUCCESS) {
                if (!enough_gas_to_store_code(s, a, r)) {
                    r.status_code = EVMC_OUT_OF_GAS;
                    r.gas_left = 0;
                    return false;
                }
                return true;
            }
            // EIP-140 - support remaining gas with REVERT
            else if (r.status_code != EVMC_REVERT) {
                r.gas_left = 0;
            }

            return false;
        }
    };
    // constantinople - 7'280'000

    struct istanbul : public byzantium // constantinople
    {
        static constexpr auto block_number = 9'069'000u;

        // https://eips.ethereum.org/EIPS/eip-2028
        [[nodiscard]] static constexpr inline unsigned
        g_data(Transaction const &t) noexcept
        {
            const unsigned zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            const auto nonzeros = t.data.size() - zeros;
            return zeros * 4u + nonzeros * 16u;
        }

        [[nodiscard]] static constexpr inline auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t);
        }
    };

    // muir_glacier - 9'200'000

    struct berlin : public istanbul
    {
        static constexpr auto block_number = 12'244'000u;

        // https://eips.ethereum.org/EIPS/eip-2930
        [[nodiscard]] static constexpr inline auto
        g_access_and_storage(Transaction const &t) noexcept
        {
            uint64_t g = t.access_list.size() * 2'400u;
            for (auto &i : t.access_list) {
                g += i.keys.size() * 1'900u;
            }
            return g;
        }

        [[nodiscard]] static constexpr inline auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t) +
                   g_access_and_storage(t);
        }
    };

    struct london : public berlin
    {
        static constexpr auto block_number = 12'965'000;

        // https://eips.ethereum.org/EIPS/eip-3529
        template <class TState>
        [[nodiscard]] static constexpr inline uint64_t
        get_selfdestruct_refund(TState const &) noexcept
        {
            return 0u;
        }

        [[nodiscard]] static constexpr inline uint64_t
        max_refund_quotient() noexcept
        {
            return 5u;
        }

        // https://eips.ethereum.org/EIPS/eip-3541
        template <class TState>
        [[nodiscard]] static constexpr inline bool store_contract_code(
            TState &s, address_t const &a, evmc_result &r) noexcept
        {
            if (r.output_size > 0 && r.output_data[0] == 0xef) {
                r.status_code = EVMC_CONTRACT_VALIDATION_FAILURE;
                r.gas_left = 0;
                return false;
            }
            return berlin::store_contract_code(s, a, r);
        }
    };

    // paris - 15'537'394
}

MONAD_NAMESPACE_END

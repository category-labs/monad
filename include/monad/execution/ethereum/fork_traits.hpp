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

        [[nodiscard]] static constexpr inline auto g_data(Transaction const &t)
        {
            const unsigned zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            const auto nonzeros = t.data.size() - zeros;
            return zeros * 4 + nonzeros * 68;
        }

        // Yellow paper, section 6.2, eqn. 60
        [[nodiscard]] static constexpr inline unsigned
        intrinsic_gas(Transaction const &t) noexcept
        {
            return 21'000 + g_data(t);
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
    };

    // dao - 1'920'000
    // tangerine_whistle - 2'463'000
    // spurious_dragon - 2'675'000
    // byzantium - 4'370'000
    // constantinople - 7'280'000

    struct istanbul : public homestead // constantinople
    {
        static constexpr auto block_number = 9'069'000u;

        // https://eips.ethereum.org/EIPS/eip-2028
        [[nodiscard]] static constexpr inline unsigned
        g_data(Transaction const &t)
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
        g_access_and_storage(Transaction const &t)
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

    // london - 12'965'000
    // paris - 15'537'394
}

MONAD_NAMESPACE_END


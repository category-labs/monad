#pragma once

#include <monad/config.hpp>
#include <monad/core/transaction.hpp>

MONAD_NAMESPACE_BEGIN

namespace hard_fork
{
    struct genesis
    {
        static constexpr auto block_number = 0;
        [[nodiscard]] static constexpr inline auto
        base_gas_cost(Transaction const &) noexcept
        {
            return 21'000;
        }
    };

    struct homestead : public genesis
    {
        // https://eips.ethereum.org/EIPS/eip-2
        static constexpr auto block_number = 1'150'000;
        [[nodiscard]] static constexpr inline auto
        base_gas_cost(Transaction const &t) noexcept
        {
            if (!t.to.has_value()) {
                return 53'000;
            }
            return genesis::base_gas_cost(t);
        }
    };
}
MONAD_NAMESPACE_END

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/execution/base_fee_per_gas.hpp>

MONAD_NAMESPACE_BEGIN

uint256_t base_fee_per_gas(BlockHeader const &parent_header)
{
    constexpr uint256_t initial_base_fee = 1'000'000'000;
    constexpr int base_fee_max_change_demoninator = 8;
    constexpr int elasticity_multiplier = 2;

    if (!parent_header.base_fee_per_gas.has_value()) {
        return initial_base_fee;
    }

    uint64_t const parent_gas_target{
        parent_header.gas_limit / elasticity_multiplier};

    if (MONAD_UNLIKELY(parent_header.gas_used == parent_gas_target)) {
        return parent_header.base_fee_per_gas.value();
    }
    else if (parent_header.gas_used > parent_gas_target) {
        uint64_t const delta = parent_header.gas_used - parent_gas_target;
        return parent_header.base_fee_per_gas.value() +
               std::max(
                   parent_header.base_fee_per_gas.value() * delta /
                       parent_gas_target / base_fee_max_change_demoninator,
                   uint256_t{1});
    }
    else {
        uint64_t const delta = parent_gas_target - parent_header.gas_used;
        return parent_header.base_fee_per_gas.value() -
               parent_header.base_fee_per_gas.value() * delta /
                   parent_gas_target / base_fee_max_change_demoninator;
    }
}

MONAD_NAMESPACE_END

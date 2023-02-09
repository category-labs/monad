#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

#include <evmc/evmc.h>

#include <optional>
#include <unordered_map>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace fake
{
    inline evmc_vm *get_fake_evmc()
    {
        return NULL;
    }

    // Simple fake state proxy
    struct Accounts
    {
        std::unordered_map<address_t, Account> _map{};
        address_t _a{};

        [[nodiscard]] std::optional<Account> fetch(address_t const &a)
        {
            _a = a;
            if (auto is_present = _map.find(a); is_present != _map.end())
                return {_map[a]};
            return {};
        };
        std::optional<Account> wait_for_data() { return _map[_a]; };
    };

    struct traits
    {
        static inline uint64_t block_number{};
        static inline uint64_t _intrinsic_gas{21'000u};
        static inline auto intrinsic_gas(Transaction const &)
        {
            return _intrinsic_gas;
        }
    };

    static_assert(concepts::fork_traits<traits>);
}

MONAD_EXECUTION_NAMESPACE_END

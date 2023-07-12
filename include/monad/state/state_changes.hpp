#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/state/config.hpp>

#include <optional>
#include <vector>

MONAD_STATE_NAMESPACE_BEGIN

struct StateChanges
{
    std::vector<std::pair<address_t, std::optional<Account>>> account_changes;
    std::unordered_map<address_t, std::vector<std::pair<bytes32_t, bytes32_t>>>
        storage_changes;
};

MONAD_STATE_NAMESPACE_END

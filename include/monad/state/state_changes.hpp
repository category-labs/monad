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
    using AccountChanges =
        std::vector<std::pair<address_t, std::optional<Account>>>;
    using StorageChanges = std::unordered_map<
        address_t, std::vector<std::pair<bytes32_t, bytes32_t>>>;
    AccountChanges account_changes;
    StorageChanges storage_changes;
};

MONAD_STATE_NAMESPACE_END

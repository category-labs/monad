#pragma once

#include <monad/db/config.hpp>
#include <monad/db/db_interface.hpp>
#include <monad/execution/execution_model.hpp>

MONAD_DB_NAMESPACE_BEGIN

// Database impl without trie root generating logic, backed by stl
struct InMemoryDB
    : public DBInterface<InMemoryDB, monad::execution::SerialExecution>
{
    using DBInterface<InMemoryDB, monad::execution::SerialExecution>::updates;

    std::unordered_map<address_t, Account> accounts;
    std::unordered_map<address_t, std::unordered_map<bytes32_t, bytes32_t>>
        storage;

    ////////////////////////////////////////////////////////////////////
    // DBInterface implementations
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] bool contains(address_t const &a) const
    {
        return accounts.contains(a);
    }

    [[nodiscard]] bool contains(address_t const &a, bytes32_t const &k) const
    {
        return storage.contains(a) && storage.at(a).contains(k);
    }

    [[nodiscard]] std::optional<Account> try_find(address_t const &a) const
    {
        if (accounts.contains(a)) {
            return accounts.at(a);
        }
        return std::nullopt;
    }

    [[nodiscard]] std::optional<bytes32_t>
    try_find(address_t const &a, bytes32_t const &k) const
    {
        if (!contains(a, k)) {
            return std::nullopt;
        }
        return storage.at(a).at(k);
    }

    void commit(state::changeset auto const &obj)
    {
        for (auto const &[a, updates] : obj.storage_changes) {
            for (auto const &[k, v] : updates) {
                if (v != bytes32_t{}) {
                    storage[a][k] = v;
                }
                else {
                    auto const n = storage[a].erase(k);
                    MONAD_DEBUG_ASSERT(n == 1);
                }
            }
            if (storage[a].empty()) {
                storage.erase(a);
            }
        }

        for (auto const &[a, acct] : obj.account_changes) {
            if (acct.has_value()) {
                accounts[a] = acct.value();
            }
            else {
                auto const n = accounts.erase(a);
                MONAD_DEBUG_ASSERT(n == 1);
            }
        }
    }

    constexpr void
    create_and_prune_block_history(uint64_t /* block_number */) const
    {
    }
};

MONAD_DB_NAMESPACE_END

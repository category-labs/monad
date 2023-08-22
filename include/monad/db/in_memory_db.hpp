#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>

MONAD_DB_NAMESPACE_BEGIN

// Database impl without trie root generating logic, backed by stl
struct InMemoryDB : public Db
{
    std::unordered_map<address_t, Account> accounts;
    std::unordered_map<address_t, std::unordered_map<bytes32_t, bytes32_t>>
        storage;
    std::unordered_map<bytes32_t, byte_string> code;

    [[nodiscard]] std::optional<Account>
    read_account(address_t const &a) override
    {
        if (accounts.contains(a)) {
            return accounts.at(a);
        }
        return std::nullopt;
    }

    [[nodiscard]] bytes32_t
    read_storage(address_t const &a, uint64_t, bytes32_t const &k) override
    {
        if (storage.contains(a) && storage.at(a).contains(k)) {
            return storage.at(a).at(k);
        }
        return bytes32_t{};
    }

    [[nodiscard]] byte_string read_code(bytes32_t const &hash) override
    {
        if (code.contains(hash)) {
            return code.at(hash);
        }
        return byte_string{};
    }

    void commit(state::StateChanges const &obj) override
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

        for (auto const &[ch, c] : obj.code_changes) {
            code[ch] = c;
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
    create_and_prune_block_history(uint64_t /* block_number */) const override
    {
    }
};

MONAD_DB_NAMESPACE_END

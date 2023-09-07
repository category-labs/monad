#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/state_deltas.hpp>

MONAD_DB_NAMESPACE_BEGIN

// Database impl without trie root generating logic, backed by stl
struct InMemoryDB : public Db
{
    std::unordered_map<address_t, Account> accounts;
    std::unordered_map<address_t, std::unordered_map<bytes32_t, bytes32_t>>
        storage;
    std::unordered_map<bytes32_t, byte_string> code;

    [[nodiscard]] std::optional<Account>
    read_account(address_t const &a) const override
    {
        if (accounts.contains(a)) {
            return accounts.at(a);
        }
        return std::nullopt;
    }

    [[nodiscard]] bytes32_t read_storage(
        address_t const &a, uint64_t, bytes32_t const &k) const override
    {
        if (storage.contains(a) && storage.at(a).contains(k)) {
            return storage.at(a).at(k);
        }
        return bytes32_t{};
    }

    [[nodiscard]] byte_string read_code(bytes32_t const &hash) const override
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

    void
    commit(StateDeltas const &state_deltas, Code const &code_delta) override
    {
        for (auto const &[addr, state_delta] : state_deltas) {

            auto const &account_delta = state_delta.account;
            auto const &storage_deltas = state_delta.storage;
            auto &account_storage = storage[addr];

            // storage
            if (account_delta.second.has_value()) {
                for (auto const &[key, value] : storage_deltas) {
                    auto const it = account_storage.find(key);
                    MONAD_DEBUG_ASSERT(
                        (it == account_storage.end() && is_zero(value.first)) ||
                        (it->second == value.first));
                    if (value.first != value.second) {
                        if (value.second != bytes32_t{}) {
                            account_storage[key] = value.second;
                        }
                        else {
                            auto const n = account_storage.erase(key);
                            MONAD_DEBUG_ASSERT(n == 1);
                        }
                    }
                }
            }

            // account
            if (account_delta.first != account_delta.second) {
                if (account_delta.second.has_value()) {
                    accounts[addr] = account_delta.second.value();
                }
                else {
                    auto const n = accounts.erase(addr);
                    MONAD_DEBUG_ASSERT(n == 1);
                    account_storage.clear();
                }
            }
        }

        for (auto const &[ch, c] : code_delta) {
            code[ch] = c;
        }
    }

    constexpr void
    create_and_prune_block_history(uint64_t /* block_number */) const override
    {
    }
};

MONAD_DB_NAMESPACE_END

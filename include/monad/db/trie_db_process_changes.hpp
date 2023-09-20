#pragma once

#include <monad/config.hpp>
#include <monad/db/trie_db_read_account.hpp>
#include <monad/state/state_changes.hpp>
#include <monad/trie/update.hpp>

#include <ethash/keccak.hpp>
#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

template <typename TAccountTrie, typename TStorageTrie>
void trie_db_process_changes(
    state::StateChanges const &obj, TAccountTrie &account_trie,
    TStorageTrie &storage_trie)
{
    std::unordered_map<address_t, bytes32_t> updated_storage_roots;
    std::vector<trie::Update> storage_trie_updates;
    std::vector<trie::Update> account_trie_updates;

    for (auto const &u : obj.storage_changes) {
        MONAD_DEBUG_ASSERT(!u.second.empty());

        storage_trie.trie.set_trie_prefix(u.first);

        storage_trie_updates.clear();
        std::ranges::transform(
            u.second,
            std::back_inserter(storage_trie_updates),
            [](auto const &su) -> trie::Update {
                auto const &[k, v] = su;
                auto const key = trie::Nibbles{std::bit_cast<bytes32_t>(
                    ethash::keccak256(k.bytes, sizeof(k.bytes)))};
                auto const value = rlp::encode_string(
                    zeroless_view(to_byte_string_view(v.bytes)));
                if (v != bytes32_t{}) {
                    return trie::Upsert{.key = key, .value = value};
                }
                return trie::Delete{.key = key};
            });

        std::ranges::sort(
            storage_trie_updates, std::less<>{}, trie::get_update_key);

        LOG_DEBUG(
            "STORAGE_UPDATES({}) account={} {}",
            storage_trie_updates.size(),
            u.first,
            storage_trie_updates);

        auto const [_, success] = updated_storage_roots.try_emplace(
            u.first, storage_trie.trie.process_updates(storage_trie_updates));
        MONAD_DEBUG_ASSERT(success);
    }

    for (auto const &u : obj.account_changes) {
        auto const &[a, acct] = u;
        storage_trie.trie.set_trie_prefix(a);
        auto const ak = trie::Nibbles{std::bit_cast<bytes32_t>(
            ethash::keccak256(a.bytes, sizeof(a.bytes)))};
        if (acct.has_value()) {
            auto const it = updated_storage_roots.find(a);
            auto const root_hash = it != updated_storage_roots.end()
                                       ? it->second
                                       : storage_trie.trie.root_hash();
            if (it != updated_storage_roots.end()) {
                updated_storage_roots.erase(it);
            }
            account_trie_updates.emplace_back(trie::Upsert{
                .key = ak,
                .value = rlp::encode_account(acct.value(), root_hash)});
        }
        else {
            storage_trie.trie.clear();
            updated_storage_roots.erase(a);
            account_trie_updates.emplace_back(trie::Delete{.key = ak});
        }
    }

    for (auto const &[addr, storage_root] : updated_storage_roots) {
        auto const account = trie_db_read_account(
            addr,
            account_trie.make_leaf_cursor(),
            account_trie.make_trie_cursor());
        MONAD_DEBUG_ASSERT(account.has_value());

        auto const ak = trie::Nibbles{std::bit_cast<bytes32_t>(
            ethash::keccak256(addr.bytes, sizeof(addr.bytes)))};
        account_trie_updates.emplace_back(trie::Upsert{
            .key = ak,
            .value = rlp::encode_account(account.value(), storage_root)});
    }

    if (!account_trie_updates.empty()) {
        std::ranges::sort(
            account_trie_updates, std::less<>{}, trie::get_update_key);
        LOG_DEBUG(
            "ACCOUNT_UPDATES({}) {}",
            account_trie_updates.size(),
            account_trie_updates);

        account_trie.trie.process_updates(account_trie_updates);
    }
    else {
        // there should never be an instance where we have storage
        // updates but no account updates.
        MONAD_DEBUG_ASSERT(obj.storage_changes.empty());
        MONAD_DEBUG_ASSERT(obj.account_changes.empty());
    }
}

template <typename TAccountTrie, typename TStorageTrie>
void trie_db_process_changes(
    StateDeltas const &state_deltas, TAccountTrie &account_trie,
    TStorageTrie &storage_trie)
{
    std::unordered_map<address_t, bytes32_t> updated_storage_roots;
    std::vector<trie::Update> storage_trie_updates;
    std::vector<trie::Update> account_trie_updates;

    for (auto const &[addr, state_delta] : state_deltas) {

        storage_trie.trie.set_trie_prefix(addr);

        auto const &account_delta = state_delta.account;
        auto const &storage_delta = state_delta.storage;

        // process storage updates first
        storage_trie_updates.clear();
        if (account_delta.second.has_value()) {
            for (auto const &[k, v] : storage_delta) {
                if (v.first != v.second) {
                    auto const key = trie::Nibbles{std::bit_cast<bytes32_t>(
                        ethash::keccak256(k.bytes, sizeof(k.bytes)))};
                    auto const value = rlp::encode_string(
                        zeroless_view(to_byte_string_view(v.second.bytes)));
                    if (v.second != bytes32_t{}) {
                        storage_trie_updates.emplace_back(
                            trie::Upsert{.key = key, .value = value});
                    }
                    else {
                        storage_trie_updates.emplace_back(
                            trie::Delete{.key = key});
                    }
                }
            }

            if (!storage_trie_updates.empty()) {
                std::ranges::sort(
                    storage_trie_updates, std::less<>{}, trie::get_update_key);

                LOG_DEBUG(
                    "STORAGE_UPDATES({}) account={} {}",
                    storage_trie_updates.size(),
                    addr,
                    storage_trie_updates);

                auto const [_, success] = updated_storage_roots.try_emplace(
                    addr,
                    storage_trie.trie.process_updates(storage_trie_updates));
                MONAD_DEBUG_ASSERT(success);
            }
        }

        // process account updates after
        auto const account_key = trie::Nibbles{std::bit_cast<bytes32_t>(
            ethash::keccak256(addr.bytes, sizeof(addr.bytes)))};

        if (account_delta.first != account_delta.second) {
            if (account_delta.second.has_value()) {
                auto const it = updated_storage_roots.find(addr);
                auto const root_hash = it != updated_storage_roots.end()
                                           ? it->second
                                           : storage_trie.trie.root_hash();
                if (it != updated_storage_roots.end()) {
                    updated_storage_roots.erase(it);
                }
                account_trie_updates.emplace_back(trie::Upsert{
                    .key = account_key,
                    .value = rlp::encode_account(
                        account_delta.second.value(), root_hash)});
            }
            else {
                storage_trie.trie.clear();
                updated_storage_roots.erase(addr);
                account_trie_updates.emplace_back(
                    trie::Delete{.key = account_key});
            }
        }
    }

    for (auto const &[addr, storage_root] : updated_storage_roots) {
        auto const account = trie_db_read_account(
            addr,
            account_trie.make_leaf_cursor(),
            account_trie.make_trie_cursor());
        MONAD_DEBUG_ASSERT(account.has_value());

        auto const ak = trie::Nibbles{std::bit_cast<bytes32_t>(
            ethash::keccak256(addr.bytes, sizeof(addr.bytes)))};
        account_trie_updates.emplace_back(trie::Upsert{
            .key = ak,
            .value = rlp::encode_account(account.value(), storage_root)});
    }

    if (!account_trie_updates.empty()) {
        std::ranges::sort(
            account_trie_updates, std::less<>{}, trie::get_update_key);
        LOG_DEBUG(
            "ACCOUNT_UPDATES({}) {}",
            account_trie_updates.size(),
            account_trie_updates);

        account_trie.trie.process_updates(account_trie_updates);
    }
    else {
        MONAD_DEBUG_ASSERT(storage_trie_updates.empty());
    }
}

MONAD_NAMESPACE_END

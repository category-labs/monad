#pragma once

#include <monad/core/likely.h>
#include <monad/db/config.hpp>
#include <monad/db/db_interface.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/logging/monad_log.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/rlp/encode_helpers.hpp>
#include <monad/trie/get_trie_key_of_leaf.hpp>
#include <monad/trie/node.hpp>
#include <monad/trie/update.hpp>

#include <filesystem>
#include <optional>
#include <utility>

MONAD_DB_NAMESPACE_BEGIN

template <typename TTrieDBImpl>
struct TrieDBInterface
    : public DBInterface<
          TrieDBInterface<TTrieDBImpl>, monad::execution::BoostFiberExecution>
{
    using DBInterface<
        TrieDBInterface<TTrieDBImpl>,
        monad::execution::BoostFiberExecution>::updates;

    std::vector<trie::Update> account_trie_updates;
    std::vector<trie::Update> storage_trie_updates;

    decltype(monad::log::logger_t::get_logger()) logger =
        monad::log::logger_t::get_logger("trie_db_logger");
    static_assert(std::is_pointer_v<decltype(logger)>);

    ////////////////////////////////////////////////////////////////////
    // Interface functions
    ////////////////////////////////////////////////////////////////////

    TTrieDBImpl &self() { return static_cast<TTrieDBImpl &>(*this); }
    TTrieDBImpl const &self() const
    {
        return static_cast<TTrieDBImpl const &>(*this);
    }

    auto &accounts() { return self().accounts(); }
    auto &storage() { return self().storage(); }
    auto const &accounts() const { return self().accounts(); }
    auto const &storage() const { return self().storage(); }
    void take_snapshot() { return self().take_snapshot(); }

    ////////////////////////////////////////////////////////////////////
    // DBInterface accessor implementations
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] constexpr bool contains(address_t const &a) const
    {
        return find(a).has_value();
    }

    [[nodiscard]] constexpr bool
    contains(address_t const &a, bytes32_t const &k) const
    {
        return find(a, k).has_value();
    }

    [[nodiscard]] std::optional<Account> try_find(address_t const &a) const
    {
        auto const c = find(a);
        if (!c.has_value()) {
            return std::nullopt;
        }

        auto const key =
            c->key().transform(&decltype(c)::value_type::Key::path);
        MONAD_ASSERT(key.has_value());

        auto const value = c->value();
        MONAD_ASSERT(value.has_value());

        auto const node = trie::deserialize_node(*key, *value);
        MONAD_ASSERT(std::holds_alternative<trie::Leaf>(node));

        Account ret;
        bytes32_t _;
        auto const rest =
            rlp::decode_account(ret, _, std::get<trie::Leaf>(node).value);
        MONAD_ASSERT(rest.empty());
        return ret;
    }

    [[nodiscard]] std::optional<bytes32_t>
    try_find(address_t const &a, bytes32_t const &k) const
    {
        auto const c = find(a, k);
        if (!c.has_value()) {
            return std::nullopt;
        }

        auto const key =
            c->key().transform(&decltype(c)::value_type::Key::path);
        MONAD_ASSERT(key.has_value());

        auto const value = c->value();
        MONAD_ASSERT(c.has_value());

        auto const node = trie::deserialize_node(*key, *value);
        MONAD_ASSERT(std::holds_alternative<trie::Leaf>(node));

        byte_string zeroless;
        auto const rest =
            rlp::decode_string(zeroless, std::get<trie::Leaf>(node).value);
        MONAD_ASSERT(rest.empty());
        MONAD_ASSERT(zeroless.size() <= sizeof(bytes32_t));

        bytes32_t ret;
        std::copy_n(
            zeroless.data(),
            zeroless.size(),
            std::next(
                std::begin(ret.bytes),
                static_cast<uint8_t>(sizeof(bytes32_t) - zeroless.size())));
        MONAD_ASSERT(ret != bytes32_t{});
        return ret;
    }

    ////////////////////////////////////////////////////////////////////
    // Additional accessors
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] constexpr bytes32_t root_hash() const
    {
        return accounts().trie.root_hash();
    }

    [[nodiscard]] constexpr bytes32_t root_hash(address_t a)
    {
        storage().trie.set_trie_prefix(a);
        return storage().trie.root_hash();
    }

    ////////////////////////////////////////////////////////////////////
    // DBInterface modifiers
    ////////////////////////////////////////////////////////////////////

    void commit_storage_impl()
    {
        if (updates.storage.empty()) {
            return;
        }

        for (auto const &u : updates.storage) {
            MONAD_DEBUG_ASSERT(!u.second.empty());

            storage().trie.set_trie_prefix(u.first);

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

            MONAD_LOG_INFO(
                logger,
                "{} storage updates for {}: {}",
                storage_trie_updates.size(),
                u.first,
                storage_trie_updates);
            storage().trie.process_updates(storage_trie_updates);
        }
        storage().leaves_writer.write();
        storage().trie_writer.write();
        take_snapshot();
    }

    void commit_accounts_impl()
    {
        MONAD_DEBUG_ASSERT(updates.storage.empty());

        if (updates.accounts.empty()) {
            return;
        }

        for (auto const &u : updates.accounts) {
            auto const &[a, acct] = u;
            storage().trie.set_trie_prefix(a);
            auto const ak = trie::Nibbles{std::bit_cast<bytes32_t>(
                ethash::keccak256(a.bytes, sizeof(a.bytes)))};
            if (acct.has_value()) {
                account_trie_updates.emplace_back(trie::Upsert{
                    .key = ak,
                    .value = rlp::encode_account(
                        acct.value(), storage().trie.root_hash())});
            }
            else {
                storage().trie.clear();
                account_trie_updates.emplace_back(trie::Delete{.key = ak});
            }
        }

        std::ranges::sort(
            account_trie_updates, std::less<>{}, trie::get_update_key);
        MONAD_LOG_INFO(
            logger,
            "{} account updates: {}",
            account_trie_updates.size(),
            account_trie_updates);
        accounts().trie.process_updates(account_trie_updates);

        accounts().leaves_writer.write();
        accounts().trie_writer.write();
        storage().leaves_writer.write();
        storage().trie_writer.write();
        take_snapshot();
        account_trie_updates.clear();
    }

    ////////////////////////////////////////////////////////////////////
    // Helper functions
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] constexpr auto find(address_t const &a) const
    {
        // TODO: make this return the keccak so that it can be just passed in
        // to avoid double keccaking?
        auto lc = accounts().make_leaf_cursor();

        std::optional<std::decay_t<decltype(accounts().make_trie_cursor())>>
            ret{};
        if (MONAD_UNLIKELY(lc.empty())) {
            MONAD_DEBUG_ASSERT(ret == std::nullopt);
            return ret;
        }

        auto const [key, exists] = get_trie_key_of_leaf(
            trie::Nibbles{std::bit_cast<bytes32_t>(
                ethash::keccak256(a.bytes, sizeof(a.bytes)))},
            lc);

        if (exists) {
            ret.emplace(accounts().make_trie_cursor());
            ret->lower_bound(key);
        }
        return ret;
    }

    [[nodiscard]] constexpr auto
    find(address_t const &a, bytes32_t const &k) const
    {
        auto lc = storage().make_leaf_cursor();

        lc.set_prefix(a);

        std::optional<std::decay_t<decltype(storage().make_trie_cursor())>>
            ret{};
        if (MONAD_UNLIKELY(lc.empty())) {
            MONAD_DEBUG_ASSERT(ret == std::nullopt);
            return ret;
        }

        auto const [key, exists] = get_trie_key_of_leaf(
            trie::Nibbles{std::bit_cast<bytes32_t>(
                ethash::keccak256(k.bytes, sizeof(k.bytes)))},
            lc);

        if (exists) {
            ret.emplace(storage().make_trie_cursor());
            ret->set_prefix(a);
            ret->lower_bound(key);
        }
        return ret;
    }
};

MONAD_DB_NAMESPACE_END

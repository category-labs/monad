#pragma once

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/db/config.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/trie/in_memory_comparator.hpp>
#include <monad/trie/in_memory_cursor.hpp>
#include <monad/trie/in_memory_writer.hpp>
#include <monad/trie/key_buffer.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/node.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/trie.hpp>

#include <ethash/keccak.hpp>

#include <bits/ranges_algo.h>
#include <unordered_map>

MONAD_DB_NAMESPACE_BEGIN

namespace impl
{
    template <typename TDBImpl, typename TExecution>
    struct DBInterface
    {
        struct Updates
        {
            std::unordered_map<address_t, std::optional<Account>> accounts;
            std::unordered_map<
                address_t, std::unordered_map<bytes32_t, bytes32_t>>
                storage;
        } updates{};

        decltype(TExecution::get_executor()) executor{
            TExecution::get_executor()};

        TDBImpl &self() { return static_cast<TDBImpl &>(*this); }
        TDBImpl const &self() const
        {
            return static_cast<TDBImpl const &>(*this);
        }

        [[nodiscard]] std::optional<Account> try_find(address_t const &a) const
        {
            return self().try_find(a);
        }

        [[nodiscard]] std::optional<Account> query(address_t const &a) const
        {
            return executor([=, this]() { return try_find(a); });
        }

        [[nodiscard]] constexpr bool contains(address_t const &a) const
        {
            return self().contains(a);
        }

        [[nodiscard]] constexpr bool
        contains(address_t const &a, bytes32_t const &k) const
        {
            return self().contains(a, k);
        }

        [[nodiscard]] Account at(address_t const &a) const
        {
            auto const ret = try_find(a);
            MONAD_ASSERT(ret);
            return ret.value();
        }

        [[nodiscard]] std::optional<bytes32_t>
        query(address_t const &a, bytes32_t const &k) const
        {
            return executor([=, this]() { return try_find(a, k); });
        }

        [[nodiscard]] std::optional<bytes32_t>
        try_find(address_t const &a, bytes32_t const &k) const
        {
            return self().try_find(a, k);
        }

        [[nodiscard]] bytes32_t at(address_t const &a, bytes32_t const &k) const
        {
            auto const ret = try_find(a, k);
            MONAD_ASSERT(ret);
            return ret.value();
        }

        void create(address_t const &a, Account const &acct)
        {
            MONAD_DEBUG_ASSERT(!contains(a));
            auto const [_, inserted] = updates.accounts.try_emplace(a, acct);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void create(address_t const &a, bytes32_t const &k, bytes32_t const &v)
        {
            MONAD_DEBUG_ASSERT(v != bytes32_t{});
            MONAD_DEBUG_ASSERT(!contains(a, k));
            auto const [_, inserted] = updates.storage[a].try_emplace(k, v);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void update(address_t const &a, Account const &acct)
        {
            MONAD_DEBUG_ASSERT(contains(a));
            auto const [_, inserted] = updates.accounts.try_emplace(a, acct);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void update(address_t const &a, bytes32_t const &k, bytes32_t const &v)
        {
            MONAD_DEBUG_ASSERT(v != bytes32_t{});
            MONAD_DEBUG_ASSERT(contains(a));
            MONAD_DEBUG_ASSERT(contains(a, k));
            auto const [_, inserted] = updates.storage[a].try_emplace(k, v);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void erase(address_t const &a)
        {
            MONAD_DEBUG_ASSERT(contains(a));
            auto const [_, inserted] =
                updates.accounts.try_emplace(a, std::nullopt);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void erase(address_t const &a, bytes32_t const &k)
        {
            MONAD_DEBUG_ASSERT(contains(a));
            MONAD_DEBUG_ASSERT(contains(a, k));
            auto const [_, inserted] =
                updates.storage[a].try_emplace(k, bytes32_t{});
            MONAD_DEBUG_ASSERT(inserted);
        }

        void commit_storage_impl() { self().commit_storage_impl(); }

        void commit_storage()
        {
            commit_storage_impl();
            updates.storage.clear();
        }

        void commit_accounts_impl() { self().commit_accounts_impl(); }

        void commit_accounts()
        {
            commit_accounts_impl();
            updates.accounts.clear();
        }

        void commit()
        {
            commit_storage();
            commit_accounts();
        }
    };

    template <typename TExecution>
    struct InMemoryDBImpl
        : public DBInterface<InMemoryDBImpl<TExecution>, TExecution>
    {
        using DBInterface<InMemoryDBImpl<TExecution>, TExecution>::updates;

        std::unordered_map<address_t, Account> accounts;
        std::unordered_map<address_t, std::unordered_map<bytes32_t, bytes32_t>>
            storage;

        [[nodiscard]] bool contains(address_t const &a) const
        {
            return accounts.contains(a);
        }

        [[nodiscard]] bool
        contains(address_t const &a, bytes32_t const &k) const
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

        void commit_storage_impl()
        {
            for (auto const &[a, updates] : updates.storage) {
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
        }

        void commit_accounts_impl()
        {
            for (auto const &[a, acct] : updates.accounts) {
                if (acct.has_value()) {
                    accounts[a] = acct.value();
                }
                else {
                    auto const n = accounts.erase(a);
                    MONAD_DEBUG_ASSERT(n == 1);
                }
            }
        }
    };

    template <
        typename TAccountsCursor, typename TStorageCursor,
        typename TAccountsWriter, typename TStorageWriter, typename TExecutor>
    struct TrieDBImpl
        : public DBInterface<
              TrieDBImpl<
                  TAccountsCursor, TStorageCursor, TAccountsWriter,
                  TStorageWriter, TExecutor>,
              TExecutor>
    {
        using DBInterface<
            TrieDBImpl<
                TAccountsCursor, TStorageCursor, TAccountsWriter,
                TStorageWriter, TExecutor>,
            TExecutor>::updates;

        template <typename TCursor, typename TWriter>
        struct Trie
        {
            using storage_t = typename TCursor::storage_t;
            storage_t leaves_storage;
            TCursor leaves_cursor;
            TWriter leaves_writer;
            storage_t trie_storage;
            TCursor trie_cursor;
            TWriter trie_writer;
            trie::Trie<TCursor, TWriter> trie;

            Trie()
                : leaves_storage{}
                , leaves_cursor{leaves_storage}
                , leaves_writer{leaves_storage}
                , trie_storage{}
                , trie_cursor{trie_storage}
                , trie_writer{trie_storage}
                , trie{leaves_cursor, trie_cursor, leaves_writer, trie_writer}
            {
            }
        };

        Trie<TAccountsCursor, TAccountsWriter> accounts{};
        Trie<TStorageCursor, TStorageWriter> storage{};
        std::vector<trie::Update> account_trie_updates{};
        std::vector<trie::Update> storage_trie_updates{};

        [[nodiscard]] constexpr bytes32_t root_hash() const
        {
            return accounts.trie.root_hash();
        }

        [[nodiscard]] constexpr bytes32_t root_hash(address_t a)
        {
            storage.trie.set_trie_prefix(a);
            return storage.trie.root_hash();
        }

        template <typename TCursor>
        [[nodiscard]] constexpr bool
        move(trie::Nibbles const &lk, TCursor &lc, TCursor &tc) const
        {
            lc.lower_bound(lk);

            if (lc.key().transform(&TCursor::Key::path) != lk) {
                return false;
            }

            lc.prev();

            using namespace std::placeholders;

            auto const left =
                lc.key()
                    .transform(&TCursor::Key::path)
                    .transform([&](auto const &l) {
                        return trie::longest_common_prefix_size(l, lk);
                    });

            lc.next();
            MONAD_DEBUG_ASSERT(lc.key().transform(&TCursor::Key::path) == lk);
            lc.next();

            auto const right =
                lc.key()
                    .transform(&TCursor::Key::path)
                    .transform([&](auto const &r) {
                        return trie::longest_common_prefix_size(lk, r);
                    });

            auto const tk =
                !left.has_value() && !right.has_value()
                    ? trie::Nibbles{}
                    : trie::Nibbles{lk.prefix(static_cast<uint8_t>(
                          std::max(left.value_or(0), right.value_or(0)) + 1))};

            tc.lower_bound(tk);
            return tc.key().transform(&TCursor::Key::path) == tk;
        }

        // TODO: make this return the keccak so that it can be just passed in
        // to avoid double keccaking?
        [[nodiscard]] constexpr tl::optional<TAccountsCursor>
        find(address_t const &a) const
        {
            auto lc = TAccountsCursor{accounts.leaves_storage};
            auto tc = TAccountsCursor{accounts.trie_storage};
            auto const found = move(
                trie::Nibbles{std::bit_cast<bytes32_t>(
                    ethash::keccak256(a.bytes, sizeof(a.bytes)))},
                lc,
                tc);

            if (found) {
                return tc;
            }
            return tl::nullopt;
        }

        [[nodiscard]] constexpr tl::optional<TStorageCursor>
        find(address_t const &a, bytes32_t const &k) const
        {
            auto lc = TStorageCursor{storage.leaves_storage};
            auto tc = TStorageCursor{storage.trie_storage};

            lc.set_prefix(a);
            tc.set_prefix(a);

            auto const found = move(
                trie::Nibbles{std::bit_cast<bytes32_t>(
                    ethash::keccak256(k.bytes, sizeof(k.bytes)))},
                lc,
                tc);

            if (found) {
                return tc;
            }
            return tl::nullopt;
        }

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

        void commit_storage_impl()
        {
            if (updates.storage.empty()) {
                return;
            }

            for (auto const &u : updates.storage) {
                MONAD_DEBUG_ASSERT(!u.second.empty());

                storage.trie.set_trie_prefix(u.first);

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
                storage.trie.process_updates(storage_trie_updates);
            }
            storage.leaves_writer.write();
            storage.trie_writer.write();
            storage.trie.take_snapshot();
        }

        void commit_accounts_impl()
        {
            MONAD_DEBUG_ASSERT(updates.storage.empty());

            if (updates.accounts.empty()) {
                return;
            }

            for (auto const &u : updates.accounts) {
                auto const &[a, acct] = u;
                storage.trie.set_trie_prefix(a);
                auto const ak = trie::Nibbles{std::bit_cast<bytes32_t>(
                    ethash::keccak256(a.bytes, sizeof(a.bytes)))};
                if (acct.has_value()) {
                    account_trie_updates.emplace_back(trie::Upsert{
                        .key = ak,
                        .value = rlp::encode_account(
                            acct.value(), storage.trie.root_hash())});
                }
                else {
                    storage.trie.clear();
                    account_trie_updates.emplace_back(trie::Delete{.key = ak});
                }
            }

            std::ranges::sort(
                account_trie_updates, std::less<>{}, trie::get_update_key);
            accounts.trie.process_updates(account_trie_updates);

            accounts.leaves_writer.write();
            accounts.trie_writer.write();
            storage.leaves_writer.write();
            storage.trie_writer.write();
            accounts.trie.take_snapshot();
            storage.trie.take_snapshot();
            account_trie_updates.clear();
        }
    };
}

// Database impl with trie root generating logic, backed by stl
using InMemoryTrieDB = impl::TrieDBImpl<
    trie::InMemoryCursor<trie::InMemoryPathComparator>,
    trie::InMemoryCursor<trie::InMemoryPrefixPathComparator>,
    trie::InMemoryWriter<trie::InMemoryPathComparator>,
    trie::InMemoryWriter<trie::InMemoryPrefixPathComparator>,
    monad::execution::BoostFiberExecution>;

// Database impl without trie root generating logic, backed by stl
using InMemoryDB = impl::InMemoryDBImpl<monad::execution::BoostFiberExecution>;

MONAD_DB_NAMESPACE_END

#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>

MONAD_DB_NAMESPACE_BEGIN

template <typename TDBImpl, typename TExecution>
struct DBInterface
{
    struct Updates
    {
        std::unordered_map<address_t, std::optional<Account>> accounts;
        std::unordered_map<address_t, std::unordered_map<bytes32_t, bytes32_t>>
            storage;
    } updates{};

    decltype(TExecution::get_executor()) executor{TExecution::get_executor()};

    TDBImpl &self() { return static_cast<TDBImpl &>(*this); }
    TDBImpl const &self() const { return static_cast<TDBImpl const &>(*this); }

    ////////////////////////////////////////////////////////////////////
    // Accessors
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] std::optional<Account> try_find(address_t const &a)
    {
        return self().try_find(a);
    }

    [[nodiscard]] std::optional<Account> query(address_t const &a)
    {
        return executor([=, this]() { return try_find(a); });
    }

    [[nodiscard]] constexpr bool contains(address_t const &a)
    {
        return self().contains(a);
    }

    [[nodiscard]] constexpr bool
    contains(address_t const &a, bytes32_t const &k)
    {
        return self().contains(a, k);
    }

    [[nodiscard]] Account at(address_t const &a)
    {
        auto const ret = try_find(a);
        MONAD_ASSERT(ret);
        return ret.value();
    }

    [[nodiscard]] std::optional<bytes32_t>
    query(address_t const &a, bytes32_t const &k)
    {
        return executor([=, this]() { return try_find(a, k); });
    }

    [[nodiscard]] std::optional<bytes32_t>
    try_find(address_t const &a, bytes32_t const &k)
    {
        return self().try_find(a, k);
    }

    [[nodiscard]] bytes32_t at(address_t const &a, bytes32_t const &k)
    {
        auto const ret = try_find(a, k);
        MONAD_ASSERT(ret);
        return ret.value();
    }

    ////////////////////////////////////////////////////////////////////
    // modifiers
    ////////////////////////////////////////////////////////////////////

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

    void commit_accounts_impl() { self().commit_accounts_impl(); }

    void commit_storage()
    {
        commit_storage_impl();
        updates.storage.clear();
    }

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

MONAD_DB_NAMESPACE_END

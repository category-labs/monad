#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/state/concepts.hpp>

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

    [[nodiscard]] constexpr TDBImpl &self() noexcept
    {
        return static_cast<TDBImpl &>(*this);
    }
    [[nodiscard]] constexpr TDBImpl const &self() const noexcept
    {
        return static_cast<TDBImpl const &>(*this);
    }

    ////////////////////////////////////////////////////////////////////
    // Accessors
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] constexpr std::optional<Account> try_find(address_t const &a)
    {
        return self().try_find(a);
    }

    [[nodiscard]] constexpr std::optional<Account> query(address_t const &a)
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

    [[nodiscard]] constexpr Account at(address_t const &a)
    {
        auto const ret = try_find(a);
        MONAD_ASSERT(ret);
        return ret.value();
    }

    [[nodiscard]] constexpr std::optional<bytes32_t>
    query(address_t const &a, bytes32_t const &k)
    {
        return executor([=, this]() { return try_find(a, k); });
    }

    [[nodiscard]] constexpr std::optional<bytes32_t>
    try_find(address_t const &a, bytes32_t const &k)
    {
        return self().try_find(a, k);
    }

    [[nodiscard]] constexpr bytes32_t at(address_t const &a, bytes32_t const &k)
    {
        auto const ret = try_find(a, k);
        MONAD_ASSERT(ret);
        return ret.value();
    }

    ////////////////////////////////////////////////////////////////////
    // modifiers
    ////////////////////////////////////////////////////////////////////

    constexpr void commit(state::changeset auto const &obj)
    {
        self().commit(obj);
    }
};

MONAD_DB_NAMESPACE_END

#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/state/concepts.hpp>

MONAD_DB_NAMESPACE_BEGIN

template <typename TDBImpl, typename TExecutor>
struct DBInterface
{
    struct Updates
    {
        std::unordered_map<address_t, std::optional<Account>> accounts;
        std::unordered_map<address_t, std::unordered_map<bytes32_t, bytes32_t>>
            storage;
    } updates{};

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
        return TExecutor::execute(
            [=, this]() { return self().try_find_impl(a); });
    }

    [[nodiscard]] constexpr bool contains(address_t const &a)
    {
        return TExecutor::execute(
            [=, this]() { return self().contains_impl(a); });
    }

    [[nodiscard]] constexpr Account at(address_t const &a)
    {
        auto const ret = try_find(a);
        MONAD_ASSERT(ret);
        return ret.value();
    }

    [[nodiscard]] constexpr bytes32_t
    try_find(address_t const &a, bytes32_t const &k)
    {
        return TExecutor::execute(
            [=, this]() { return self().try_find_impl(a, k); });
    }

    [[nodiscard]] constexpr bool
    contains(address_t const &a, bytes32_t const &k)
    {
        return TExecutor::execute(
            [=, this]() { return self().contains_impl(a, k); });
    }

    [[nodiscard]] constexpr bytes32_t at(address_t const &a, bytes32_t const &k)
    {
        auto const ret = try_find(a, k);
        MONAD_ASSERT(ret != bytes32_t{});
        return ret;
    }

    ////////////////////////////////////////////////////////////////////
    // modifiers
    ////////////////////////////////////////////////////////////////////

    constexpr void commit(state::changeset auto const &obj)
    {
        self().commit(obj);
    }

    constexpr void create_and_prune_block_history(uint64_t block_number) const
    {
        self().create_and_prune_block_history(block_number);
    }
};

MONAD_DB_NAMESPACE_END

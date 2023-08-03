#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/concepts.hpp>
#include <monad/db/config.hpp>
#include <monad/state/concepts.hpp>

MONAD_DB_NAMESPACE_BEGIN

template <typename TDBImpl, typename TExecutor, Permission TPermission>
struct DBInterface
{
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

    // Account
    [[nodiscard]] constexpr std::optional<Account> try_find(address_t const &a)
        requires Readable<TPermission>
    {
        return TExecutor::execute(
            [=, this]() { return self().try_find_impl(a); });
    }

    [[nodiscard]] constexpr bool contains(address_t const &a)
        requires Readable<TPermission>
    {
        return TExecutor::execute(
            [=, this]() { return self().contains_impl(a); });
    }

    [[nodiscard]] constexpr Account at(address_t const &a)
        requires Readable<TPermission>
    {
        auto const ret = try_find(a);
        MONAD_ASSERT(ret);
        return ret.value();
    }

    // Storage
    [[nodiscard]] constexpr bytes32_t
    try_find(address_t const &a, bytes32_t const &k)
        requires Readable<TPermission>
    {
        return TExecutor::execute(
            [=, this]() { return self().try_find_impl(a, k); });
    }

    [[nodiscard]] constexpr bool
    contains(address_t const &a, bytes32_t const &k)
        requires Readable<TPermission>
    {
        return TExecutor::execute(
            [=, this]() { return self().contains_impl(a, k); });
    }

    [[nodiscard]] constexpr bytes32_t at(address_t const &a, bytes32_t const &k)
        requires Readable<TPermission>
    {
        auto const ret = try_find(a, k);
        MONAD_ASSERT(ret != bytes32_t{});
        return ret;
    }

    // Code
    [[nodiscard]] constexpr byte_string try_find(bytes32_t const &ch)
        requires Readable<TPermission>
    {
        return TExecutor::execute(
            [=, this]() { return self().try_find_impl(ch); });
    }

    [[nodiscard]] constexpr bool contains(bytes32_t const &ch)
        requires Readable<TPermission>
    {
        return TExecutor::execute(
            [=, this]() { return self().contains_impl(ch); });
    }

    [[nodiscard]] constexpr byte_string at(bytes32_t const &ch)
        requires Readable<TPermission>
    {
        auto const ret = try_find(ch);
        MONAD_ASSERT(ret != byte_string{});
        return ret;
    }

    ////////////////////////////////////////////////////////////////////
    // modifiers
    ////////////////////////////////////////////////////////////////////

    constexpr void commit(state::changeset auto const &obj)
        requires Writable<TPermission>
    {
        self().commit(obj);
    }

    constexpr void create_and_prune_block_history(uint64_t block_number) const
        requires Writable<TPermission>
    {
        self().create_and_prune_block_history(block_number);
    }
};

MONAD_DB_NAMESPACE_END

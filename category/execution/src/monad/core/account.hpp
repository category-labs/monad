#pragma once

#include <category/core/config.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <monad/types/incarnation.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct Account
{
    uint256_t balance{0}; // sigma[a]_b
    bytes32_t code_hash{NULL_HASH}; // sigma[a]_c
    uint64_t nonce{0}; // sigma[a]_n
    Incarnation incarnation{0, 0};

    friend bool operator==(Account const &, Account const &) = default;
};

static_assert(sizeof(Account) == 80);
static_assert(alignof(Account) == 8);

static_assert(sizeof(std::optional<Account>) == 88);
static_assert(alignof(std::optional<Account>) == 8);

// YP (14)
inline constexpr bool is_empty(Account const &account)
{
    return account.code_hash == NULL_HASH && account.nonce == 0 &&
           account.balance == 0;
}

// YP (15)
inline constexpr bool is_dead(std::optional<Account> const &account)
{
    return !account.has_value() || is_empty(account.value());
}

MONAD_NAMESPACE_END

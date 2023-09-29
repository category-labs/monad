#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

#include <cstdint>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

struct Account
{
    uint256_t balance{0};
    bytes32_t code_hash{NULL_HASH};
    uint64_t nonce{0};
    uint64_t incarnation{1};

    friend bool operator==(Account const &, Account const &) = default;
};

static_assert(sizeof(Account) == 80);
static_assert(alignof(Account) == 8);

constexpr bool is_dead(Account const &account)
{
    return account.balance == 0 && account.code_hash == NULL_HASH &&
           account.nonce == 0;
}

MONAD_NAMESPACE_END

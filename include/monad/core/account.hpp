#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

struct Account
{
    uint256_t balance{0};
    bytes32_t code_hash{NULL_HASH};
    uint64_t nonce{0};

    friend bool operator==(Account const &lhs, Account const &rhs) = default;
};

static_assert(sizeof(Account) == 72);
static_assert(alignof(Account) == 8);


MONAD_NAMESPACE_END

#pragma once

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>

MONAD_NAMESPACE_BEGIN

// EIP-4895
struct Withdrawal
{
    uint64_t index{0};
    uint64_t validator_index{};
    uint64_t amount{};
    Address recipient{};

    friend bool operator==(Withdrawal const &, Withdrawal const &) = default;
};

static_assert(sizeof(Withdrawal) == 48);
static_assert(alignof(Withdrawal) == 8);

MONAD_NAMESPACE_END

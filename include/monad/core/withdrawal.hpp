#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>

MONAD_NAMESPACE_BEGIN

// TODO: Potential Optimization for padding??
// EIP-4895
struct Withdrawal
{
    uint64_t index{0};
    uint64_t validator_index{};
    address_t recipient{};
    uint64_t amount{}; // this should never be 0
};

static_assert(sizeof(Withdrawal) == 48);
static_assert(alignof(Withdrawal) == 8);

MONAD_NAMESPACE_END

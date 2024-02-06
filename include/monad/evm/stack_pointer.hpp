#pragma once

#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>

MONAD_EVM_NAMESPACE_BEGIN

class StackPointer
{
    uint256_t *ptr_;

public:
    explicit StackPointer(uint256_t *) noexcept;

    uint256_t const &pop() noexcept;
    void push(uint256_t const &) noexcept;
    uint256_t &at(size_t) noexcept;
};

static_assert(sizeof(StackPointer) == 8);
static_assert(alignof(StackPointer) == 8);

MONAD_EVM_NAMESPACE_END

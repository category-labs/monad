#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class BlockHash
{
public:
    static constexpr unsigned N = 256;

    virtual bytes32_t get(uint64_t) const = 0;
    virtual ~BlockHash() = default;
};

MONAD_NAMESPACE_END
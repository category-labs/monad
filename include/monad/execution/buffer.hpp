#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class Buffer
{
    static constexpr unsigned block_hash_buffer_size = 256;
    bytes32_t block_hash_buffer_[block_hash_buffer_size];
    uint64_t current_block_number_;

public:
    Buffer();

    void set_block_hash(uint64_t const block_number, bytes32_t const &hash)
    {
        MONAD_DEBUG_ASSERT(
            !current_block_number_ || block_number == current_block_number_);
        block_hash_buffer_[current_block_number_ % block_hash_buffer_size] =
            hash;
        current_block_number_ = block_number + 1;
    }

    bytes32_t const &get_block_hash(uint64_t const block_number) const
    {
        MONAD_DEBUG_ASSERT(
            block_number < current_block_number_ &&
            block_number + block_hash_buffer_size >= current_block_number_);
        return block_hash_buffer_[block_number % block_hash_buffer_size];
    }
};

MONAD_NAMESPACE_END

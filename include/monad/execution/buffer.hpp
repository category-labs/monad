#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

class Buffer
{
    static constexpr unsigned block_hash_buffer_size = 256;
    bytes32_t block_hash_buffer_[block_hash_buffer_size];
    uint64_t last_block_number_;

    BlockHeader parent_header_;
    bytes32_t parent_hash_;

public:
    Buffer();

    void set_block_hash(uint64_t const block_number, bytes32_t const &hash)
    {
        MONAD_DEBUG_ASSERT(
            !last_block_number_ || block_number == last_block_number_);
        block_hash_buffer_[last_block_number_ % block_hash_buffer_size] = hash;
        last_block_number_ = block_number;
    }

    bytes32_t const &get_block_hash(uint64_t const block_number) const
    {
        MONAD_DEBUG_ASSERT(
            block_number <= last_block_number_ &&
            block_number + block_hash_buffer_size >= last_block_number_ + 1);
        return block_hash_buffer_[block_number % block_hash_buffer_size];
    }

    void set_parent_header(BlockHeader const &parent_header);

    std::optional<BlockHeader> const
    get_parent_header(bytes32_t const &parent_hash) const
    {
        if (MONAD_UNLIKELY(parent_hash != parent_hash_)) {
            return std::nullopt;
        }

        return parent_header_;
    }

    void to_next_block()
    {
        last_block_number_++;
    }
};

MONAD_NAMESPACE_END

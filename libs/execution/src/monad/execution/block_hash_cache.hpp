#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_hash_function.hpp>

#include <cstdint>
#include <map>

MONAD_NAMESPACE_BEGIN

class BlockHashCache
{
    static constexpr unsigned N = 256;

    std::map<uint64_t, bytes32_t> cache_{};

public:
    BlockHashCache() = default;

    bytes32_t
    get(uint64_t const block_number,
        BlockHashFunction const &block_hash_function)
    {
        auto it = cache_.find(block_number);
        if (MONAD_UNLIKELY(it == cache_.end()) {
            it = cache_
                     .try_emplace(
                         block_number, block_hash_function(block_number))
                     .second;
            uint64_t const min_block_number =
                block_number >= N ? (block_number - N) : 0;
            cache_.remove(cache_.begin(), cache_.lower_bound(min_block_number));
        }
        return it->second;
    }
};

MONAD_NAMESPACE_END

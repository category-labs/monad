#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/buffer.hpp>

MONAD_NAMESPACE_BEGIN

Buffer::Buffer()
    : block_hash_buffer_{}
    , current_block_number_{0}
{
    for (auto &hash : block_hash_buffer_) {
        hash = NULL_HASH;
    }
}

MONAD_NAMESPACE_END

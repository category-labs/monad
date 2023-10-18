#include <monad/execution/block_hash_buffer.hpp>

MONAD_NAMESPACE_BEGIN

BlockHashBuffer::BlockHashBuffer()
    : b_{}
    , n_{0}
{
    for (auto &h : b_) {
        h = NULL_HASH;
    }
}

MONAD_NAMESPACE_END

#include <monad/config.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/mpt/db.hpp>

#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

BlockHashBuffer::BlockHashBuffer()
    : b_{}
    , n_{0}
{
    for (auto &h : b_) {
        h = NULL_HASH;
    }
}

bytes32_t BlockHashBuffer::get(uint64_t const n) const
{
    MONAD_ASSERT(n < n_ && n + N >= n_);
    return b_[n % N];
}

void BlockHashBuffer::set(uint64_t const n, bytes32_t const &h)
{
    MONAD_ASSERT(!n_ || n == n_);
    b_[n % N] = h;
    n_ = n + 1;
}

bool init_block_hash_buffer_from_triedb(
    mpt::Db &rodb, uint64_t const block_number,
    BlockHashBuffer &block_hash_buffer)
{
    for (uint64_t b = block_number < 256 ? 0 : block_number - 256;
         b < block_number;
         ++b) {
        auto const header = rodb.get(
            mpt::concat(
                FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
            b);
        if (!header.has_value()) {
            LOG_WARNING(
                "Could not query block header {} from TrieDb -- {}",
                b,
                header.error().message().c_str());
            return false;
        }
        auto const h = to_bytes(keccak256(header.value()));
        block_hash_buffer.set(b, h);
    }

    return true;
}

MONAD_NAMESPACE_END

#include <monad/config.hpp>
#include <monad/core/block_rlp.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/buffer.hpp>

#include <ethash/keccak.hpp>

#include <bit>

MONAD_NAMESPACE_BEGIN

Buffer::Buffer()
    : block_hash_buffer_{}
    , last_block_number_{0}
    , parent_header_{}
    , parent_hash_{}
{
    for (auto &hash : block_hash_buffer_) {
        hash = NULL_HASH;
    }
}

void Buffer::set_parent_header(BlockHeader const &parent_header)
{
    parent_header_ = parent_header;
    auto const encoded_header = rlp::encode_block_header(parent_header);
    parent_hash_ = std::bit_cast<bytes32_t>(
        ethash::keccak256(encoded_header.data(), encoded_header.length()));
}

MONAD_NAMESPACE_END

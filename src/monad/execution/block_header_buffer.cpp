#include <monad/core/block_rlp.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_header_buffer.hpp>

#include <ethash/keccak.hpp>

#include <bit>
#include <optional>

MONAD_NAMESPACE_BEGIN

void BlockHeaderBuffer::set_parent_header(BlockHeader const &parent_header)
{
    parent_header_ = parent_header;
    auto const encoded_header = rlp::encode_block_header(parent_header);
    parent_hash_ = std::bit_cast<bytes32_t>(
        ethash::keccak256(encoded_header.data(), encoded_header.length()));
}

std::optional<BlockHeader>
BlockHeaderBuffer::get_parent_header(bytes32_t const &parent_hash) const noexcept
{
    if (MONAD_UNLIKELY(parent_hash != parent_hash_)) {
        return std::nullopt;
    }

    return parent_header_;
}

MONAD_NAMESPACE_END

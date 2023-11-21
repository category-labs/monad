#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/block_rlp.hpp>
#include <monad/core/bytes.hpp>

#include <ethash/keccak.hpp>

#include <bit>

MONAD_NAMESPACE_BEGIN

bytes32_t hash(BlockHeader const &block_header)
{
    auto const encoded_header = rlp::encode_block_header(block_header);
    return std::bit_cast<bytes32_t>(
        ethash::keccak256(encoded_header.data(), encoded_header.length()));
}

MONAD_NAMESPACE_END

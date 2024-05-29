#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.h>
#include <monad/core/rlp/block_rlp.hpp>

#include <ethash/hash_types.hpp>

#include <bit>

MONAD_NAMESPACE_BEGIN

bytes32_t hash(BlockHeader const &block_header)
{
    auto const encoded_header = rlp::encode_block_header(block_header);
    bytes32_t res;
    keccak256(encoded_header.data(), encoded_header.size(), res.bytes);
    return res;
}

MONAD_NAMESPACE_END

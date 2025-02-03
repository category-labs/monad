#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>

#include <vector>

MONAD_NAMESPACE_BEGIN
struct BlockHeader;
struct Block;
MONAD_NAMESPACE_END

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_block_header(BlockHeader const &);
byte_string encode_block(Block const &);
byte_string encode_ommers(std::vector<BlockHeader> const &);

Result<Block> decode_block(byte_string_view &);
Result<BlockHeader> decode_block_header(byte_string_view &);
Result<std::vector<BlockHeader>>
decode_block_header_vector(byte_string_view &enc);

MONAD_RLP_NAMESPACE_END

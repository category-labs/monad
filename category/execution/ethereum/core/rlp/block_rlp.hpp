#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/core/block.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_block_header(BlockHeader const &);
byte_string encode_block(Block const &);
byte_string encode_ommers(std::vector<BlockHeader> const &);

Result<Block> decode_block(byte_string_view &);
Result<BlockHeader> decode_block_header(byte_string_view &);
Result<std::vector<BlockHeader>>
decode_block_header_vector(byte_string_view &enc);

MONAD_RLP_NAMESPACE_END

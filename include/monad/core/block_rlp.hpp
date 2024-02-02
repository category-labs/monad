#pragma once

#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_block_header(BlockHeader const &);
byte_string encode_block(Block const &);

Result<byte_string_view> decode_block(Block &, byte_string_view);
Result<byte_string_view> decode_block_header(BlockHeader &, byte_string_view);

MONAD_RLP_NAMESPACE_END

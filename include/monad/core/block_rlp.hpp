#pragma once

#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_block_header(BlockHeader const &);
byte_string encode_block(Block const &);

byte_string_view decode_block(Block &block, byte_string_view const enc);
byte_string_view
decode_block_header(BlockHeader &block_header, byte_string_view const enc);

byte_string_view get_rlp_header_from_block(byte_string_view const block_enc);

MONAD_RLP_NAMESPACE_END

#pragma once

#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_block_header(BlockHeader const &);
byte_string encode_block(Block const &);
byte_string encode_ommers(std::vector<BlockHeader> const &);

Result<Block> decode_block(byte_string_view &);
Result<BlockHeader> decode_block_header(byte_string_view &);

Result<ConsensusBlockBody> decode_consensus_block_body(byte_string_view &);
Result<ConsensusBlockHeader> decode_consensus_block_header(byte_string_view &);

MONAD_RLP_NAMESPACE_END

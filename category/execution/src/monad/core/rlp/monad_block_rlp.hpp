#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <monad/core/monad_block.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_consensus_block_body(MonadConsensusBlockBody const &);
byte_string
encode_consensus_block_header(MonadConsensusBlockHeader const &header);

Result<MonadConsensusBlockBody> decode_consensus_block_body(byte_string_view &);
Result<MonadConsensusBlockHeader>
decode_consensus_block_header(byte_string_view &);

MONAD_RLP_NAMESPACE_END

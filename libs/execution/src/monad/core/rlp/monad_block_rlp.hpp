#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_consensus_block_header(MonadConsensusBlockHeader const &header);

Result<MonadConsensusBlockBody> decode_consensus_block_body(byte_string_view &);
Result<MonadConsensusBlockHeader> decode_consensus_block_header(byte_string_view &);

MONAD_RLP_NAMESPACE_END

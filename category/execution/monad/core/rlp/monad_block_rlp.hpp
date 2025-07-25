#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/monad/core/monad_block.hpp>

MONAD_RLP_NAMESPACE_BEGIN

Result<uint64_t> decode_consensus_block_header_timestamp_s(byte_string_view &);
Result<MonadConsensusBlockBody> decode_consensus_block_body(byte_string_view &);
template <class MonadConsensusBlockHeader>
Result<MonadConsensusBlockHeader>
decode_consensus_block_header(byte_string_view &);

MONAD_RLP_NAMESPACE_END

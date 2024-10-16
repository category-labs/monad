#pragma once

#include <monad/chain/chain.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>

#include <evmc/evmc.h>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_block_header(evmc_revision, BlockHeader const &);
byte_string encode_block(evmc_revision, Block const &);

Result<Block> decode_block(Chain const &, byte_string_view &);
Result<BlockHeader> decode_block_header(Chain const &, byte_string_view &);

MONAD_RLP_NAMESPACE_END

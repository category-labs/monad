#pragma once

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/result.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/rpc/config.hpp>

#include <evmc/evmc.hpp>

#include <filesystem>
#include <vector>

MONAD_RPC_NAMESPACE_BEGIN

Result<evmc::Result> eth_call(
    Transaction const &, BlockHeader const &, block_num_t const,
    Address const &, BlockHashBuffer const &,
    std::vector<std::filesystem::path> const &);

MONAD_RPC_NAMESPACE_END

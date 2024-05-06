#pragma once

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/result.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/rpc/config.hpp>

#include <evmc/evmc.hpp>

#include <filesystem>
#include <string>
#include <vector>

MONAD_RPC_NAMESPACE_BEGIN

evmc_result eth_call(
    std::vector<uint8_t> const &rlp_encoded_transaction,
    std::vector<uint8_t> const &rlp_encoded_block_header,
    std::vector<uint8_t> const &rlp_encoded_sender, uint64_t const,
    std::string const &trie_db_path, std::string const &block_db_path);

Result<evmc::Result> eth_call_helper(
    Transaction const &, BlockHeader const &, uint64_t const, Address const &,
    BlockHashBuffer const &, std::vector<std::filesystem::path> const &);

MONAD_RPC_NAMESPACE_END

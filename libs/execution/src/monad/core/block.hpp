#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct BlockHeader
{
    Receipt::Bloom logs_bloom{}; // H_b
    bytes32_t parent_hash{}; // H_p
    bytes32_t ommers_hash{NULL_LIST_HASH}; // H_o
    bytes32_t state_root{NULL_ROOT}; // H_r
    bytes32_t transactions_root{NULL_ROOT}; // H_t
    bytes32_t receipts_root{NULL_ROOT}; // H_e
    bytes32_t prev_randao{}; // H_a
    uint256_t difficulty{}; // H_d

    uint64_t number{0}; // H_i
    uint64_t gas_limit{0}; // H_l
    uint64_t gas_used{0}; // H_g
    uint64_t timestamp{0}; // H_s

    byte_string_fixed<8> nonce{}; // H_n
    byte_string extra_data{}; // H_x

    Address beneficiary{}; // H_c

    std::optional<uint256_t> base_fee_per_gas{std::nullopt}; // H_f
    std::optional<bytes32_t> withdrawals_root{std::nullopt}; // H_w
    std::optional<uint64_t> blob_gas_used{std::nullopt}; // EIP-4844
    std::optional<uint64_t> excess_blob_gas{std::nullopt}; // EIP-4844
    std::optional<bytes32_t> parent_beacon_block_root{std::nullopt}; // EIP-4788
    std::optional<bytes32_t> requests_hash{std::nullopt}; // EIP-7685

    friend bool operator==(BlockHeader const &, BlockHeader const &) = default;
};

struct Block
{
    BlockHeader header;
    std::vector<Transaction> transactions{};
    std::vector<BlockHeader> ommers{};
    std::optional<std::vector<Withdrawal>> withdrawals{std::nullopt};

    friend bool operator==(Block const &, Block const &) = default;
};

static_assert(sizeof(BlockHeader) == 760);
static_assert(alignof(BlockHeader) == 8);

static_assert(sizeof(Block) == 840);
static_assert(alignof(Block) == 8);

MONAD_NAMESPACE_END

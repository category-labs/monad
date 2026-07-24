// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>

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
    // EIP-7843. RLP-encoded as a trailing optional field (see
    // encode_block_header/decode_block_header) once requests_hash is also
    // present. The consensus round is durably carried in
    // MonadConsensusBlockHeader::block_round; only the consensus execution
    // path (propose_block in runloop_monad) populates this field from it.
    // Any entrypoint that does not repopulate it -- RPC/trace re-execution in
    // monad_executor, historical-block replay runloops -- leaves it nullopt,
    // so the round read via value_or(0) is 0 there (see EXE-60).
    std::optional<uint64_t> slot_number{std::nullopt};

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

static_assert(sizeof(BlockHeader) == 776);
static_assert(alignof(BlockHeader) == 8);

static_assert(sizeof(Block) == 856);
static_assert(alignof(Block) == 8);

MONAD_NAMESPACE_END

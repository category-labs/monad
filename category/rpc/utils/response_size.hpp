// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/config.hpp>

#include <cstddef>
#include <span>
#include <string_view>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Address;
struct Block;
struct CallFrame;
struct Receipt;
struct bytes32_t;

// Given a requested maximum size, this function returns a slightly larger size
// to provide headroom for some bookkeeping to manage the RPC request resource
// consumption.
size_t padded_max_size(size_t);

namespace rpc::eth_simulateV1
{
    // Shared eth_simulateV1 output field keys and stable string values.
    namespace json_fields
    {
        inline constexpr std::string_view calls = "calls";
        inline constexpr std::string_view status = "status";
        inline constexpr std::string_view return_data = "returnData";
        inline constexpr std::string_view logs = "logs";
        inline constexpr std::string_view address = "address";
        inline constexpr std::string_view topics = "topics";
        inline constexpr std::string_view data = "data";
        inline constexpr std::string_view gas_used = "gasUsed";
        inline constexpr std::string_view block_number = "blockNumber";
        inline constexpr std::string_view transaction_hash = "transactionHash";
        inline constexpr std::string_view transaction_index =
            "transactionIndex";
        inline constexpr std::string_view block_hash = "blockHash";
        inline constexpr std::string_view log_index = "logIndex";
        inline constexpr std::string_view removed = "removed";
        inline constexpr std::string_view error = "error";
        inline constexpr std::string_view message = "message";
        inline constexpr std::string_view execution_reverted =
            "execution reverted";
        inline constexpr std::string_view hash = "hash";
        inline constexpr std::string_view parent_hash = "parentHash";
        inline constexpr std::string_view sha3_uncles = "sha3Uncles";
        inline constexpr std::string_view miner = "miner";
        inline constexpr std::string_view size = "size";
        inline constexpr std::string_view state_root = "stateRoot";
        inline constexpr std::string_view transactions_root =
            "transactionsRoot";
        inline constexpr std::string_view receipts_root = "receiptsRoot";
        inline constexpr std::string_view withdrawals_root = "withdrawalsRoot";
        inline constexpr std::string_view logs_bloom = "logsBloom";
        inline constexpr std::string_view difficulty = "difficulty";
        inline constexpr std::string_view number = "number";
        inline constexpr std::string_view gas_limit = "gasLimit";
        inline constexpr std::string_view timestamp = "timestamp";
        inline constexpr std::string_view extra_data = "extraData";
        inline constexpr std::string_view mix_hash = "mixHash";
        inline constexpr std::string_view nonce = "nonce";
        inline constexpr std::string_view base_fee_per_gas = "baseFeePerGas";
        inline constexpr std::string_view uncles = "uncles";
        inline constexpr std::string_view transactions = "transactions";
        inline constexpr std::string_view withdrawals = "withdrawals";
        inline constexpr std::string_view index = "index";
        inline constexpr std::string_view validator_index = "validatorIndex";
        inline constexpr std::string_view amount = "amount";
        inline constexpr std::string_view recipient = "recipient";
    }

    // Estimates the in-memory contribution of one eth_simulateV1 output entry.
    size_t log_entry_size(
        Block const &block, std::vector<Receipt> const &receipts,
        std::span<std::vector<CallFrame> const> const call_frames,
        bytes32_t const &block_hash,
        std::span<bytes32_t const> const txn_hashes);
}

MONAD_NAMESPACE_END

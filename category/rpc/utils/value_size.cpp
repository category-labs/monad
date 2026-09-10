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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/rpc/utils/value_size.hpp>

#include <bit>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <string_view>
#include <tuple>
#include <vector>

#include <evmc/evmc.h>
#include <nlohmann/json.hpp>

MONAD_NAMESPACE_BEGIN

namespace
{
    namespace eth_simulate_json = rpc::eth_simulateV1::json_fields;

    template <typename... Terms>
    size_t json_size_sum(Terms const... terms)
    {
        return (size_t{0} + ... + static_cast<size_t>(terms));
    }

    constexpr size_t json_object_overhead_size()
    {
        return sizeof(nlohmann::json::object_t);
    }

    constexpr size_t json_array_overhead_size()
    {
        return sizeof(nlohmann::json::array_t);
    }

    constexpr size_t json_value_overhead_size()
    {
        return sizeof(nlohmann::json::value_t);
    }

    template <typename T>
    size_t json_named_value_size(std::string_view const name, T const &value)
    {
        return name.size() + value_size(value);
    }

    template <typename Owner, typename Member>
    size_t json_named_value_size(
        std::string_view const name, Owner const &owner, Member Owner::*member)
    {
        return json_named_value_size(name, owner.*member);
    }

    constexpr size_t json_named_encoded_size(
        std::string_view const name, size_t const encoded_value_size)
    {
        return name.size() + encoded_value_size;
    }

    constexpr size_t json_bytes32_hex_size()
    {
        return sizeof(bytes32_t) * 2 + 2;
    }

    size_t json_bytes32_array_encoded_size(size_t const count)
    {
        return json_array_overhead_size() +
               (json_value_overhead_size() + json_bytes32_hex_size()) * count;
    }

    constexpr size_t eth_simulate_status_encoded_size()
    {
        // Status is always either "0x0" or "0x1".
        return json_value_overhead_size() + 3;
    }

    constexpr size_t eth_simulate_removed_encoded_size()
    {
        return json_value_overhead_size() + sizeof(bool);
    }

    constexpr size_t eth_simulate_error_encoded_size(
        std::string_view const error, std::string_view const message,
        std::string_view const execution_reverted)
    {
        return json_object_overhead_size() + 2 * json_value_overhead_size() +
               error.size() + message.size() + execution_reverted.size();
    }

    template <typename Owner, typename Member>
    struct JsonNamedMember
    {
        std::string_view name;
        Member Owner::*member;
    };

    template <typename Owner, typename Member>
    constexpr JsonNamedMember<Owner, Member>
    json_named_member(std::string_view const name, Member Owner::*member)
    {
        return JsonNamedMember<Owner, Member>{name, member};
    }

    template <typename Owner, typename... Members>
    size_t json_named_members_size(
        Owner const &owner, JsonNamedMember<Owner, Members> const... members)
    {
        return json_size_sum(
            json_named_value_size(members.name, owner, members.member)...);
    }

    template <typename Owner, typename... Members>
    size_t json_named_members_size(
        Owner const &owner,
        std::tuple<JsonNamedMember<Owner, Members>...> const &members)
    {
        return std::apply(
            [&owner](auto const &...member) {
                return json_named_members_size(owner, member...);
            },
            members);
    }

    constexpr auto eth_simulate_block_header_named_members()
    {
        return std::tuple{
            json_named_member(
                eth_simulate_json::parent_hash, &BlockHeader::parent_hash),
            json_named_member(
                eth_simulate_json::sha3_uncles, &BlockHeader::ommers_hash),
            json_named_member(
                eth_simulate_json::miner, &BlockHeader::beneficiary),
            json_named_member(
                eth_simulate_json::state_root, &BlockHeader::state_root),
            json_named_member(
                eth_simulate_json::transactions_root,
                &BlockHeader::transactions_root),
            json_named_member(
                eth_simulate_json::receipts_root, &BlockHeader::receipts_root),
            json_named_member(
                eth_simulate_json::withdrawals_root,
                &BlockHeader::withdrawals_root),
            json_named_member(
                eth_simulate_json::logs_bloom, &BlockHeader::logs_bloom),
            json_named_member(
                eth_simulate_json::difficulty, &BlockHeader::difficulty),
            json_named_member(eth_simulate_json::number, &BlockHeader::number),
            json_named_member(
                eth_simulate_json::gas_limit, &BlockHeader::gas_limit),
            json_named_member(
                eth_simulate_json::gas_used, &BlockHeader::gas_used),
            json_named_member(
                eth_simulate_json::timestamp, &BlockHeader::timestamp),
            json_named_member(
                eth_simulate_json::extra_data, &BlockHeader::extra_data),
            json_named_member(
                eth_simulate_json::mix_hash, &BlockHeader::prev_randao),
            json_named_member(eth_simulate_json::nonce, &BlockHeader::nonce),
            json_named_member(
                eth_simulate_json::base_fee_per_gas,
                &BlockHeader::base_fee_per_gas),
        };
    }

    size_t eth_simulate_call_result_base_size(CallFrame const &frame)
    {
        return json_size_sum(
            json_named_value_size(eth_simulate_json::return_data, frame.output),
            json_named_value_size(eth_simulate_json::gas_used, frame.gas_used),
            json_named_encoded_size(
                eth_simulate_json::status, eth_simulate_status_encoded_size()));
    }

    size_t eth_simulate_receipt_log_size(
        Receipt::Log const &log, BlockHeader const &header,
        bytes32_t const &tx_hash, bytes32_t const &block_hash,
        size_t const tx_index, size_t const log_index_value)
    {
        return json_object_overhead_size() +
               json_size_sum(
                   json_named_value_size(
                       eth_simulate_json::address, log.address),
                   json_named_encoded_size(
                       eth_simulate_json::topics,
                       json_bytes32_array_encoded_size(log.topics.size())),
                   json_named_value_size(eth_simulate_json::data, log.data),
                   json_named_value_size(
                       eth_simulate_json::block_number,
                       header,
                       &BlockHeader::number),
                   json_named_value_size(
                       eth_simulate_json::transaction_hash, tx_hash),
                   json_named_value_size(
                       eth_simulate_json::transaction_index, tx_index),
                   json_named_value_size(
                       eth_simulate_json::block_hash, block_hash),
                   json_named_value_size(
                       eth_simulate_json::log_index, log_index_value),
                   json_named_encoded_size(
                       eth_simulate_json::removed,
                       eth_simulate_removed_encoded_size()));
    }

    constexpr size_t eth_simulate_call_error_size()
    {
        return eth_simulate_error_encoded_size(
            eth_simulate_json::error,
            eth_simulate_json::message,
            eth_simulate_json::execution_reverted);
    }

    size_t eth_simulate_calls_array_size(size_t const transactions_count)
    {
        return eth_simulate_json::calls.size() + json_array_overhead_size() +
               json_value_overhead_size() +
               json_object_overhead_size() * transactions_count;
    }

    size_t eth_simulate_call_logs_size(
        std::vector<Receipt::Log> const &receipt_logs,
        BlockHeader const &header, bytes32_t const &tx_hash,
        bytes32_t const &block_hash, size_t const tx_index)
    {
        size_t carried_size =
            eth_simulate_json::logs.size() + json_array_overhead_size();
        for (size_t log_index = 0; log_index < receipt_logs.size();
             ++log_index) {
            carried_size += eth_simulate_receipt_log_size(
                receipt_logs[log_index],
                header,
                tx_hash,
                block_hash,
                tx_index,
                log_index);
        }
        return carried_size;
    }

    size_t eth_simulate_call_result_size(
        Receipt const &receipt, CallFrame const &top_call_frame,
        BlockHeader const &header, bytes32_t const &tx_hash,
        bytes32_t const &block_hash, size_t const tx_index)
    {
        size_t carried_size =
            eth_simulate_call_result_base_size(top_call_frame);

        if (top_call_frame.status == EVMC_SUCCESS) {
            carried_size += eth_simulate_call_logs_size(
                receipt.logs, header, tx_hash, block_hash, tx_index);
        }
        else {
            carried_size += eth_simulate_call_error_size();
        }

        return carried_size;
    }

    size_t eth_simulate_calls_size(
        std::vector<Receipt> const &receipts,
        std::vector<std::vector<CallFrame>> const &call_frames,
        BlockHeader const &header, bytes32_t const &block_hash,
        std::vector<bytes32_t> const &txn_hashes)
    {
        size_t carried_size = 0;

        for (size_t tx_idx = 0; tx_idx < txn_hashes.size(); ++tx_idx) {
            MONAD_ASSERT_THROW(
                call_frames[tx_idx].size() > 0,
                "call frames size must be greater than 0");
            carried_size += eth_simulate_call_result_size(
                receipts[tx_idx],
                call_frames[tx_idx][0],
                header,
                txn_hashes[tx_idx],
                block_hash,
                tx_idx);
        }

        return carried_size;
    }

    size_t eth_simulate_uncles_array_size(size_t const ommers_count)
    {
        return json_named_encoded_size(
            eth_simulate_json::uncles,
            json_bytes32_array_encoded_size(ommers_count));
    }

    size_t eth_simulate_transactions_array_size(size_t const transactions_count)
    {
        return json_named_encoded_size(
            eth_simulate_json::transactions,
            json_bytes32_array_encoded_size(transactions_count));
    }

    size_t eth_simulate_withdrawals_array_size()
    {
        return json_named_encoded_size(
            eth_simulate_json::withdrawals, json_array_overhead_size());
    }

    size_t eth_simulate_block_header_fields_size(
        bytes32_t const &block_hash, BlockHeader const &header)
    {
        static constexpr auto block_header_named_members =
            eth_simulate_block_header_named_members();

        return json_size_sum(
            json_named_value_size(eth_simulate_json::hash, block_hash),
            json_named_value_size(
                eth_simulate_json::size,
                // NOTE(dhil): The block size is calculated later, however,
                // its size is bounded by size_t. This is a conservative
                // estimate which likely overestimates the size of the field by
                // 10-12 bytes or so.
                std::numeric_limits<size_t>::max()),
            json_named_members_size(header, block_header_named_members));
    }

    size_t eth_simulate_output_header_size(
        bytes32_t const &block_hash, BlockHeader const &header,
        size_t const ommers_count, size_t const transactions_count)
    {
        return eth_simulate_block_header_fields_size(block_hash, header) +
               json_size_sum(
                   eth_simulate_uncles_array_size(ommers_count),
                   eth_simulate_transactions_array_size(transactions_count),
                   eth_simulate_withdrawals_array_size());
    }

    size_t eth_simulate_withdrawal_size(Withdrawal const &withdrawal)
    {
        return json_object_overhead_size() +
               json_named_members_size(
                   withdrawal,
                   json_named_member(
                       eth_simulate_json::index, &Withdrawal::index),
                   json_named_member(
                       eth_simulate_json::validator_index,
                       &Withdrawal::validator_index),
                   json_named_member(
                       eth_simulate_json::amount, &Withdrawal::amount),
                   json_named_member(
                       eth_simulate_json::recipient, &Withdrawal::recipient));
    }

    size_t eth_simulate_withdrawals_size(
        std::optional<std::vector<Withdrawal>> const &withdrawals)
    {
        if (!withdrawals.has_value()) {
            return 0;
        }

        size_t carried_size = 0;
        for (auto const &withdrawal : withdrawals.value()) {
            carried_size += eth_simulate_withdrawal_size(withdrawal);
        }
        return carried_size;
    }
}

size_t value_size(size_t x)
{
    // The image of bit_width is [0, 64] for size_t on typical platforms, so it
    // is safe to interpret its return value as an element of size_t.
    return x == 0 ? 3 : 2 + (static_cast<size_t>(std::bit_width(x)) + 3) / 4;
}

size_t value_size(uint256_t const &x)
{
    return x == 0 ? 3 : 2 + (monad::bit_width(x) + 3) / 4;
}

size_t value_size(Address const &)
{
    return 2 * sizeof(Address) + 2 /* 0xABCDEF.... */;
}

size_t value_size(bytes32_t const &)
{
    return 2 * sizeof(bytes32_t) + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string_view const &x)
{
    return x.size() * 2 + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string const &x)
{
    return x.size() * 2 + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string_fixed<8> const &)
{
    return 18; // 0x0000...
}

size_t value_size(byte_string_fixed<256> const &)
{
    return 514; // 0x0000...
}

size_t value_size(std::optional<Address> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<bytes32_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<uint64_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<uint256_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t padded_max_size(size_t max_size)
{
    // We use the size of the in-memory structures to bound the memory
    // consumption. This estimator is inaccurate as the RPC
    // client submits the maximum size of the CBOR response, which is
    // more compact than the in-memory structures.  Therefore we keep a
    // small amount of headroom to absorb estimator drift while still
    // bounding memory growth. We use a monotonic hyperbolic function to
    // compute the headroom, which decays percentage-wise as the
    // `max_size` increases. This is to avoid over-estimating the
    // headroom for large `max_size` values, preventing excessive
    // memory usage.
    //
    // Monotonic hyperbolic percentage in basis points:
    // S(M) = M_min + (M_max - M_min) * k / (k + M)
    // where k controls how quickly slack decays.
    constexpr size_t bps_scale = 10'000; // basis points: 100% = 10'000.
    constexpr size_t M_max = bps_scale / 2; // 50%
    constexpr size_t M_min = 1; // 0.01%
    constexpr size_t k = 4096; // 4 KiB
    // At the time of writing the BFT RPC client has M = 25'000'000 (25
    // MB). Meaning, we get roughly 2500 bytes of slack using this
    // method.

    size_t const denominator = max_size > std::numeric_limits<size_t>::max() - k
                                   ? std::numeric_limits<size_t>::max()
                                   : max_size + k;
    size_t const slack_bps = M_min + ((M_max - M_min) * k) / denominator;

    // Computing `ceil(max_size * slack_bps / bps_scale)` using integer
    // maths.
    size_t const whole = (max_size / bps_scale) * slack_bps;
    size_t const remainder = max_size % bps_scale;
    size_t const fraction =
        (remainder * slack_bps + (bps_scale - 1)) / bps_scale;
    size_t const slack = whole + fraction;

    if (max_size > std::numeric_limits<size_t>::max() - slack) {
        return std::numeric_limits<size_t>::max();
    }
    return max_size + slack;
}

namespace rpc::eth_simulateV1
{
    size_t log_entry_size(
        Block const &block, std::vector<Receipt> const &receipts,
        std::vector<std::vector<CallFrame>> const &call_frames,
        bytes32_t const &block_hash, std::vector<bytes32_t> const &txn_hashes)
    {
        return json_size_sum(
            eth_simulate_calls_array_size(block.transactions.size()),
            eth_simulate_calls_size(
                receipts, call_frames, block.header, block_hash, txn_hashes),
            eth_simulate_output_header_size(
                block_hash,
                block.header,
                block.ommers.size(),
                txn_hashes.size()),
            eth_simulate_withdrawals_size(block.withdrawals));
    }
}

MONAD_NAMESPACE_END
